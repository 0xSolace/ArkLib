/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Julian Sutherland, Ilia Vlasov, Aristotle (Harmonic)
-/

import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Field

import ArkLib.Data.CodingTheory.ReedSolomon.Domain.CosetFftDomain.Ops
import ArkLib.Data.CodingTheory.ReedSolomon.Domain.FftDomain.Ops

namespace ReedSolomon

variable {F : Type} [Field F] [DecidableEq F]

namespace CosetFftDomainClass

variable {n : ℕ}
variable {D : Type} [FunLike D (Fin (2 ^ n)) F] [CosetFftDomainClass D (Fin (2 ^ n)) F]

private def subdomain_embed (i : Fin n.succ) (k : Fin (2 ^ (i : ℕ))) :
  Fin (2 ^ n) :=
  ⟨2 ^ (n - i) * k.val, match i, k with
    | ⟨i, hi⟩, ⟨k, hk⟩ => by
      simp only at hk ⊢
      by_cases hk_zero : k = 0 <;> try (subst hk_zero; simp)
      calc 2 ^ (n - i) * k < 2 ^ (n - i) * 2 ^ i :=
              Nat.mul_lt_mul_of_pos_left hk (by positivity)
          _ = 2 ^ n := by rw [←pow_add, Nat.sub_add_cancel (by omega)]⟩

private lemma subdomain_embed_add (i : Fin n.succ) (a b : Fin (2 ^ (i : ℕ))) :
  subdomain_embed i (a + b) = subdomain_embed i a + subdomain_embed i b := by
  unfold subdomain_embed
  simp +decide [Fin.val_add]
  ring_nf
  norm_num [Fin.ext_iff, Fin.val_add, Fin.val_mul]
  rw [←add_mul, ←Nat.mul_mod_mul_right, ←pow_add,
    Nat.add_sub_of_le (Nat.le_of_lt_succ i.2)]

private lemma subdomain_embed_zero (i : Fin n.succ) : subdomain_embed i (0 :
  Fin (2 ^ (i : ℕ))) = (0 : Fin (2 ^ n)) := by
  unfold subdomain_embed
  aesop

private lemma subdomain_embed_injective (i : Fin n.succ) :
  Function.Injective (subdomain_embed (n := n) i) := by
  intro a b h
  simp_all [Fin.ext_iff, subdomain_embed]

/-- Given a smooth FFT domain `ω` of log-order `n`
  this function returns its subdomain of log-order `i`.
-/
def subdomain (ω : D) (i : Fin n.succ) :
  SmoothCosetFftDomain i F :=
  ⟨{ toFun := fun k ↦ mkSubgroupUnit ω (subdomain_embed i (Multiplicative.toAdd k))
     map_one' := by 
      aesop (add simp [subdomain_embed_zero, mkSubgroupUnit])
     map_mul' := by 
      aesop 
        (add simp [toAdd_mul, subdomain_embed_add,
                   mkSubgroupUnit, CosetFftDomainClass.map_add])
        (add safe (by field_simp)) },
   by
     intro a b h
     have h2 := ω.inj h
     have h3 := Multiplicative.ofAdd.injective h2
     exact Multiplicative.ofAdd.injective (subdomain_embed_injective i h3),
  (CosetFftDomainClass.mkSubgroupUnit ω 0) ^ 2 ^ (n - i.val)⟩


omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma apply_zero : ω 0 = ω.cosetGenerator := by 
  have : (0 : ι) = (1 : Multiplicative ι) := by rfl
  aesop (add simp
     [eval_coset_fft_domain_eq_eval_generator_mul_domain])

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma apply_add_eq_inv_mul_mul :
  ω (i + j) = ω.cosetGenerator⁻¹ * ω i * ω j := by cases ω with
  | mk x ω =>
    have : i + j = Multiplicative.ofAdd i * Multiplicative.ofAdd j := by rfl
    aesop
      (add simp 
        [eval_coset_fft_domain_eq_eval_generator_mul_domain, ]) (add safe (by ring_nf))

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma apply_neg_eq_sq_mul_inv :
  ω (-i) = ω.cosetGenerator ^ 2 * (ω i)⁻¹ := by cases ω with
  | mk x ω =>
  have : -i = (Multiplicative.ofAdd i)⁻¹ := by rfl 
  aesop 
    (add simp [eval_coset_fft_domain_eq_eval_generator_mul_domain]) 
    (add safe (by field_simp))

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
lemma apply_sub_eq_mul_div :
  ω (i - j) = ω.cosetGenerator * ω i / ω j := by cases ω with
  | mk x ω =>
  have : (i - j) = Multiplicative.ofAdd i / Multiplicative.ofAdd j := by rfl
  aesop 
    (add simp [eval_coset_fft_domain_eq_eval_generator_mul_domain, Multiplicative.ofAdd]) 
    (add safe (by field_simp))

end CosetFftDomain

namespace CosetFftDomainClass

section Smooth

variable {n : ℕ}
variable {D : Type} [FunLike D (Fin (2 ^ n)) F] [CosetFftDomainClass D (Fin (2 ^ n)) F]
variable {ω : D} {x : F}

omit [DecidableEq F] in
theorem neg_mem_domain_of_mem [nz : NeZero n] (h : x ∈ ω) :
  -x ∈ ω := by
  rw [show -x = (-1) * x by simp]
  exact CosetFftDomainClass.mul_mem_of_mem_toFftDomain_of_mem (by simp) h

omit [DecidableEq F] in
@[simp]
lemma neg_mem_domain_iff_mem [nz : NeZero n] :
  -x ∈ ω ↔ x ∈ ω := by
  constructor <;> intro h
  · rw [show x = -(-x) by simp] 
    exact neg_mem_domain_of_mem h
  · exact neg_mem_domain_of_mem h

omit [DecidableEq F] in
lemma domain_implies_char_ne_2 [NeZero n] (ω : D) :
  ¬CharP F 2 := FftDomainClass.domain_implies_char_ne_2 (toFftDomain ω)
  
end Smooth

end CosetFftDomainClass

end ReedSolomon
