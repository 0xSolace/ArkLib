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

import ArkLib.Data.CodingTheory.ReedSolomon.Domain.CosetFftDomain.Mem
import ArkLib.Data.CodingTheory.ReedSolomon.Domain.CosetFftDomain.ToFftDomain
import ArkLib.Data.CodingTheory.ReedSolomon.Domain.FftDomain.Ops

namespace ReedSolomon

variable {ι : Type} [Fintype ι] [AddCommGroup ι] [DecidableEq ι]
variable {F : Type} [Field F] [DecidableEq F]

namespace CosetFftDomain

variable {ω : CosetFftDomain ι F} {i j : ι}

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
