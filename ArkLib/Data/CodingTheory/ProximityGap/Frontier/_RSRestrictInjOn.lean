/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Tactic

/-!
# Reed–Solomon `k`-projection rigidity (#444, list-decoding side)

A clean, unconditional structural lemma surfaced by the *deletion-closed entropy descent* attack on the
MCA list-count (the off-character-sum, list-decoding side of the proximity-gap prize). The attack closed
with a **vacuity-or-loss dichotomy**: Shearer / sub-additive entropy descent cannot beat the
Johnson/volume bound for Reed–Solomon list-counts, because at block size `≥ k` the per-block entropy
*equals* the global entropy — there is no sub-additivity to exploit. The exact certificate of that
vacuity is this rigidity fact, which is genuinely useful in its own right (it is the MDS "any `k`
coordinates determine the codeword" property, in the precise `InjOn` form the list-decoding arguments
need, and was absent in-tree as a named standalone):

> **Restricting an RS codeword to any `k` evaluation points is injective on the code.**

The mechanism is the fundamental one: two degree-`< k` polynomials agreeing on `≥ k` distinct points have
a difference that is a degree-`< k` polynomial with `≥ k` roots, hence zero.

## Results (axiom-clean)
* `degreeLT_eq_zero_of_eval_eq_zero` — a degree-`< k` polynomial vanishing on `≥ k` distinct points
  (here the images of a `k`-subset of the evaluation domain under the injective `domain`) is `0`.
* `rs_restrict_injOn_of_k_le` — `Set.InjOn` of the projection `c ↦ c|_S` on `ReedSolomon.code domain k`
  for any `S` with `k ≤ S.card`. The `k`-projection rigidity / MDS recovery certificate.

NOT prize closure — a true, reusable list-decoding-side brick (the Shearer-route no-go certificate).
-/

namespace ArkLib.ProximityGap.Frontier.RSRestrictInjOn

open Polynomial ReedSolomon

variable {F ι : Type*} [Field F] [DecidableEq F]

/-- **The polynomial rigidity core (proven).** A polynomial `r` of degree `< k` that vanishes at the
`domain`-images of every point of a finset `S` with `k ≤ S.card` is identically zero: it would otherwise
have `≥ k` distinct roots while its degree is `< k`. -/
theorem degreeLT_eq_zero_of_eval_eq_zero
    (domain : ι ↪ F) (k : ℕ) (S : Finset ι) (hk : k ≤ S.card)
    (r : F[X]) (hr : r ∈ Polynomial.degreeLT F k)
    (hroots : ∀ i ∈ S, r.eval (domain i) = 0) : r = 0 := by
  by_contra h0
  -- the `|S|` distinct images `domain i` are all roots of `r`
  have hsub : S.image domain ⊆ r.roots.toFinset := by
    intro x hx
    simp only [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨h0, hroots i hi⟩
  -- hence `|S| ≤ #roots ≤ natDegree r`
  have hcard : S.card ≤ r.natDegree := by
    calc S.card = (S.image domain).card :=
          (Finset.card_image_of_injective S domain.injective).symm
      _ ≤ r.roots.toFinset.card := Finset.card_le_card hsub
      _ ≤ Multiset.card r.roots := Multiset.toFinset_card_le _
      _ ≤ r.natDegree := Polynomial.card_roots' r
  -- but `natDegree r < k ≤ |S|`, contradiction
  have hdeg : r.natDegree < k := by
    rw [Polynomial.mem_degreeLT] at hr
    exact (Polynomial.natDegree_lt_iff_degree_lt h0).mpr hr
  omega

/-- **RS `k`-projection rigidity (proven).** For an injective evaluation `domain : ι ↪ F` and any finset
`S` of evaluation indices with `k ≤ S.card`, the restriction map `c ↦ c|_S` is injective on the
Reed–Solomon code `ReedSolomon.code domain k` (degree `< k`). I.e. any `k` coordinates determine an RS
codeword — the MDS recovery property in `InjOn` form. This is the certificate that Shearer/entropy
sub-additivity is vacuous on RS list-counts at block size `≥ k` (per-block = global information). -/
theorem rs_restrict_injOn_of_k_le
    (domain : ι ↪ F) (k : ℕ) (S : Finset ι) (hk : k ≤ S.card) :
    Set.InjOn (fun c : ι → F => fun i : S => c i)
      (ReedSolomon.code domain k : Set (ι → F)) := by
  intro c₁ hc₁ c₂ hc₂ hres
  simp only [SetLike.mem_coe, ReedSolomon.code, Submodule.mem_map] at hc₁ hc₂
  obtain ⟨p, hp, rfl⟩ := hc₁
  obtain ⟨q, hq, rfl⟩ := hc₂
  -- `p - q` is degree `< k` and vanishes on `S`
  have hrmem : p - q ∈ Polynomial.degreeLT F k := (Polynomial.degreeLT F k).sub_mem hp hq
  have hvanish : ∀ i ∈ S, (p - q).eval (domain i) = 0 := by
    intro i hi
    have hpt : (evalOnPoints domain p) i = (evalOnPoints domain q) i := congrFun hres ⟨i, hi⟩
    have hp' : (evalOnPoints domain p) i = p.eval (domain i) := rfl
    have hq' : (evalOnPoints domain q) i = q.eval (domain i) := rfl
    rw [hp'] at hpt; rw [hq'] at hpt
    rw [Polynomial.eval_sub, hpt, sub_self]
  have hzero : p - q = 0 := degreeLT_eq_zero_of_eval_eq_zero domain k S hk _ hrmem hvanish
  have : p = q := sub_eq_zero.mp hzero
  rw [this]

end ArkLib.ProximityGap.Frontier.RSRestrictInjOn

/-! ## Axiom audit (expected: only `propext, Classical.choice, Quot.sound`; no `sorryAx`) -/
#print axioms ArkLib.ProximityGap.Frontier.RSRestrictInjOn.degreeLT_eq_zero_of_eval_eq_zero
#print axioms ArkLib.ProximityGap.Frontier.RSRestrictInjOn.rs_restrict_injOn_of_k_le
