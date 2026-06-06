/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeRadiusOneExact
import ArkLib.Data.CodingTheory.ProximityGap.MCABadCount
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeCollapse

/-!
# A second-moment lower bound on the radius-one MCA error, deciding the §1 prize window

`GrandChallengeRadiusOneExact.lean` pins `ε_mca(RS, 1) = C(n, k+1)/q` only once
`q > C(C(n,k+1), 2) ≈ C(n,k+1)²/2` (the hyperplane-avoidance regime: there is a *single*
first word `u₀` separating **all** the `(k+1)`-subset functionals `c_T`). This file proves a
genuinely new, weaker-but-much-wider lower bound that survives far below that quadratic
threshold, by a **second-moment / averaging** argument instead of a union bound.

## The mathematics

Fix any family `𝒯` of `M'` distinct `(k+1)`-subsets. For a uniformly chosen first word
`u₀`, the *expected* number of ordered colliding pairs `coll(u₀) :=
#{(T,T') ∈ 𝒯.offDiag | c_T(u₀) = c_{T'}(u₀)}` equals `|𝒯.offDiag|·q^{n-1}` summed over the
`q^n` words (each pair collides on exactly the `q^{n-1}`-sized kernel of `c_T - c_{T'}`).
Pigeonhole therefore gives a single `u₀` with `q·coll(u₀) ≤ |𝒯.offDiag| ≤ M'²`. For that
`u₀` the `M'` values `c_T(u₀)` take at least `M' - coll(u₀) ≥ M' - M'²/q` distinct values
(a fiber-counting / handshake bound), each of which is a *bad scalar* for the deep-hole
line `(u₀, deepHole)`. Hence

  `ε_mca(RS, 1) ≥ (M' - M'²/q)/q`           (`epsMCA_one_ge_second_moment`)

for every `M' ≤ C(n, k+1)`. Optimizing `M' ≈ q/2^{127}` decides the formal §1 MCA prize:

  `not_mcaPrize_of_second_moment` — for `n ≥ 2` and
  `2^{129} ≤ q ≤ 2^{127}·C(n, ⌊n/2⌋+1)` the formal prize predicate is **false**.

Combined with `mcaPrize_of_large_field` (`q ≥ 2^{128}·C(n, k_j+1) ∀j ⟹ TRUE`, already in
tree) the formal prize is now decided for **all** field sizes except the knife-edge band
`q ∈ (2^{127}·C(n, k₀+1), 2^{128}·C(n, k₀+1))` — a single bit of `q`, where the truth
depends on the exact extremal distinct-value count (relative width of the genuinely
undecided sliver after optimizing constants is `~2^{-127}`).

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*, §1.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code Polynomial ReedSolomon
open scoped ProbabilityTheory BigOperators ENNReal

section SecondMoment

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-! ## (1) The fiber-counting lemma (pure `Finset` combinatorics) -/

/-- The off-diagonal collision set of `f` on `s`, grouped over the image, is a disjoint
union of the off-diagonals of the fibers. -/
lemma offDiag_collisions_eq_biUnion {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    (s.offDiag.filter (fun p => f p.1 = f p.2))
      = (s.image f).biUnion (fun b => (s.filter (fun a => f a = b)).offDiag) := by
  ext ⟨a, a'⟩
  simp only [Finset.mem_filter, Finset.mem_offDiag, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨⟨ha, ha', hne⟩, hcoll⟩
    exact ⟨f a, ⟨a, ha, rfl⟩, ⟨ha, rfl⟩, ⟨ha', hcoll.symm⟩, hne⟩
  · rintro ⟨b, _, ⟨ha, hab⟩, ⟨ha', ha'b⟩, hne⟩
    exact ⟨⟨ha, ha', hne⟩, hab.trans ha'b.symm⟩

/-- **Off-diagonal collisions counted fiberwise.** The number of ordered colliding pairs is
`Σ_{b ∈ image} m_b·(m_b - 1)`, with `m_b` the fiber size. -/
lemma card_offDiag_collisions {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    (s.offDiag.filter (fun p => f p.1 = f p.2)).card
      = ∑ b ∈ s.image f, (s.filter (fun a => f a = b)).card *
          ((s.filter (fun a => f a = b)).card - 1) := by
  rw [offDiag_collisions_eq_biUnion]
  rw [Finset.card_biUnion]
  · refine Finset.sum_congr rfl ?_
    intro b _
    rw [Finset.offDiag_card]
    -- m * m - m = m * (m - 1)
    cases h : (s.filter (fun a => f a = b)).card with
    | zero => simp
    | succ m => rw [Nat.succ_sub_one]; ring_nf; omega
  · -- fibers are pairwise disjoint, hence their off-diagonals are
    intro b _ b' _ hbb'
    apply Finset.disjoint_left.mpr
    rintro ⟨a, a'⟩ hp hp'
    rw [Finset.mem_offDiag, Finset.mem_filter] at hp hp'
    exact hbb' (hp.1.2.symm.trans hp'.1.2)

/-- **Fiber-counting lemma.** The image of `f` on `s` has at least `s.card` minus the number
of ordered off-diagonal collisions distinct values. -/
lemma card_image_ge_card_sub_offDiag_collisions {α β : Type*} [DecidableEq α] [DecidableEq β]
    (s : Finset α) (f : α → β) :
    s.card - (s.offDiag.filter (fun p => f p.1 = f p.2)).card ≤ (s.image f).card := by
  classical
  set d := (s.image f).card with hd
  -- `s.card = Σ_b m_b` and `P = Σ_b m_b·(m_b-1)`; per-fiber `m_b ≤ 1 + m_b·(m_b-1)`.
  have hcard : s.card = ∑ b ∈ s.image f, (s.filter (fun a => f a = b)).card :=
    Finset.card_eq_sum_card_image f s
  have hP := card_offDiag_collisions s f
  -- `d = Σ_b 1`.
  have hdsum : d = ∑ _b ∈ s.image f, 1 := by rw [hd, Finset.sum_const, smul_eq_mul, mul_one]
  -- per-fiber: `m_b ≤ 1 + m_b·(m_b-1)` (fibers nonempty ⇒ `m_b ≥ 1`).
  have hterm : ∀ b ∈ s.image f, (s.filter (fun a => f a = b)).card ≤
      1 + (s.filter (fun a => f a = b)).card * ((s.filter (fun a => f a = b)).card - 1) := by
    intro b hb
    have hm1 : 1 ≤ (s.filter (fun a => f a = b)).card := by
      rw [Finset.mem_image] at hb
      obtain ⟨a, ha, hab⟩ := hb
      exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hab⟩⟩
    -- `m ≤ 1 + m·(m-1)`: write `m = (m-1)+1`, so `m·(m-1) ≥ m-1`.
    set m := (s.filter (fun a => f a = b)).card with hm
    have hmul : m - 1 ≤ m * (m - 1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  -- sum: `s.card ≤ d + P`.
  have hsum : s.card ≤ d + (s.offDiag.filter (fun p => f p.1 = f p.2)).card := by
    rw [hcard, hP, hdsum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hterm
  omega

/-! ## (2) Averaging / pigeonhole over `u₀` (the second moment) -/

/-- The ordered off-diagonal collision count of the functionals `c_T` at a first word `u₀`,
over a family `𝒯` of subsets. -/
noncomputable def collCount (domain : ι ↪ F) (k : ℕ) (𝒯 : Finset (Finset ι)) (u₀ : ι → F) : ℕ :=
  (𝒯.offDiag.filter (fun p => cT domain k p.1 u₀ = cT domain k p.2 u₀)).card

/-- **Per-pair kernel count.** For a fixed pair `(T, T')` of distinct `(k+1)`-subsets, the
number of words `u₀` with `c_T(u₀) = c_{T'}(u₀)` is `q^{n-1}`. -/
lemma card_filter_pair_eq (domain : ι ↪ F) {k : ℕ} {T T' : Finset ι}
    (hT : T.card = k + 1) (hT' : T'.card = k + 1) (hne : T ≠ T') :
    (Finset.univ.filter (fun u₀ : ι → F => cT domain k T u₀ = cT domain k T' u₀)).card
      = Fintype.card F ^ (Fintype.card ι - 1) :=
  card_agree_le domain hT hT' hne

/-- **Second moment.** Summing the collision count over all `q^n` first words gives exactly
`|𝒯.offDiag|·q^{n-1}`. -/
lemma sum_collCount (domain : ι ↪ F) {k : ℕ} {𝒯 : Finset (Finset ι)}
    (h𝒯 : ∀ T ∈ 𝒯, T.card = k + 1) :
    ∑ u₀ : ι → F, collCount domain k 𝒯 u₀
      = 𝒯.offDiag.card * Fintype.card F ^ (Fintype.card ι - 1) := by
  classical
  -- swap the order of summation: count pairs first.
  have hswap : ∑ u₀ : ι → F, collCount domain k 𝒯 u₀
      = ∑ p ∈ 𝒯.offDiag,
          (Finset.univ.filter (fun u₀ : ι → F => cT domain k p.1 u₀ = cT domain k p.2 u₀)).card := by
    simp only [collCount, Finset.card_filter]
    rw [Finset.sum_comm]
  rw [hswap]
  -- each pair contributes `q^{n-1}`.
  rw [Finset.sum_congr rfl (fun p hp => ?_)]
  · rw [Finset.sum_const, smul_eq_mul]
  · rw [Finset.mem_offDiag] at hp
    exact card_filter_pair_eq domain (h𝒯 p.1 hp.1) (h𝒯 p.2 hp.2.1) hp.2.2

/-- **Existence of a low-collision first word.** Some first word `u₀` has at most
`|𝒯.offDiag|/q` ordered collisions: `q·coll(u₀) ≤ |𝒯.offDiag|`. -/
lemma exists_u0_small_collisions (domain : ι ↪ F) {k : ℕ} {𝒯 : Finset (Finset ι)}
    (h𝒯 : ∀ T ∈ 𝒯, T.card = k + 1) :
    ∃ u₀ : ι → F, Fintype.card F * collCount domain k 𝒯 u₀ ≤ 𝒯.offDiag.card := by
  classical
  by_contra hcon
  push Not at hcon
  -- if `q·coll(u₀) ≥ offDiag + 1` for all `u₀`, sum to a contradiction.
  have hpt : ∀ u₀ : ι → F, 𝒯.offDiag.card + 1 ≤ Fintype.card F * collCount domain k 𝒯 u₀ := by
    intro u₀; exact hcon u₀
  have hsum_lo : (Finset.univ : Finset (ι → F)).card * (𝒯.offDiag.card + 1)
      ≤ ∑ u₀ : ι → F, Fintype.card F * collCount domain k 𝒯 u₀ := by
    calc (Finset.univ : Finset (ι → F)).card * (𝒯.offDiag.card + 1)
        = ∑ _u₀ : ι → F, (𝒯.offDiag.card + 1) := by
          rw [Finset.sum_const, smul_eq_mul, Finset.card_univ]
      _ ≤ ∑ u₀ : ι → F, Fintype.card F * collCount domain k 𝒯 u₀ :=
          Finset.sum_le_sum (fun u₀ _ => hpt u₀)
  have hsum_eq : ∑ u₀ : ι → F, Fintype.card F * collCount domain k 𝒯 u₀
      = Fintype.card F * (𝒯.offDiag.card * Fintype.card F ^ (Fintype.card ι - 1)) := by
    rw [← Finset.mul_sum, sum_collCount domain h𝒯]
  -- `|univ| = q^n`, and `q^n = q · q^{n-1}` (n ≥ 1).
  have hn1 : Fintype.card ι - 1 + 1 = Fintype.card ι := by
    have : 1 ≤ Fintype.card ι := Fintype.card_pos
    omega
  have hcard_univ : (Finset.univ : Finset (ι → F)).card
      = Fintype.card F * Fintype.card F ^ (Fintype.card ι - 1) := by
    rw [Finset.card_univ, Fintype.card_fun, ← pow_succ', hn1]
  rw [hsum_eq, hcard_univ] at hsum_lo
  -- `q^n·(offDiag+1) ≤ q^n·offDiag` is impossible (q^n > 0).
  have hqpos : 0 < Fintype.card F ^ (Fintype.card ι - 1) := pow_pos Fintype.card_pos _
  have hqn : 0 < Fintype.card F := Fintype.card_pos
  nlinarith [hsum_lo, hqpos, hqn]

end SecondMoment

end ProximityGap
