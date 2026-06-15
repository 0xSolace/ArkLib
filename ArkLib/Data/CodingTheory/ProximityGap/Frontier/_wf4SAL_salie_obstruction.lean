/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

set_option linter.style.longLine false
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# wf-SAL (Issue #444) — the Salié obstruction for the under-determined (s−k=1) δ\* floor.

**Lane question.** The under-determined stratum's binding incidence is the p-dependent character
sum = the BGK period `η_b = ∑_{x∈μ_n} e_p(b x)` (the open 25-year wall). Salié sums (the
quadratic-character-twisted Kloosterman analogue) evaluate EXACTLY in closed form. Since `−1 ∈ μ_n`
(negation symmetry) and the dyadic `μ_{2^μ}` carries a quadratic structure, one might hope the
binding sum is Salié-type (exactly evaluable, off the BGK wall). **This file records, axiom-clean,
the precise structural obstruction that kills that hope.**

**The obstruction (proven here).** A Salié evaluation needs a *nontrivial* quadratic-character twist
on the summation domain. The natural candidate twist is the "subgroup-Salié" sum
`T_b = ∑_{x∈G} χ(x)·ψ(b x)` with `χ` the quadratic character of `F`. But in the prize regime the
index `m = (q−1)/n = 2^128` has `v₂(q−1) = μ + 128 ≫ μ = log₂ n`, so **every element of `μ_n` is a
square in `F_q`** (because `μ_n ⊆ (F_q^×)^{2}` exactly when `n ∣ (q−1)/2`). When every element of a
finset `G` is a square, the quadratic character `χ` is identically `1` on `G`, hence:

`subgroupSalieTwist`: `∑_{x∈G} χ(x)·ψ(b x) = ∑_{x∈G} ψ(b x) = η_b`.

So the χ-twist **collapses to the untwisted BGK period** — it supplies no new (Salié-evaluable)
object. The Salié route degenerates exactly in the prize regime. (Numerically confirmed in
`scripts/probes/probe_wf4SAL_{salie_underdet,obstruction}.py`: the χ-trivial regime is `v₂(p−1)>μ`,
i.e. `m` even; and even off it — `m` odd, `n=32` — the twisted `|T_b|` still SPREADS continuously
like a Gauss period, never bimodal `{0,2√q}` like a true Salié sum.)

**Why the negation symmetry doesn't help.** The Salié closed form comes from a degree-2 substitution
`x = y²` collapsing the twist into a single Gauss sum over a *full* group/line. On `μ_{2^μ}` the
squaring map is the index-2 endomorphism `μ_n ↠ μ_{n/2}` (2-to-1 onto), so the "square route"
re-funnels `η` into a period over the smaller dyadic subgroup `μ_{n/2}` — self-similar, never a
single Gauss sum. (Verified in the probe.)

**Verdict (this lane).** The under-determined s−k=1 floor is **NOT** a Salié sum: it is a generic
cyclotomic Gauss period (BGK-family), exactly the open wall. `refuted` (the Salié-closure hope),
with the obstruction pinned as a machine-checked collapse identity.

All results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).
-/

open scoped BigOperators
open Finset

namespace ArkLib.ProximityGap.SalieObstruction

noncomputable section

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **χ-triviality on a square-set.** If every element of a finset `G` is a (nonzero) square in `F`,
the quadratic character is identically `1` on `G`. This is the prize-regime fact: in the dyadic
regime with `n ∣ (q−1)/2` (i.e. `v₂(q−1) > log₂ n`), every element of `μ_n` is a square. -/
theorem quadraticChar_eq_one_on_squareSet
    {G : Finset F} (hsq : ∀ x ∈ G, ∃ y : F, y ≠ 0 ∧ x = y ^ 2) :
    ∀ x ∈ G, quadraticChar F x = 1 := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hsq x hx
  exact quadraticChar_sq_one' hy

/-- **The Salié-twist collapse (the obstruction).** When every element of the summation domain `G`
is a nonzero square in `F`, the quadratic-character-twisted "subgroup-Salié" sum equals the
untwisted BGK period `∑_{x∈G} f x`. The χ-twist — the only candidate that could make the
under-determined floor a Salié sum — supplies nothing in the prize regime. Stated for an arbitrary
weight `f : F → ℂ` (instantiate `f x = ψ (b * x)` to get `T_b = η_b`). -/
theorem subgroupSalieTwist_collapse
    {G : Finset F} (hsq : ∀ x ∈ G, ∃ y : F, y ≠ 0 ∧ x = y ^ 2) (f : F → ℂ) :
    (∑ x ∈ G, (quadraticChar F x : ℂ) * f x) = ∑ x ∈ G, f x := by
  refine Finset.sum_congr rfl (fun x hx => ?_)
  rw [quadraticChar_eq_one_on_squareSet hsq x hx]
  push_cast
  ring

/-- **Specialization to the BGK period.** With `f x = ψ (b * x)` the twisted subgroup-Salié sum over
a square-set domain is exactly the BGK period `η_b = ∑_{x∈G} ψ(b x)`. The Salié route degenerates to
the open wall. -/
theorem subgroupSalie_eq_bgk_period
    {G : Finset F} (hsq : ∀ x ∈ G, ∃ y : F, y ≠ 0 ∧ x = y ^ 2)
    (ψ : AddChar F ℂ) (b : F) :
    (∑ x ∈ G, (quadraticChar F x : ℂ) * ψ (b * x)) = ∑ x ∈ G, ψ (b * x) :=
  subgroupSalieTwist_collapse hsq (fun x => ψ (b * x))

/-- **The squaring map is index-2 on dyadic data (the negation-symmetry obstruction).** The hoped-for
Salié closed form comes from `x = y²`; here we record the elementary fact that on a `2`-power-order
cyclic structure squaring is `2`-to-`1` onto the squares, so the substitution re-funnels into a
self-similar (smaller-subgroup) period rather than collapsing to a single Gauss sum. Concretely:
for `x ≠ 0`, the fiber `{y : y² = x}` over a square `x` has exactly two elements `{y, −y}` whenever
`−1 ≠ 1` (char ≠ 2), i.e. squaring is genuinely 2-to-1, never an isomorphism. -/
theorem sq_fiber_card_two (hF : ringChar F ≠ 2) {x y : F} (hy : y ≠ 0) (hxy : x = y ^ 2) :
    ({z : F | z ^ 2 = x} : Set F) = {y, -y} := by
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · intro hz
    have : z ^ 2 = y ^ 2 := by rw [hz, hxy]
    have hfac : (z - y) * (z + y) = 0 := by linear_combination this
    rcases mul_eq_zero.mp hfac with h | h
    · left; linear_combination h
    · right; linear_combination h
  · rintro (rfl | rfl)
    · exact hxy.symm
    · rw [hxy]; ring

/-- `y ≠ −y` when `y ≠ 0` and `char ≠ 2`: the two square-roots are genuinely distinct, so squaring
is strictly 2-to-1 (not injective) — the structural reason the Salié square-substitution does not
collapse the dyadic subgroup period to a single Gauss sum. -/
theorem sqrt_pair_distinct (hF : ringChar F ≠ 2) {y : F} (hy : y ≠ 0) : y ≠ -y := by
  intro h
  have h2 : (2 : F) * y = 0 := by linear_combination h
  rcases mul_eq_zero.mp h2 with h0 | h0
  · exact (Ring.two_ne_zero hF) h0
  · exact hy h0

end

end ArkLib.ProximityGap.SalieObstruction

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SalieObstruction.quadraticChar_eq_one_on_squareSet
#print axioms ArkLib.ProximityGap.SalieObstruction.subgroupSalieTwist_collapse
#print axioms ArkLib.ProximityGap.SalieObstruction.subgroupSalie_eq_bgk_period
#print axioms ArkLib.ProximityGap.SalieObstruction.sq_fiber_card_two
#print axioms ArkLib.ProximityGap.SalieObstruction.sqrt_pair_distinct
