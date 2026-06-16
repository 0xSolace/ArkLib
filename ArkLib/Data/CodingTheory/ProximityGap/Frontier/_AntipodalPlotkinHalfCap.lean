/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Coeff
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Group.Nat

/-!
# The antipodal far-line route caps at delta* >= 1/2 (Plotkin half-agreement) (#444 / #407)

`_AntipodalAgreementScope` proved *when* the off-BGK antipodal tower applies: precisely to **even or
odd** agreement polynomials (whose root set is negation-closed). This file proves the complementary
*ceiling*: the **odd** branch of that route caps at the **Plotkin half-agreement** delta* >= 1/2, so
on the prize side (rate `rho < 1/4`, where the floor is `1 - rho - Theta(1/log n) > 1/2`) the
antipodal route lies strictly BELOW the floor and is **prize-inert**. This is lalalune's #444
master-open-thread item 5 ("antipodal route caps at delta* = 1/2 (Plotkin ceiling) -- provable;
isolate the residual to *asymmetric* far-line words"), an axiom-clean structural separation.

## Mechanism (char != 2)

An **odd** agreement polynomial `P` (`P(-X) = -P`, equivalently `P.eval (-z) = - P.eval z`) cannot
hit a fixed nonzero value `c` at both `z` and `-z`: if `P z = c` then `P (-z) = -c`, and `-c != c`
because `c != 0` and `2 != 0`. So the agreement set `A_c = {z in G : P z = c}` is **antipode-free**:
it contains at most one of each antipodal pair `{z, -z}`. On a negation-closed set `G` carrying the
fixed-point-free involution `z |-> -z`, an antipode-free subset has cardinality `<= G.card / 2`.
Hence `#A_c <= |G|/2` and the far-line agreement with any single nonzero codeword value is at most
half the subgroup -- the Plotkin half-cap, giving `delta* >= 1/2`.

Probe `scripts/probes/probe_antipodal_plotkin_cap.py` (PROPER thin mu_n, p >> n^3, p == 1 mod n, two
structured primes per n, never n = q-1, n = 8..64): **0 paired-violations**, value-multiplicity
always `<= n/2`. The `rho = 1/4` worst word `x^a + x^b` (a, b both odd) is odd
(`AntipodalAgreementScope.twoMonomial_odd_of_both_odd`) -- in scope, so the cap applies to it.

## Honest scope

Char-free finite combinatorics over a field of char != 2; **field-universal**, NOT
thinness-essential (the half-cap is the antipodal-symmetry Plotkin ceiling, regime-independent). It
follows that the antipodal route caps at Plotkin and does NOT close the
prize: it CAPS the symmetric/antipodal route and thereby **isolates** the hard residual to the
genuinely *asymmetric* (non even/odd) far-line words, which `_AntipodalAgreementScope` already pins
as the open BGK core. CORE `M(mu_n) <= C sqrt(n log(p/n))` stays OPEN. Axiom-clean. (#407, #444.)
-/

open Polynomial

namespace ProximityGap.Frontier.AntipodalPlotkinHalfCap

open scoped Classical

variable {F : Type*} [Field F]

/-- **Odd polynomials negate their values** (the working hypothesis, matching
`_AntipodalAgreementScope.eval_neg_eq_neg_of_odd`): `P(-z) = -P(z)`. -/
def IsOddOn (P : F[X]) : Prop := ∀ z : F, P.eval (-z) = - P.eval z

/-- An odd polynomial cannot hit a **nonzero** value `c` at both `z` and `-z` (char != 2). -/
theorem not_both_of_odd {P : F[X]} (hodd : IsOddOn P) {c : F} (hc : c ≠ 0)
    (htwo : (2 : F) ≠ 0) {z : F} (hz : P.eval z = c) : P.eval (-z) ≠ c := by
  rw [hodd z, hz]
  intro h
  -- -c = c  =>  2 c = 0  =>  c = 0 (char != 2), contradiction
  apply hc
  have h2c : c + c = 0 := by
    have hcc : -c + c = c + c := by rw [h]
    rw [neg_add_cancel] at hcc
    exact hcc.symm
  have hmul : (2 : F) * c = 0 := by rw [two_mul]; exact h2c
  rcases mul_eq_zero.mp hmul with h2 | hc0
  · exact absurd h2 htwo
  · exact hc0

/-- The **agreement set** of `P` at value `c` over a negation-closed evaluation set `G`. -/
noncomputable def agreeSet (P : F[X]) (G : Finset F) (c : F) : Finset F :=
  G.filter (fun z => P.eval z = c)

/-- **Antipode-freeness of the agreement set** (char != 2): for a nonzero target `c` and an odd `P`,
if `z` is in the agreement set then `-z` is not. This is the structural core of the half-cap. -/
theorem agreeSet_antipode_free {P : F[X]} (hodd : IsOddOn P) {G : Finset F} {c : F}
    (hc : c ≠ 0) (htwo : (2 : F) ≠ 0) {z : F} (hz : z ∈ agreeSet P G c) :
    (-z) ∉ agreeSet P G c := by
  simp only [agreeSet, Finset.mem_filter] at hz ⊢
  rintro ⟨_, hroot⟩
  exact not_both_of_odd hodd hc htwo hz.2 hroot

/-- The negation map is a **fixed-point-free involution** on a field of char != 2: `-z != z` for any
`z` such that ... ` -z = z` forces `z = 0`. We package the disjointness needed for the half-cap:
the agreement set and its pointwise negation are disjoint. -/
theorem agreeSet_disjoint_neg {P : F[X]} (hodd : IsOddOn P) {G : Finset F} {c : F}
    (hc : c ≠ 0) (htwo : (2 : F) ≠ 0) :
    Disjoint (agreeSet P G c) ((agreeSet P G c).image (fun z => -z)) := by
  rw [Finset.disjoint_left]
  intro a ha hain
  rw [Finset.mem_image] at hain
  obtain ⟨b, hb, hba⟩ := hain
  -- a = -b, and both a, b in the agreement set; but -b not in it (antipode-free on b)
  have hnb : (-b) ∉ agreeSet P G c := agreeSet_antipode_free hodd hc htwo hb
  rw [hba] at hnb
  exact hnb ha

/-- **Plotkin half-cap (Finset form).** For an odd `P`, a nonzero target `c`, and char != 2, the
agreement set of `P` at `c` over `G` injects into a set disjoint from its own negation-image of
equal size, so `2 * #agreeSet <= #(agreeSet) + #(neg-image)`. We state the
clean consequence: `2 * (agreeSet P G c).card <= (G ∪ G.image Neg.neg).card`. When `G` is
negation-closed this is `<= G.card`, giving the half-cap. -/
theorem two_mul_agreeSet_card_le {P : F[X]} (hodd : IsOddOn P) {G : Finset F} {c : F}
    (hc : c ≠ 0) (htwo : (2 : F) ≠ 0) :
    2 * (agreeSet P G c).card ≤ (G ∪ G.image (fun z => -z)).card := by
  set A := agreeSet P G c with hA
  have hneg_card : (A.image (fun z => -z)).card = A.card := by
    apply Finset.card_image_of_injective
    intro x y hxy
    simpa using hxy
  have hdisj := agreeSet_disjoint_neg hodd hc htwo (P := P) (G := G) (c := c)
  have hunion : (A ∪ A.image (fun z => -z)).card = A.card + A.card := by
    rw [Finset.card_union_of_disjoint hdisj, hneg_card]
  -- A ⊆ G and A.image Neg ⊆ G.image Neg, so the union ⊆ G ∪ G.image Neg
  have hAG : A ⊆ G := by
    intro x hx
    simp only [hA, agreeSet, Finset.mem_filter] at hx
    exact hx.1
  have hsub : A ∪ A.image (fun z => -z) ⊆ G ∪ G.image (fun z => -z) := by
    apply Finset.union_subset_union hAG
    exact Finset.image_subset_image hAG
  calc 2 * A.card = A.card + A.card := by ring
    _ = (A ∪ A.image (fun z => -z)).card := by rw [hunion]
    _ ≤ (G ∪ G.image (fun z => -z)).card := Finset.card_le_card hsub

/-- **Plotkin half-cap on a negation-closed `G`.** If `G` is closed under negation
(`g ∈ G ⟹ -g ∈ G`), then `G.image Neg.neg ⊆ G`, so `G ∪ G.image Neg = G`, and the cap reads
`2 * #agreeSet <= #G`: the agreement with any single nonzero value is at most half the subgroup.
This is **delta* >= 1/2** (Plotkin) for the odd/antipodal far-line route. -/
theorem two_mul_agreeSet_card_le_of_neg_closed {P : F[X]} (hodd : IsOddOn P) {G : Finset F} {c : F}
    (hc : c ≠ 0) (htwo : (2 : F) ≠ 0) (hG : ∀ g ∈ G, -g ∈ G) :
    2 * (agreeSet P G c).card ≤ G.card := by
  have himg : G.image (fun z => -z) ⊆ G := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨g, hg, hgx⟩ := hx
    rw [← hgx]; exact hG g hg
  have hunion : G ∪ G.image (fun z => -z) = G := Finset.union_eq_left.mpr himg
  have := two_mul_agreeSet_card_le hodd hc htwo (P := P) (G := G) (c := c)
  rwa [hunion] at this

/-- **The clean Plotkin ceiling.** On a negation-closed `G`, an odd far-line agreement polynomial
agrees with any single nonzero codeword value on at most `#G / 2` points -- the symmetric/antipodal
route is capped at half-agreement `delta* >= 1/2`. For prize rate `rho < 1/4` the floor
`1 - rho - Theta(1/log n) > 1/2`, so this route is **below the floor / prize-inert**, isolating the
hard residual to genuinely asymmetric far-line words. -/
theorem agreeSet_card_le_half {P : F[X]} (hodd : IsOddOn P) {G : Finset F} {c : F}
    (hc : c ≠ 0) (htwo : (2 : F) ≠ 0) (hG : ∀ g ∈ G, -g ∈ G) :
    (agreeSet P G c).card ≤ G.card / 2 := by
  have h := two_mul_agreeSet_card_le_of_neg_closed hodd hc htwo hG (P := P) (c := c)
  omega

end ProximityGap.Frontier.AntipodalPlotkinHalfCap

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.AntipodalPlotkinHalfCap.not_both_of_odd
#print axioms ProximityGap.Frontier.AntipodalPlotkinHalfCap.two_mul_agreeSet_card_le_of_neg_closed
#print axioms ProximityGap.Frontier.AntipodalPlotkinHalfCap.agreeSet_card_le_half
