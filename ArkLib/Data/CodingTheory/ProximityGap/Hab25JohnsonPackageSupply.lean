/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CellPencilJohnson
import ArkLib.Data.CodingTheory.ProximityGap.Hab25CellDichotomyWiring
import ArkLib.Data.CodingTheory.ProximityGap.Hab25JohnsonDischarge

/-!
# The Johnson discharge from ONE named residual: the per-cell §5 package (#357, #348)

The Johnson lane's consumer chain is fully proven in-tree and axiom-clean:

  `CellPackage` (this file) → `cell_improvement_of_pinning_package'`
  → `himpr` → `johnsonNumericBound_holds_of_himpr` → `JohnsonNumericBound`
  → `JohnsonDischargeStatement`.

This file names the single remaining input.  `CellPackage` bundles the [BCIKS20] §5
heavy-agreement package for one factor cell — the centre `x₀`, the surface hypotheses,
the Y-root divisor `w`, the per-coordinate matching sets with base/separability/fold
agreement, the kill-target weight budget, and the heavy pinning set `S₀`.
`CellPackageSupply` asserts: every large cell carries such a package.  The two welds —

* `himpr_of_cellPackageSupply` — supply ⟹ the funnel's per-cell disjunct, and
* `johnsonDischargeStatement_of_packageSupply` — supply at every instance ⟹ the
  full `JohnsonDischargeStatement`

— make the supply Prop the **exact** residual: discharging it (the [BCIKS20] Claim 5.7
γ-root production over the cell) is the only remaining mathematics on this lane.
-/

set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000

open Polynomial Polynomial.Bivariate PowerSeries
open BCIKS20AppendixA BCIKS20AppendixA.ClaimA2
open BCIKS20.HenselNumerator
open _root_.ProximityGap Code
open CodingTheory.ProximityGap.Hab25Core
open CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
open scoped NNReal ENNReal
open ArkLib

namespace BCIKS20.CellPencilJohnson

variable {F₀ : Type} [Field F₀]

/-- **The per-cell §5 heavy-agreement package.**  Everything
`cell_improvement_of_pinning_package'` consumes beyond the cell data itself: the place
curve `H` is a parameter (with its instances), all the [BCIKS20] §5 legs are fields. -/
structure CellPackage [Fintype F₀] [DecidableEq F₀] {n : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀) (k : ℕ) (δ : ℝ≥0) (u : WordStack F₀ (Fin 2) (Fin n))
    (R : (F₀[X])[X][Y])
    (H : F₀[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)] : Type where
  x₀ : F₀
  hHyp : Hypotheses x₀ R H
  hmonic : H.Monic
  htail : ∀ t, n ≤ t → αGenuine H x₀ R hHyp t = 0
  e : Fin n → F₀
  he : Function.Injective e
  u₀ : Fin n → F₀
  u₁ : Fin n → F₀
  D : ℕ
  hD : D ≥ Bivariate.totalDegree H
  matchingSet : Fin n → Finset F₀
  root : (z : F₀) → rationalRoot (H_tilde' H) z
  w : F₀[X][Y]
  hwdeg : w.natDegree < n
  hwdvd : (Polynomial.X - Polynomial.C w) ∣ R
  hbaseA : ∀ j, ∀ z ∈ matchingSet j, (w.eval (Polynomial.C x₀)).eval z = (root z).1
  hsepA : ∀ j, ∀ z ∈ matchingSet j,
    ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z (root z)
        (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
          hmonic.leadingCoeff z (root z))))).Separable
  hfold : ∀ j, ∀ z ∈ matchingSet j,
    (w.eval (Polynomial.C (e j) + Polynomial.C x₀)).eval z = u₀ j + z * u₁ j
  W : ℕ
  hweight : ∀ j, weight_Λ_over_𝒪 (Fact.out (p := 0 < H.natDegree))
      (Claim510Kill.killTarget H x₀ R hHyp n (e j) (u₀ j) (u₁ j)) D ≤ (W : WithBot ℕ)
  hcard : ∀ j, W * H.natDegree < (matchingSet j).card
  S₀ : Finset F₀
  hbase₀ : ∀ z ∈ S₀, (w.eval (Polynomial.C x₀)).eval z = (root z).1
  hsep₀ : ∀ z ∈ S₀,
    ((R.map (coeffHom_loc x₀ hHyp)).map
      (PowerSeries.map (π_hat_z hHyp z (root z)
        (BCIKS20.Claim510AgreementSupply.pi_z_xi_ne_zero_of_monic hHyp
          hmonic.leadingCoeff z (root z))))).Separable
  Bw : ℕ
  hBw : ∀ t, ((Polynomial.taylor (Polynomial.C x₀) w).coeff t).natDegree ≤ Bw
  hS₀ : max Bw 1 < S₀.card

/-- **The single named residual of the Johnson lane.**  Every cell of every stack is
either small (`≤ T`) or carries a §5 package.  Discharging this Prop — the [BCIKS20]
Claim 5.7 production of the centre, the Y-root divisor, and the matching sets over a
large cell — is the only remaining mathematics between the in-tree funnel and the
unconditional `JohnsonDischargeStatement`. -/
def CellPackageSupply [Fintype F₀] [DecidableEq F₀] {n : ℕ} [NeZero n]
    (domain : Fin n ↪ F₀) (k : ℕ) (δ : ℝ≥0) (T : ℕ) : Prop :=
  ∀ (u : WordStack F₀ (Fin 2) (Fin n)) (R : (F₀[X])[X][Y]) (E : Finset F₀)
    (P : F₀ → F₀[X]),
    Irreducible R →
    (∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ) →
    (∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
        R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) →
    E.card ≤ T ∨
    ∃ (H : F₀[X][Y]) (h1 : Fact (Irreducible H)) (h2 : Fact (0 < H.natDegree)),
      haveI := h1; haveI := h2
      Nonempty (CellPackage domain k δ u R H)

open Classical in
/-- **Supply ⟹ the funnel's per-cell disjunct.**  A cell with a §5 package yields the
improving pair via `cell_improvement_of_pinning_package'`; a small cell is small. -/
theorem himpr_of_cellPackageSupply [Fintype F₀] [DecidableEq F₀]
    {n k : ℕ} (hn : 0 < n) [NeZero n] {domain : Fin n ↪ F₀} {δ : ℝ≥0}
    {T : ℕ} (hT : 1 ≤ T) (hk : 0 < k)
    (hsupply : CellPackageSupply domain k δ T)
    (u : WordStack F₀ (Fin 2) (Fin n))
    (R : (F₀[X])[X][Y]) (E : Finset F₀) (P : F₀ → F₀[X])
    (hRirr : Irreducible R)
    (hdec : ∀ γ ∈ E, ∃ d : McaDecode domain k δ u γ, d.P = P γ)
    (hdvdR : ∀ γ ∈ E, (Polynomial.X - Polynomial.C (P γ)) ∣
      R.map (Polynomial.mapRingHom (Polynomial.evalRingHom γ))) :
    E.card ≤ T ∨ ∃ d₀ d₁ : Fin n → F₀, ∀ z ∈ E,
      ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0 := by
  rcases hsupply u R E P hRirr hdec hdvdR with hsmall | ⟨H, h1, h2, hpkg⟩
  · exact Or.inl hsmall
  · haveI := h1
    haveI := h2
    obtain ⟨pkg⟩ := hpkg
    exact cell_improvement_of_pinning_package' hn hT hk R hRirr E P hdec hdvdR
      pkg.x₀ pkg.hHyp h2.out pkg.hmonic pkg.htail pkg.e pkg.he pkg.u₀ pkg.u₁ pkg.hD
      pkg.matchingSet pkg.root pkg.hwdeg pkg.hwdvd pkg.hbaseA pkg.hsepA pkg.hfold
      pkg.hweight pkg.hcard pkg.S₀ pkg.hbase₀ pkg.hsep₀ pkg.hBw pkg.hS₀

open Classical in
/-- **The Johnson discharge from the named residual.**  If every instance in the
discharge range has cell-package supply at the funnel's tight budget, the full
`JohnsonDischargeStatement` holds.  The supply Prop is the exact remaining input:
everything else in the chain is proven. -/
theorem johnsonDischargeStatement_of_packageSupply
    (hsupply : ∀ (n k m : ℕ) (_ : NeZero n) (F₀ : Type) (_ : Field F₀) (_ : Fintype F₀)
      (_ : DecidableEq F₀) (domain : Fin n ↪ F₀) (δ : ℝ≥0),
      2 ≤ k → k + 1 ≤ n → 12 ≤ m → δ ≤ 1 →
      CellPackageSupply domain k δ
        (max (n * (GuruswamiSudan.constraintIndices m).card
          * (gs_degree_bound k n m / (k - 1))) n)) :
    JohnsonDischargeStatement := by
  intro n k m hNZ F₀ hF hFin hDec domain η δ hk2 hkn hm12 hδ1 hδJ hmle
  letI := hNZ
  letI := hF
  letI := hFin
  letI := hDec
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hmle' : (m : ℝ) ≤
      max (⌈((((k : ℝ) / Fintype.card (Fin n) + 1 / Fintype.card (Fin n)))
        ^ ((1 : ℝ) / 2)) / (2 * (η : ℝ))⌉ : ℝ) 3 := by
    rwa [Fintype.card_fin]
  refine johnsonNumericBound_holds_of_himpr domain η δ hk2 hkn hm12 hδ1 hδJ hmle' ?_
  intro u R E P hRirr hdec hdvdR
  exact himpr_of_cellPackageSupply hn (le_trans hn (le_max_right _ _)) (by omega)
    (hsupply n k m hNZ F₀ hF hFin hDec domain δ hk2 hkn hm12 hδ1) u R E P
    hRirr hdec hdvdR

end BCIKS20.CellPencilJohnson

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms BCIKS20.CellPencilJohnson.himpr_of_cellPackageSupply
#print axioms BCIKS20.CellPencilJohnson.johnsonDischargeStatement_of_packageSupply
