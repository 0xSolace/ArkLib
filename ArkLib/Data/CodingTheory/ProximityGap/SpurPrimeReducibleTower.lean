/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# `Φ_{2^m}` is REDUCIBLE mod `3` for ALL `m ≥ 3` — the uniform-in-`m` candidate-persistence of the
# spur prime `p = 3` (Issue #444)

The char-`p` energy splits `E_r = E_r^{(0)} + Spur_r(p)`, and a prime `p` is a *candidate bad prime*
at dyadic depth `m` only if `Φ_{2^m}` is **reducible** mod `p` (a necessary condition: some short
relation can vanish in an extension `F_{p^f}` only when `Φ_{2^m}` actually splits there). The concrete
witnesses (`SpurWeightThree`, `SpurPrimePersistTower`) show `p = 3` is bad at `m = 3, 4` by exhibiting a
shared factor at each depth. This file gives the **uniform-in-`m`** structural reason those factors
keep existing: `Φ_{2^m}` is reducible mod `3` for *every* `m ≥ 3`, via a single tower identity.

## The mechanism: the dyadic doubling identity lifts reducibility up the whole tower

Over ANY commutative ring, `Φ_{2^{m+1}} = X^{2^m} + 1 = (X^2)^{2^{m-1}} + 1 = Φ_{2^m}(X^2)` — i.e.

>   `cyclotomic (2^{m+1}) R = (cyclotomic (2^m) R).comp (X^2)`   (`m ≥ 1`).

So composition with `X²` carries any factorization one rung up the tower: if `g ∣ Φ_{2^m}` then
`g.comp(X²) ∣ Φ_{2^{m+1}}`, and `natDegree (g.comp X²) = 2·natDegree g`, so a non-unit stays a non-unit.
Starting from the `m = 3` base (`Φ_8 = (X²+X−1)(X²−X−1)` over `F_3`, `SpurWeightThree.phi8_factor_mod3`),
this **lifts to every `m ≥ 3` by induction**: `Φ_{2^m}` always has the non-unit divisor obtained by
iterating `X ↦ X²` on `X²+X−1`. Hence `Φ_{2^m}` is reducible mod `3` for all `m ≥ 3`.

Probe `probe_phi_reducible_mod3_uniform.py` (exact sympy, `m = 3..8`): `Φ_{2^m}` mod 3 splits into
exactly 2 irreducible factors, each of degree `ord_{2^m}(3) = 2^{m-2} = ½·deg` — the non-cyclicity of
`(ℤ/2^m)*` (`m ≥ 3`) makes `3` never a primitive root, so `Φ` never stays irreducible.
Probe `probe_phi_doubling_lift.py`: `Φ_{2^{m+1}} = Φ_{2^m}(X²)` and the `X²+X−1` lift divides `Φ_{2^m}`
at every `m = 3..7`.

## Honest scope

NOT a CORE bound, NOT a refutation, NOT full Spur-persistence. *Reducibility* of `Φ_{2^m}` mod 3 is
NECESSARY but not sufficient for a genuine `Spur` collision (one also needs a SHORT antipodal-free
relation among the factors — supplied at low `m` by the witness files). This file proves the necessary
condition holds uniformly in `m` (so `3` stays a CANDIDATE bad prime at every depth), via a clean
tower identity that is itself a reusable brick (`cyclotomic_two_pow_succ_eq_comp_sq`). It carries no
capacity / beyond-Johnson / cliff-at-`n/2` / `δ*→0` claim. `CORE M(μ_n) ≤ C·√(n·log(p/n))` OPEN.

Issue #444.
-/

open Polynomial

namespace ArkLib.ProximityGap.SpurPrimeReducible

local instance fact3 : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- **`Φ_{2^m} = X^{2^{m−1}} + 1` over any commutative ring** (`m ≥ 1`). The `p = 2` prime-power
cyclotomic; pulled out as a reusable named form. -/
theorem cyclotomic_two_pow {R : Type*} [CommRing R] {m : ℕ} (hm : 1 ≤ m) :
    cyclotomic (2 ^ m) R = X ^ (2 ^ (m - 1)) + 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have hm1 : 1 + k - 1 = k := by omega
  rw [hm1]
  have h : (2 : ℕ) ^ (1 + k) = 2 ^ (k + 1) := by ring_nf
  rw [h, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  ring

/-- **THE DYADIC DOUBLING IDENTITY: `Φ_{2^{m+1}} = Φ_{2^m}(X²)` over any commutative ring** (`m ≥ 1`).
Both sides equal `X^{2^m} + 1`. This is the single lever that lifts factorizations up the dyadic tower. -/
theorem cyclotomic_two_pow_succ_eq_comp_sq {R : Type*} [CommRing R] {m : ℕ} (hm : 1 ≤ m) :
    cyclotomic (2 ^ (m + 1)) R = (cyclotomic (2 ^ m) R).comp (X ^ 2) := by
  rw [cyclotomic_two_pow (Nat.le_succ_of_le hm), cyclotomic_two_pow hm]
  simp only [add_comp, pow_comp, X_comp, one_comp]
  rw [← pow_mul]
  congr 2
  have h1 : m + 1 - 1 = (m - 1) + 1 := by omega
  rw [h1, pow_succ, mul_comm]

/-- `natDegree (X^2) = 2` over a nontrivial commutative ring. -/
theorem natDegree_X_sq {R : Type*} [CommRing R] [Nontrivial R] :
    (X ^ 2 : R[X]).natDegree = 2 := by
  simp [natDegree_X_pow]

/-- **Reducibility lifts through `comp (X²)`:** over a field, if `p` is NOT irreducible and has positive
degree, then `p.comp (X²)` is not irreducible either. The factorization `p = a*b` (both non-unit)
lifts to `p.comp(X²) = a.comp(X²) * b.comp(X²)` with both factors non-unit (their degrees double). -/
theorem not_irreducible_comp_sq_of_not_irreducible {K : Type*} [Field K] {p : K[X]}
    (hp : 0 < p.natDegree) (hred : ¬ Irreducible p) :
    ¬ Irreducible (p.comp (X ^ 2)) := by
  -- p is not a unit (positive degree) and not irreducible ⟹ p = a*b with a,b non-units (a, b ≠ 0).
  have hpu : ¬ IsUnit p := by
    intro hu
    rw [Polynomial.natDegree_eq_zero_of_isUnit hu] at hp
    exact absurd hp (lt_irrefl 0)
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  -- extract a non-trivial factorization from ¬Irreducible
  rw [irreducible_iff, not_and_or] at hred
  rcases hred with h | h
  · exact absurd hpu h
  · push_neg at h
    obtain ⟨a, b, hab, hau, hbu⟩ := h
    -- a, b have positive degree (non-unit, nonzero since product is p ≠ 0)
    have ha0 : a ≠ 0 := by rintro rfl; simp [hab] at hp0
    have hb0 : b ≠ 0 := by rintro rfl; simp [hab] at hp0
    have hadeg : 0 < a.natDegree := by
      rcases Nat.eq_zero_or_pos a.natDegree with h0 | h0
      · exact absurd ((Polynomial.isUnit_iff_degree_eq_zero).2
          (by rw [Polynomial.degree_eq_natDegree ha0, h0]; rfl)) hau
      · exact h0
    have hbdeg : 0 < b.natDegree := by
      rcases Nat.eq_zero_or_pos b.natDegree with h0 | h0
      · exact absurd ((Polynomial.isUnit_iff_degree_eq_zero).2
          (by rw [Polynomial.degree_eq_natDegree hb0, h0]; rfl)) hbu
      · exact h0
    -- lift: p.comp(X²) = a.comp(X²) * b.comp(X²)
    rw [irreducible_iff, not_and_or]; right; push_neg
    refine ⟨a.comp (X ^ 2), b.comp (X ^ 2), by rw [hab, mul_comp], ?_, ?_⟩
    · -- a.comp(X²) non-unit: its natDegree = 2*natDegree a > 0
      intro hu
      have : (a.comp (X ^ 2)).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      rw [natDegree_comp, natDegree_X_sq] at this
      omega
    · intro hu
      have : (b.comp (X ^ 2)).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
      rw [natDegree_comp, natDegree_X_sq] at this
      omega

/-- `Φ_{2^m}` over `F_3` has positive degree for `m ≥ 1` (`natDegree = 2^{m-1} ≥ 1`). -/
theorem natDegree_cyclotomic_two_pow_pos {m : ℕ} (hm : 1 ≤ m) :
    0 < (cyclotomic (2 ^ m) (ZMod 3)).natDegree := by
  rw [Polynomial.natDegree_cyclotomic]
  have : 0 < Nat.totient (2 ^ m) := Nat.totient_pos.2 (by positivity)
  exact this

/-- **Base case: `Φ_8` is NOT irreducible over `F_3`** (`SpurWeightThree.phi8_factor_mod3`:
`X⁴+1 = (X²+X−1)(X²−X−1)`, both non-unit). -/
theorem not_irreducible_phi8_mod3 : ¬ Irreducible (cyclotomic (2 ^ 3) (ZMod 3)) := by
  rw [show cyclotomic (2 ^ 3) (ZMod 3) = X ^ 4 + 1 by
        rw [cyclotomic_two_pow (by norm_num)]; norm_num]
  rw [show (X ^ 4 + 1 : (ZMod 3)[X]) = (X ^ 2 + X - 1) * (X ^ 2 - X - 1) by
        have h3 : (3 : (ZMod 3)[X]) = 0 := by
          have : (3 : ZMod 3) = 0 := by decide
          calc (3 : (ZMod 3)[X]) = C (3 : ZMod 3) := by norm_cast
            _ = 0 := by rw [this]; exact map_zero C
        linear_combination (X ^ 2) * h3]
  rw [irreducible_iff, not_and_or]; right; push_neg
  refine ⟨X ^ 2 + X - 1, X ^ 2 - X - 1, rfl, ?_, ?_⟩
  · intro hu
    have hd : (X ^ 2 + X - 1 : (ZMod 3)[X]).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have h2 : (X ^ 2 + X - 1 : (ZMod 3)[X]).natDegree = 2 := by compute_degree!
    omega
  · intro hu
    have hd : (X ^ 2 - X - 1 : (ZMod 3)[X]).natDegree = 0 := Polynomial.natDegree_eq_zero_of_isUnit hu
    have h2 : (X ^ 2 - X - 1 : (ZMod 3)[X]).natDegree = 2 := by compute_degree!
    omega

/-- **THE UNIFORM THEOREM: `Φ_{2^m}` is REDUCIBLE (not irreducible) mod `3` for ALL `m ≥ 3`.**
Induction from the `m = 3` base via the dyadic doubling identity
`Φ_{2^{m+1}} = Φ_{2^m}(X²)` (`cyclotomic_two_pow_succ_eq_comp_sq`) and the
`comp(X²)` reducibility lift (`not_irreducible_comp_sq_of_not_irreducible`).

So the spur prime `p = 3` stays a CANDIDATE bad prime at every dyadic depth `m ≥ 3` (the necessary
splitting condition for any in-extension short-relation vanishing holds uniformly). This is the
uniform-in-`m` structural reason behind the concrete `m = 3, 4` persistence witnesses
(`SpurWeightThree`, `SpurPrimePersistTower`). NOT full Spur-persistence (which also needs a SHORT
antipodal-free relation among the factors), and NOT a CORE bound. `CORE OPEN.` -/
theorem not_irreducible_cyclotomic_two_pow_mod3 {m : ℕ} (hm : 3 ≤ m) :
    ¬ Irreducible (cyclotomic (2 ^ m) (ZMod 3)) := by
  induction m with
  | zero => omega
  | succ k ih =>
    rcases Nat.lt_or_ge k 3 with hk | hk
    · -- k+1 = 3 (since 3 ≤ k+1 and k < 3 ⟹ k = 2)
      interval_cases k
      · omega
      · omega
      · exact not_irreducible_phi8_mod3
    · -- k ≥ 3: lift from Φ_{2^k}
      have hk1 : 1 ≤ k := by omega
      rw [cyclotomic_two_pow_succ_eq_comp_sq hk1]
      exact not_irreducible_comp_sq_of_not_irreducible
        (natDegree_cyclotomic_two_pow_pos hk1) (ih hk)

end ArkLib.ProximityGap.SpurPrimeReducible

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.cyclotomic_two_pow_succ_eq_comp_sq
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_comp_sq_of_not_irreducible
#print axioms ArkLib.ProximityGap.SpurPrimeReducible.not_irreducible_cyclotomic_two_pow_mod3
