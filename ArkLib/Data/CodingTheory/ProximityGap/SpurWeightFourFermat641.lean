/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Tactic.NormNum.Prime

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# The weight-4 spurious collision at the STRUCTURED Fermat prime `641`, `m = 5` (Issue #444)

This file is the **structured-prime companion** to `SpurWeightFourCollision` (`Spur_2(17) ≥ 1` at
`m = 4`).  It exhibits the SAME antipodal-free weight-4 relation `1 + ζ + ζ² + ζ⁴` colliding at the
**Fermat-type** prime `p = 641` (which divides `2³² + 1`, the Fermat number `F_5`) at `m = 5`
(`μ_32`), again with a clean **base-field** (degree-1) witness.

## Why the structured prime matters (brief §2: structured primes incl. Fermat-type)

The honesty contract requires probing the Spur tower at **structured** primes (Fermat-type
`p ∣ 2^{2^k} + 1`), not only generic ones — structured primes are exactly where additive-moment
routes generate false positives (§3 meta-thm), so a genuine char-`p` collision there is informative.
`641 ∣ 2³² + 1` (Euler's factor of `F_5`), and `32 ∣ 641 − 1` (so `μ_32 ⊆ F_641^*`); the probe
(`probe_spur_w4_fermat641.py`, exact `sympy`/`ZMod`) finds the weight-4 relation `1 + ζ + ζ² + ζ⁴`
(exponent set `{0,1,2,4}`, antipodal-free at `m = 5` since no pair differs by `2^{m−1} = 16`)
collides at `641`:

> over `F_641`, `g = 282` is a primitive `32`-nd root of unity (`g^{16} = −1`, order `32`), and
> `1 + g + g² + g⁴ = 0` — a char-`641`-only antipodal-free vanishing relation among `32`-nd roots.

So `(X − 282)` divides BOTH `Φ_32 = X^{16} + 1` and `1 + X + X² + X⁴` over `F_641`, hence they are
not coprime, hence `641 ∣ N(1 + ζ + ζ² + ζ⁴)` (indeed `N = 2 · 641` at `m = 5`), hence
`Spur_2(641) ≥ 1`.

## Results (axiom-clean)

* `phi32_zmod641`               : `Φ_32 = X^{16} + 1` over `F_641`.
* `g_isRoot_phi32`              : `282` is a (base-field) root of `Φ_32` over `F_641`.
* `g_isRoot_rel`               : `282` is a root of `1 + X + X² + X⁴` over `F_641`.
* `linfac_dvd_phi32` / `linfac_dvd_rel` : `(X − 282)` divides each (deg-1 `dvd_iff_isRoot`).
* `weight4_relation_not_coprime_mod641` : **THE STRUCTURED-PRIME RUNG** — `Φ_32` and `1+X+X²+X⁴`
    are NOT coprime over `F_641`, i.e. `641 ∣ N(1+ζ+ζ²+ζ⁴)`, i.e. `Spur_2(641) ≥ 1`.

## Honest scope (rules 1, 2, 3, 6)

NOT a CORE closure. It is the structured-prime (Fermat-type) companion to the `m = 4` witness:
it confirms the weight-4 spurious collision persists at a Fermat-divisor prime, exactly the regime
where moment routes produce false positives — so this char-`641` relation is a genuine arithmetic
obstruction, not a moment artifact.  HONEST regime note (rule 2): `641` is structured but NOT in the
deep prize window `p ≫ n³` (here `n³ = 32³ = 32768 > 641`); it is a structured-small witness showing
the Spur support *includes* Fermat-type primes, not a prize-regime instance.  Thinness-essential in
the mild rung sense (`32 ∣ 641 − 1` ⇒ `μ_32 ⊆ F_641^*`; vacuous for `n = q − 1`).  The OPEN core is
the *count* `Spur_r(p)` at depth `r ≈ log q` over prize-regime primes — the BCHKS-1.12 wall.  CORE
(`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
- `SpurWeightFourCollision.lean` (`m = 4`, `p = 17` base-field rung); `SpurWeightThreeCollision.lean`.
- Probe: `scripts/probes/probe_spur_w4_fermat641.py`.
-/

open Polynomial

namespace ArkLib.ProximityGap.SpurWeightFourFermat

/-- `641` is prime, so `ZMod 641 = F_641` is a field. -/
local instance fact641 : Fact (Nat.Prime 641) := ⟨by norm_num⟩

/-- **`Φ_32 = X^{16} + 1` over `F_641`.** The `2^m`-th cyclotomic polynomial is `X^{2^{m−1}} + 1`;
here `m = 5` gives `X^{16} + 1`. Holds over any commutative ring; we instantiate at `F_641`. -/
theorem phi32_zmod641 : cyclotomic (2 ^ 5) (ZMod 641) = X ^ 16 + 1 := by
  have h : (2 : ℕ) ^ 5 = 2 ^ ((5 - 1) + 1) := by norm_num
  rw [h, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [add_comm]

/-- **`282` is a primitive `32`-nd root of unity in the base field `F_641`** (a root of
`Φ_32 = X^{16} + 1`, i.e. `282^{16} = −1`). The Fermat prime `641 ∣ 2³² + 1`. -/
theorem g_isRoot_phi32 :
    (X ^ 16 + 1 : (ZMod 641)[X]).IsRoot (282 : ZMod 641) := by
  simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_one]
  decide

/-- **`282` is a root of the weight-4 antipodal-free relation `1 + X + X² + X⁴` over `F_641`.** The
exponent set `{0,1,2,4}` is antipodal-free at `m = 5` (no two indices differ by `2^{m−1} = 16`), and
over `ℂ` the sum `1 + ζ + ζ² + ζ⁴ ≠ 0`; this root in `F_641` is the char-`641`-only collision. -/
theorem g_isRoot_rel :
    (1 + X + X ^ 2 + X ^ 4 : (ZMod 641)[X]).IsRoot (282 : ZMod 641) := by
  simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_one]
  decide

/-- `(X − 282)` divides `Φ_32` over `F_641` (degree-1 factor ↔ base-field root). -/
theorem linfac_dvd_phi32 :
    (X - C (282 : ZMod 641)) ∣ cyclotomic (2 ^ 5) (ZMod 641) := by
  rw [phi32_zmod641, dvd_iff_isRoot]; exact g_isRoot_phi32

/-- `(X − 282)` divides the weight-4 relation `1 + X + X² + X⁴` over `F_641`. -/
theorem linfac_dvd_rel :
    (X - C (282 : ZMod 641)) ∣ (1 + X + X ^ 2 + X ^ 4 : (ZMod 641)[X]) := by
  rw [dvd_iff_isRoot]; exact g_isRoot_rel

/-- The shared factor `X − 282` is a NON-unit (`natDegree = 1`; units have `natDegree 0`). -/
theorem nonunit_linfac : ¬ IsUnit (X - C (282 : ZMod 641)) := by
  intro hu
  have hd : (X - C (282 : ZMod 641)).natDegree = 0 :=
    Polynomial.natDegree_eq_zero_of_isUnit hu
  have h1 : (X - C (282 : ZMod 641)).natDegree = 1 := natDegree_X_sub_C _
  omega

/-- **THE STRUCTURED-PRIME RUNG: `Φ_32` and the weight-4 antipodal-free relation `1+X+X²+X⁴` are NOT
coprime over `F_641`.** Equivalently, the Fermat-type prize prime `p = 641` (`641 ∣ 2³² + 1`) divides
the cyclotomic norm `N(1 + ζ + ζ² + ζ⁴)` (`= 2·641` at `m = 5`): they share the base-field root
`282`, a primitive `32`-nd root of unity in `F_641` with `1 + 282 + 282² + 282⁴ = 0`.

Hence the weight-4 spurious-collision count `Spur_2(641) ≥ 1` at a STRUCTURED (Fermat-type) prime —
exactly the regime where additive-moment routes generate false positives, so this is a genuine
char-`641` arithmetic collision, companion to the `m = 4`, `p = 17` base-field witness. -/
theorem weight4_relation_not_coprime_mod641 :
    ¬ IsCoprime (cyclotomic (2 ^ 5) (ZMod 641)) (1 + X + X ^ 2 + X ^ 4 : (ZMod 641)[X]) := by
  intro hcop
  exact nonunit_linfac (hcop.isUnit_of_dvd' linfac_dvd_phi32 linfac_dvd_rel)

end ArkLib.ProximityGap.SpurWeightFourFermat

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SpurWeightFourFermat.phi32_zmod641
#print axioms ArkLib.ProximityGap.SpurWeightFourFermat.g_isRoot_phi32
#print axioms ArkLib.ProximityGap.SpurWeightFourFermat.g_isRoot_rel
#print axioms ArkLib.ProximityGap.SpurWeightFourFermat.weight4_relation_not_coprime_mod641
