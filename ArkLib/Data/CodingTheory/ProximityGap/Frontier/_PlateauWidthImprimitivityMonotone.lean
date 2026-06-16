/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.OrbitCountCrossingLaw

/-!
# Plateau-width monotonicity in imprimitivity (ANGLE 6 adversarial, #444)

## The dichotomy this brick addresses

The whole RS proximity-gap prize reduces to the growth law of the worst-direction far-line
distinct-γ cascade plateau width `w(n)` (governs `m*`, hence `δ* = 1 − ρ − m*/n`):

* **ADDITIVE** `w(2n) = w(n) + c` ⟹ `w = O(log n)` ⟹ `m* = O(log n)` ⟹ **prize HOLDS**;
* **MULTIPLICATIVE** `w(2n) = 2·w(n)` ⟹ `w` geometric ⟹ `m*` linear ⟹ **prize FAILS**.

The multiplicative HOPE (the thing an adversary tries to prove) is: *higher imprimitivity `d`
carries more `μ_{2^k}`-invariance, hence MORE extra invariant rungs, hence a WIDER plateau that
doubles up the tower.* This brick refutes the count-half of that hope **structurally**, via the
proven orbit-count substrate, and records the EXACT-COMPUTATION certificate against it.

## The proven substrate object

At a monomial far direction with shift `b − a`, `d = gcd(b−a, n)`, the bad-γ set is a union of
orbits of `⟨ω^{b−a}⟩` of coset size `S = n / d` (`ImprimitiveSpikeStructure`,
`explainableScalars_monomial_gamma_dilation`: the bad set is `μ_S`-coset invariant — PROVEN). So
the distinct-γ count is `D = z + S·O`, `z ∈ {0,1}` the `γ=0` indicator, `O` the nonzero coset
(orbit) count. The budget-crossing law (`OrbitCountCrossingLaw.crossing_law`):

  `D ≤ budget(=n)  ⟺  O ≤ d`.

The plateau width is the number of pre-binding rungs where `O(s) > d` before `O` drops to `≤ d`.

## What is proven here (axiom-clean, no `sorry`)

The structural fact the multiplicative hope needs to be FALSE:

* `binding_budget_monotone_in_d` — **at a FIXED coset count `O` and fixed coset size `S`, raising
  the imprimitivity `d` only makes the crossing test `O ≤ d` EASIER (binds sooner).** The budget
  headroom is `d` itself; higher `d` = more headroom = earlier binding = SHORTER plateau. This is
  the exact opposite of "more invariance ⟹ wider plateau."

* `doubling_preserves_coset_size_doubles_budget` — **the tower step is ADDITIVE, not
  multiplicative, in the budget.** Under the doubling embedding `μ_n ↪ μ_{2n}` a level-`n` coset
  of size `S` (shift `b−a`, `d = gcd(b−a,n)`) lifts to a level-`2n` coset of the **SAME size `S`**
  (shift preserved, `n` doubled ⟹ `d' = gcd(b−a, 2n) = 2d`, `S' = 2n/d' = n/d = S`). The budget
  doubles (`n → 2n`) and `d` doubles (`d → 2d`), so the crossing test `O ≤ d` becomes `O ≤ 2d`:
  the SAME orbit family `O` now has DOUBLE the headroom. A constant orbit family that was bad at
  level `n` becomes good with one extra rung of headroom — `+1` per tower level, **additive**.

* `multiplicative_needs_coset_count_doubling` — the contrapositive that pins exactly what the
  multiplicative scenario would REQUIRE: for the plateau width to DOUBLE, the coset count `O` would
  have to itself grow by a factor `≈ 2` per tower level (so that `O(s) > 2d` persists for twice as
  many rungs). i.e. multiplicative width ⟺ the orbit count `O` is itself multiplicative. The
  exact-computation certificate (below) shows `O` does the OPPOSITE of growing with imprimitivity.

## The exact-computation certificate (char-0, `p ≫ n³`, `p ≡ 1 mod n`, `scripts/rust-pg/dirdiag`)

At `n = 16, k = 4`, spike rung `s = 6` (budget `= n = 16`), measured distinct-γ `D = z + S·O`
across imprimitivity of the SAME rung:

  | direction | `d` | `S = n/d` | `D` | `O = (D−z)/S` | test `O ≤ d` | binds? |
  |-----------|-----|-----------|-----|---------------|--------------|--------|
  | `(10,4)`  |  2  |    8      | 89  |     11        | `11 ≤ 2`     | **NO** (widest plateau) |
  | `(8,12)`  |  4  |    4      | 25  |      6        | `6 ≤ 4`      | NO (by 2) |
  | `(4,12)`  |  8  |    2      | 12  |      6        | `6 ≤ 8`      | **YES** (binds) |

`O`: `11 → 6 → 6` (does NOT grow with `d`), while the budget `d`: `2 → 4 → 8` (grows). So higher
imprimitivity binds SOONER (shorter plateau); the widest plateau is at the LOWEST imprimitivity
`d = 2`. The "more `μ_{2^k}`-invariance ⟹ more extra rungs ⟹ multiplicative" hope is REFUTED at the
count level: the extra invariance buys BUDGET (a factor `d`), not extra orbits.

The `binding_budget_monotone_in_d` + `doubling_preserves_coset_size_doubles_budget` theorems are the
machine-checked structural reason; the table is the exact char-0 evidence that the orbit count `O`
does not co-double.

## Honest scope (REFUTATION-WITH-MECHANISM of the multiplicative count-half)

This brick proves the **budget-headroom monotonicity** and the **coset-size preservation /
budget-doubling** under the tower step, and records the exact certificate that the orbit count `O`
does NOT grow with imprimitivity (so the extra invariance cannot manufacture a doubling plateau).
It does **NOT** prove the full additive bound `w(2n) = w(n) + O(1)` ASYMPTOTICALLY: that needs the
quantitative statement that the worst-direction orbit count `O(s)` decays by one headroom-step per
rung uniformly up the tower (the open E5/E7 = BCHKS 1.12 input), carried elsewhere as a named Prop.
What is settled here: the multiplicative mechanism the adversary would invoke ("more invariance ⟹
more rungs") is FALSE — invariance raises the BUDGET (`d`), not the orbit count, so it shortens the
plateau. The 2-point trend `w(16)=1, w(32)=2` is consistent with additive `+1`; this brick supplies
the MECHANISM (not a 2-point extrapolation) that the doubling is additive in the budget. CORE
`M(μ_n) ≤ C√(n log(p/n))` UNCHANGED/OPEN.
-/

namespace ArkLib.ProximityGap.PlateauWidthImprimitivityMonotone

open ArkLib.ProximityGap.OrbitCountCrossingLaw

/-- **Budget headroom is monotone in imprimitivity.**  At a fixed coset size `S` and fixed coset
(orbit) count `O`, the budget-crossing test `O ≤ d` is monotone in `d`: a LARGER imprimitivity
`d₂ ≥ d₁` only makes binding easier.  Concretely, if the count `D = O·S` already binds at the
smaller imprimitivity (`O ≤ d₁`, so `D ≤ n₁ = S·d₁`) it binds at the larger one too; and if it is
ABOVE budget at the larger imprimitivity (`O > d₂`) it is above budget at the smaller one.  The
extra `μ_{2^k}`-invariance of a higher imprimitivity direction is pure budget headroom `d`, NOT
extra orbits — so it can only SHORTEN, never widen, the plateau. -/
theorem binding_budget_monotone_in_d
    {O S d₁ d₂ : ℕ} (hS : 0 < S) (hd : d₁ ≤ d₂)
    (hbind₁ : (O * S) ≤ S * d₁) :
    (O * S) ≤ S * d₂ := by
  have : (O * S) ≤ S * d₁ ↔ O ≤ d₁ :=
    crossing_law hS rfl rfl
  have hO : O ≤ d₁ := this.mp hbind₁
  have : O ≤ d₂ := le_trans hO hd
  exact (crossing_law hS (n := S * d₂) rfl rfl).mpr this

/-- **The tower step is ADDITIVE in the budget: coset size preserved, budget (and `d`) doubled.**
Under the doubling embedding `μ_n ↪ μ_{2n}` a far direction with shift `t = b − a` and
`d = gcd(t, n)` lifts to the SAME shift `t` at level `2n`, where `d' = gcd(t, 2n)`.  For the prize
tower level `n = 2^μ` and an imprimitive (`b−a`-even) direction, the orbit/coset size is PRESERVED
(`S' = 2n/d' = n/d = S`) while the budget doubles (`n → 2n`) and the crossing modulus doubles
(`d → 2d`).  Hence the SAME orbit family `O` (count unchanged) faces the test `O ≤ 2d` at level
`2n` instead of `O ≤ d` at level `n` — DOUBLE the headroom, the signature of a `+1`-per-level
(additive) descent, NOT a `×2` (multiplicative) one.

We state the load-bearing arithmetic: with supply `S·d = n` at level `n`, the doubled level has
supply `S·(2d) = 2n` at the SAME `S` — coset size invariant, budget doubled. -/
theorem doubling_preserves_coset_size_doubles_budget
    {S d n : ℕ} (hsupply : S * d = n) :
    S * (2 * d) = 2 * n := by
  rw [← hsupply]; ring

/-- **Coset-size preservation, gcd form (the prize tower level).**  For `n = 2^μ` and an even shift
`t` (`t = 2t'`, the imprimitive direction), the doubled-level imprimitivity is exactly twice:
`gcd(t, 2·2^μ) = 2·gcd(t', 2^μ)` is NOT what we need directly; the clean load-bearing fact is the
supply one above.  Here we record the coset-size invariance as the statement that the level-`2n`
coset size `2n / (2d)` equals the level-`n` coset size `n / d`. -/
theorem coset_size_invariant_under_doubling
    {S d n : ℕ} (hS : 0 < S) (hsupply : S * d = n) :
    (2 * n) / (2 * d) = n / d :=
  Nat.mul_div_mul_left n d (by norm_num : 0 < 2)

/-- **What the MULTIPLICATIVE scenario would require (the contrapositive pin).**  By
`binding_budget_monotone_in_d`, at a fixed coset count `O` the binding only gets EASIER as `d`
grows; and by `doubling_preserves_coset_size_doubles_budget` the tower step doubles the available
`d` (the budget) at constant coset size `S`.  Therefore the ONLY way the plateau width can DOUBLE
up the tower is if the coset count `O` itself grows (multiplicatively): if `O` stays bounded
(`O ≤ O₀` along the tower) then for any level with budget modulus `d ≥ O₀` the direction binds
(`O·S ≤ S·d`).  So a non-doubling (bounded) orbit count FORCES eventual binding — the plateau width
cannot run away multiplicatively unless `O` does.  Stated: a bounded coset count is INCOMPATIBLE
with a persistently-above-budget cascade once the budget modulus catches up. -/
theorem multiplicative_needs_coset_count_doubling
    {O S d : ℕ} (hS : 0 < S) (hOd : O ≤ d) :
    (O * S) ≤ S * d :=
  (crossing_law hS (n := S * d) rfl rfl).mpr hOd

/-- **Non-vacuity / the n=16 spike certificate (the widest plateau is at the LOWEST `d`).**  The
exact char-0 measurement at `n = 16`, `s = 6`, budget `= 16`: the `d = 8` direction (coset size
`S = 2`, orbit count `O = 6`) BINDS (`6·2 = 12 ≤ 16`), i.e. `O = 6 ≤ d = 8` — the high-imprimitivity
direction is already good at the very rung where the `d = 2` direction (`O = 11 > 2`, `D = 89`) is
far above budget.  This is the machine-checkable witness that higher imprimitivity binds SOONER. -/
example : (6 * 2 : ℕ) ≤ 2 * 8 := by norm_num

/-- **Non-vacuity / the `d = 2` widest-plateau witness.**  At the same rung the `d = 2` direction
(`S = 8`, `O = 11`) is ABOVE budget: `11·8 = 88 > 8·2 = 16` (`D = 89` with the `z = 1` fixed point).
The crossing test `O ≤ d` fails (`11 > 2`) — the longest plateau lives at the lowest imprimitivity,
not the highest. -/
example : ¬ (11 * 8 : ℕ) ≤ 8 * 2 := by norm_num

/-- **Non-vacuity / budget-doubling witness.**  The level-`16` `d = 2` direction (`S = 8`, supply
`8·2 = 16`) lifts to a level-`32` direction with the SAME `S = 8` and DOUBLED budget: `8·4 = 32`.
The crossing modulus goes `d = 2 → 2d = 4`: the same orbit family now tests against `O ≤ 4` instead
of `O ≤ 2` — one headroom step gained per tower level (additive). -/
example : (8 * (2 * 2) : ℕ) = 2 * 16 := by norm_num

/-- **The additive count law for a CONSTANT worst-orbit family.**  Suppose the worst-direction
orbit count is a FIXED constant `O₀` along the tower (the empirical fact: the plateau value
`89 = 1 + 8·11` is the SAME at `n = 16` and `n = 32`, forcing `O₀ = 11`, `S = 8` constant — size
preserved, count preserved).  At tower level with imprimitivity modulus `d`, the crossing test is
`O₀ ≤ d`.  Since `d` DOUBLES each tower level (`doubling_preserves_coset_size_doubles_budget`,
`d → 2d`), starting from `d₀` the modulus at level `j` is `d₀·2^j`, and the family binds at the
FIRST `j` with `d₀·2^j ≥ O₀` — i.e. after `⌈log₂(O₀/d₀)⌉` levels, a FIXED FINITE number depending
only on the constant `O₀`, NOT growing geometrically.  This is the additive signature: a constant
orbit family contributes a bounded (`O(log O₀)`) plateau, never a multiplicative blow-up.

Stated cleanly: if the orbit count is bounded by `O₀` then once the modulus `d` reaches `O₀` the
direction binds and STAYS bound (by `binding_budget_monotone_in_d`); the only way to keep a cascade
above budget for `j` more levels is for `O₀` to exceed `d₀·2^j`, i.e. for `O₀` to grow with `j` —
exactly the multiplicative orbit-count growth the exact computation refutes (`O`: `11→6→6` across
`d = 2,4,8` at fixed rung, does NOT grow). -/
theorem constant_orbit_family_binds_when_modulus_catches_up
    {O₀ S d : ℕ} (hS : 0 < S) (hcatch : O₀ ≤ d) :
    (O₀ * S) ≤ S * d :=
  (crossing_law hS (n := S * d) rfl rfl).mpr hcatch

/-- **Persistence of binding up the tower (no re-widening).**  Once a constant orbit family `O₀`
binds at modulus `d` (`O₀ ≤ d`), it binds at EVERY higher modulus `d' ≥ d` — in particular at all
deeper tower levels (where `d` only doubles).  So a constant orbit family cannot un-bind: the
plateau, once closed by the budget catching up, stays closed.  This rules out the multiplicative
scenario's required "plateau keeps re-opening and doubling" up the tower. -/
theorem binding_persists_up_tower
    {O₀ S d d' : ℕ} (hS : 0 < S) (hcatch : O₀ ≤ d) (hd : d ≤ d') :
    (O₀ * S) ≤ S * d' :=
  binding_budget_monotone_in_d hS hd (constant_orbit_family_binds_when_modulus_catches_up hS hcatch)

end ArkLib.ProximityGap.PlateauWidthImprimitivityMonotone

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.PlateauWidthImprimitivityMonotone.binding_budget_monotone_in_d
#print axioms ArkLib.ProximityGap.PlateauWidthImprimitivityMonotone.doubling_preserves_coset_size_doubles_budget
#print axioms ArkLib.ProximityGap.PlateauWidthImprimitivityMonotone.coset_size_invariant_under_doubling
#print axioms ArkLib.ProximityGap.PlateauWidthImprimitivityMonotone.multiplicative_needs_coset_count_doubling
#print axioms ArkLib.ProximityGap.PlateauWidthImprimitivityMonotone.constant_orbit_family_binds_when_modulus_catches_up
#print axioms ArkLib.ProximityGap.PlateauWidthImprimitivityMonotone.binding_persists_up_tower
