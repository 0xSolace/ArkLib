/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.RingTheory.Polynomial.Cyclotomic.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# The prize-regime (split) weight-3 spurious collision: `Spur_2(17) ≥ 1` in `F_17` (Issue #444)

Companion / prize-regime upgrade of `SpurWeightThreeCollision` (`8fadf6eb1`, the `p = 3`, `m = 3`
witness). That witness proved the p-divisibility tower does not collapse above weight 2, but at a
**non-split** prime: `p = 3 ∤ 2^3 − 1 = 7`, so `μ_8` embeds only in `F_9`, not the prime field `F_3`.
The prize regime is the **split** case `p ≡ 1 mod n` (`q·ε* ≈ n`), where the primitive `n`-th root
`g` lives in the prime field `F_p` itself and only in-`F_p` vanishings contribute to the char-`p`
energy `E_r`. We give the smallest prize-faithful witness.

## The split witness (`m = 4`, `n = 16`, `p = 17`)

`p = 17 ≡ 1 mod 16` is **split** (`16 ∣ 17 − 1`), so `F_17` contains a primitive `16`-th root of
unity — concretely `g = 3` (`3^16 = 1`, `3^8 = −1`, so `ord(3) = 16`). The weight-3 antipodal-free
relation `1 + ζ + ζ⁴` (exponent set `{0,1,4}`, no two differing by `2^{m−1} = 8`) **vanishes at `g`**:

> **`1 + 3 + 3⁴ = 0` in `F_17`**   (and `3⁸ + 1 = 0`, i.e. `g` is a root of `Φ_16 = X⁸ + 1`).

So `Φ_16` and `1 + X + X⁴` share the root `g = 3` in `F_17`: they are NOT coprime in `F_17[X]`, the
prize prime `17` divides `N(1 + ζ + ζ⁴)`, and **the spurious vanishing happens in the prime field**
(`g ∈ F_17`) — a genuine prize-regime spurious collision. Hence `Spur_2(17) ≥ 1` in the split regime.

## Deconfliction with the `p ≡ 3 mod 4` Chebotarev exclusion (`baacb5c69`)

`SpurBadPrimeChebotarev.spur_field_excludes_three_mod_four` shows no `p ≡ 3 mod 4` prime carries `μ_{2^m}`
in the **prime field** `ZMod p` (`−1` is not a square there), so the in-`F_p` spurious set is empty for
that class. The non-split `p = 3` witness (`SpurWeightThreeCollision`) is consistent: `3 ≡ 3 mod 4`, its
collision lives in `F_9` (not `F_3`), and contributes to char-`3` energy only off the prime field. THIS
witness is in the **surviving** class: `17 ≡ 1 mod 4` (and `≡ 1 mod 16`), exactly where the Chebotarev
exclusion leaves the bad-prime set non-empty and the open BCHKS-1.12 wall lives. So the two results
compose cleanly: the `≡ 3 mod 4` half-class is excluded from the in-field support, and `p = 17` exhibits
a concrete surviving (`≡ 1 mod 4`, split) prime where the in-`F_p` spurious count is genuinely `≥ 1`.

## Results (axiom-clean)

* `three_primitive_root_16`   : `g = 3` is a primitive `16`-th root of unity in `F_17` (`3^16 = 1`,
    `3^8 = −1`).
* `phi16_zmod17`              : `Φ_16 = X⁸ + 1` over `F_17`.
* `g_isRoot_phi16`            : `g = 3` is a root of `Φ_16` in `F_17`.
* `g_isRoot_relation`         : `g = 3` is a root of the weight-3 relation `1 + X + X⁴` in `F_17`
    (`1 + 3 + 3⁴ = 0`).
* `split_weight3_not_coprime_mod17` : **THE PRIZE-REGIME WALL RUNG** — `Φ_16` and `1 + X + X⁴` are NOT
    coprime in `F_17[X]` (shared root `g = 3 ∈ F_17`). The split prime `17 ≡ 1 mod 16` divides
    `N(1+ζ+ζ⁴)` and the spurious vanishing is IN THE PRIME FIELD — a genuine prize-regime collision,
    so `Spur_2(17) ≥ 1`.

## Honest scope (rules 1, 3, 6)

NOT a CORE closure. It is the prize-regime-faithful upgrade of the `p = 3` witness: a concrete SPLIT
prime `p ≡ 1 mod n` (so `g ∈ F_p`, the genuine prize regime) at which the in-field spurious-collision
count is `≥ 1`, landing in the surviving `≡ 1 mod 4` Chebotarev class. Together with the weight-2 base
(`Spur = 0` at all odd `p`) and the `≡ 3 mod 4` exclusion, it pins the wall to: **weight `≥ 3`,
`p ≡ 1 mod 4`, split** — the count `Spur_r(p)` at depth `r ≈ log q` in exactly that class. Thinness-
essential in the same mild sense (it is the `16 ∣ 17−1`, `μ_16 ⊆ F_17` prime-power-2 split fact). CORE
(`M(μ_n) ≤ C·√(n·log(p/n))`) stays OPEN.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
- `SpurWeightThreeCollision.lean` (`8fadf6eb1`, non-split `p=3`); `SpurBadPrimeChebotarev.lean`
  (`baacb5c69`, `≡ 3 mod 4` exclusion); `ShortRelationNormBase.lean` (`a823e4658`, weight-2 base).
- Probe: `scripts/probes/probe_spur_split_prize_regime.py`.
-/

open Polynomial

namespace ArkLib.ProximityGap.SpurSplitSeventeen

/-- **`g = 3` is a primitive `16`-th root of unity in `F_17`** (`3^16 = 1`, `3^8 = −1 ≠ 1`), so its
order is exactly `16 = 2^4`. Since `17 ≡ 1 mod 16` is SPLIT, `μ_16` lives in the prime field `F_17` —
the genuine prize regime (`g ∈ F_p`, not just `F̄_p`). -/
theorem three_primitive_root_16 : (3 : ZMod 17) ^ 16 = 1 ∧ (3 : ZMod 17) ^ 8 = -1 := by
  refine ⟨by decide, by decide⟩

/-- **`Φ_16 = X⁸ + 1` over `F_17`.** The `2^m`-th cyclotomic polynomial is `X^{2^{m−1}} + 1`; `m = 4`
gives `X⁸ + 1`. -/
theorem phi16_zmod17 : cyclotomic (2 ^ 4) (ZMod 17) = X ^ 8 + 1 := by
  have h : (2 : ℕ) ^ 4 = 2 ^ ((4 - 1) + 1) := by norm_num
  rw [h, cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
  rw [Finset.sum_range_succ, Finset.sum_range_one]
  simp [add_comm]

/-- **`g = 3` is a root of `Φ_16` in `F_17`** (`3⁸ + 1 = 0`): the primitive `16`-th root annihilates the
cyclotomic polynomial. -/
theorem g_isRoot_phi16 : (cyclotomic (2 ^ 4) (ZMod 17)).IsRoot 3 := by
  rw [phi16_zmod17]
  simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_one]
  decide

/-- **`g = 3` is a root of the weight-3 antipodal-free relation `1 + X + X⁴` in `F_17`**
(`1 + 3 + 3⁴ = 0`). The exponent set `{0,1,4}` is antipodal-free (no two differ by `2^{m−1} = 8`); over
`ℂ` the sum `1 + ζ + ζ⁴ ≠ 0`. -/
theorem g_isRoot_relation : (1 + X + X ^ 4 : (ZMod 17)[X]).IsRoot 3 := by
  simp only [IsRoot.def, eval_add, eval_pow, eval_X, eval_one]
  decide

/-- The relation polynomial `1 + X + X⁴` is nonzero over `F_17` (so the shared root is a genuine
non-coprimality, not a vacuous `0`-polynomial). -/
theorem relation_ne_zero : (1 + X + X ^ 4 : (ZMod 17)[X]) ≠ 0 := by
  intro h
  have hc := congrArg (fun p => Polynomial.coeff p 4) h
  simp only [coeff_add, coeff_one, coeff_X, coeff_X_pow, coeff_zero] at hc
  exact absurd hc (by decide)

/-- `3` is prime, so `F_17` is a field with the divisibility / coprimality machinery. -/
local instance fact17 : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- **THE PRIZE-REGIME WALL RUNG: `Φ_16` and the weight-3 antipodal-free relation `1 + X + X⁴` are NOT
coprime over `F_17`** — they share the root `g = 3` IN THE PRIME FIELD. The split prize prime
`17 ≡ 1 mod 16` divides `N(1 + ζ + ζ⁴)` and the spurious vanishing `1 + g + g⁴ = 0` happens in `F_17`
itself (not merely `F̄_17`), a genuine prize-regime spurious collision. Hence `Spur_2(17) ≥ 1` in the
split regime, in the surviving `≡ 1 mod 4` Chebotarev class — exactly where the open BCHKS-1.12 wall
lives. -/
theorem split_weight3_not_coprime_mod17 :
    ¬ IsCoprime (cyclotomic (2 ^ 4) (ZMod 17)) (1 + X + X ^ 4 : (ZMod 17)[X]) := by
  intro hcop
  -- a common root contradicts coprimality: evaluate the Bezout identity at g = 3.
  obtain ⟨u, v, huv⟩ := hcop
  have heval := congrArg (fun p => Polynomial.eval (3 : ZMod 17) p) huv
  -- evaluate the Bezout identity at the common root g = 3: both factors vanish, so 0 = 1.
  have hphi : Polynomial.eval (3 : ZMod 17) (cyclotomic (2 ^ 4) (ZMod 17)) = 0 := g_isRoot_phi16
  have hrel : Polynomial.eval (3 : ZMod 17) (1 + X + X ^ 4 : (ZMod 17)[X]) = 0 := g_isRoot_relation
  simp only [eval_add, eval_mul, eval_one] at heval
  rw [show (eval (3:ZMod 17) X) = 3 from eval_X,
      show (eval (3:ZMod 17) (X^4)) = 3^4 by simp] at heval
  -- heval : eval 3 u * eval 3 (Φ_16) + eval 3 v * (1 + 3 + 3^4) = 1
  rw [show (1 + (3:ZMod 17) + 3^4) = 0 by decide] at heval
  rw [show eval (3:ZMod 17) (cyclotomic (2^4) (ZMod 17)) = 0 from hphi] at heval
  simp at heval

end ArkLib.ProximityGap.SpurSplitSeventeen

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.SpurSplitSeventeen.three_primitive_root_16
#print axioms ArkLib.ProximityGap.SpurSplitSeventeen.g_isRoot_phi16
#print axioms ArkLib.ProximityGap.SpurSplitSeventeen.g_isRoot_relation
#print axioms ArkLib.ProximityGap.SpurSplitSeventeen.split_weight3_not_coprime_mod17
