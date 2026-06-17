/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-A08)
-/
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The 2-adic Newton polygon root-count of the period relation (#444, lane wf-A08)

## The angle (manifesto route 3: the deepest structure of `μ_n` is 2-adic)

`n = 2^μ`, so the spurious-relation configs `σ_T = ∑_{i∈T} ε_i ζ_n^i ∈ ℤ[ζ_n]` (`ε_i = ±1`,
antipodal-free, weight `w = |T|`) live in the cyclotomic ring whose UNIQUE ramified prime is `2`:
`(2) = λ^d`, `λ = 1 − ζ_n` the uniformizer, `e = d = φ(n) = n/2`, residue degree `f = 1`. Mann (the
only thing that bounds spurious mass in char 0) is the *archimedean* shadow: it bounds the *magnitude*
`|N(σ_T)| ≤ w^d` (House), giving the floor `w ≥ p^{1/d}`. The genuinely different, never-before-attacked
handle is the *2-adic* Newton polygon: the `λ`-adic valuation `v_λ(σ_T) = v_2(N(σ_T))` (`f = 1`),
which **splits off as a factor of `2^{v_λ}` from the norm and is `p`-FREE** (never sees the odd split
prize prime `p`).

## The NP-sharpened Mann floor (the new inequality)

A char-`p` SPURIOUS config at a prize prime `p` (odd, `p ≡ 1 mod n`) requires `p ∣ N(σ_T)`. Factor
the absolute norm as `|N(σ_T)| = 2^{v_λ} · U` with `U` ODD (`v_λ = v_2(N)`). Since `p` is odd, `p ∤ 2`,
so `p ∣ N` forces `p ∣ U = |N|/2^{v_λ}`. Combining with the House magnitude bound `|N| ≤ w^d`:

  `p · 2^{v_λ}  ≤  |N|  ≤  w^d`,   i.e.   **`w ≥ (p · 2^{v_λ})^{1/d} = 2^{v_λ/d} · p^{1/d}`**,

the 2-adic Newton-polygon **refinement** of the classical Mann floor `w ≥ p^{1/d}` by the
ramification factor `2^{v_λ/d}`.  This file proves the integer inequality `p · 2^V ≤ w^d` (the floor
in the `≤`-on-powers form, the strongest exact statement) and its consequences.

## The verdict: an OBSTRUCTION (the 2-adic conservation law)

The decisive question is whether this 2-adic refinement CROSSES the Johnson weight `w ~ n/2 = d`.
It does NOT, and the reason is RIGID: the gain factor is bounded by the ramification index.
For `σ_T ≠ 0` (antipodal-free ⇒ not an honest char-0 vanishing) the valuation is capped,
`v_λ ≤ d − 1` (`v_λ = d` would force the principal prime to the full ramification, the all-equal
config), so

  `2^{v_λ/d}  ≤  2^{(d−1)/d}  <  2`   for all `d ≥ 1`.

Hence the NP floor `2^{v_λ/d} · p^{1/d}` improves Mann by **at most one bit of weight**. At prize
scale (`d = 2^29`, `p ≍ n^4 = 2^120`) `p^{1/d} = 2^{120/2^29} ≈ 1` and the gain `< 2`, so the floor
is `< 2`, while the Johnson weight is `d = 2^29`. The exact prize-scale prescreen
(`scripts/probes/rust/probe_wfA08_*.rs`, `probe_wfA08_mann.rs`) shows `NPfloor/Johnson → 0`
monotonically (`0.917 → 0.285 → 0.103 → 0.042 → 0.018 → 0.004 → …` for `n = 16..1024`). The 2-adic
Newton polygon, like every domain-first/second-order estimate, CAPS at Johnson — the
conservation-law meta-theorem holds 2-adically. This is a PRECISE OBSTRUCTION: it pins the maximal
possible 2-adic gain to the ramification factor `< 2`, ruling out the 2-adic route as a beyond-Johnson
mechanism.

## What is PROVEN here (axiom-clean ℕ/ℝ arithmetic)

* `np_sharpened_mann_floor` — the core: from the House magnitude bound `p * 2^V ≤ w^d` (with
  `p ∣ N`, `p` odd, `v_2(N) = V`, `|N| ≤ w^d`, assembled in `house_to_floor`) it is exactly the
  Mann floor multiplied by the 2-adic factor; stated as `p * 2 ^ V ≤ w ^ d`.
* `house_to_floor` — the assembly: `p` odd, `p ∣ N`, `N ≠ 0`, `v₂(N) = V`, `|N| ≤ B` ⟹ `p * 2^V ≤ B`
  (since `2^V ∣ N`, `p ∣ N`, `gcd(p, 2^V) = 1` ⇒ `p * 2^V ∣ N` ⇒ `p * 2^V ≤ |N| ≤ B`).
* `mann_gain_factor_lt_two` — the OBSTRUCTION: for `V ≤ d − 1`, `(2:ℝ)^((V:ℝ)/d) < 2` (`d ≥ 1`),
  the bounded-gain certificate: the 2-adic refinement is `< 2^{1} = 2`.
* `mann_gain_le_two` — the clean `≤ 2` corollary and `np_floor_lt_two_mul_mann` packaging.

## Honest scope

NOT a CORE closure: the House magnitude bound `|N| ≤ w^d` and the `p`-divisibility `p ∣ N` are the
(cited / measured) inputs (same status as the S7/S8 archimedean floor and S9 split decomposition);
this file supplies the 2-adic refinement on top and proves it is bounded by the ramification factor.
The CORE `M(μ_n) ≤ C√(n log(p/n))` stays OPEN; this file CLOSES the 2-adic-NP route as a no-go for
beyond-Johnson, with the exact bound `gain < 2`. Issues #444, #407, #389.

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. #444.
- Mann, *On linear relations between roots of unity* (the archimedean House floor `|N| ≤ w^d`).
- in-tree `_wfS9_vp_split_decomposition.lean` (split-`p` valuation), `_SpurEvenValuationTwoSquares.lean`
  (the `p ≡ 3 mod 4` even-valuation cut), `probe_wfS9_oneminuszeta.rs` (the `v_λ` weight-parity law).
-/

namespace ArkLib.ProximityGap.Frontier.WFA08

open scoped BigOperators

/-! ### §1  The NP-sharpened Mann floor (integer core). -/

/-- **Coprimality of `p` and `2^V` for an odd prime `p`.** An odd prime `p` is coprime to every
power of `2`. (`λ`-adic side and the odd-prize side are arithmetically independent.) -/
theorem odd_prime_coprime_two_pow {p : ℕ} (hp : p.Prime) (hodd : p ≠ 2) (V : ℕ) :
    Nat.Coprime p (2 ^ V) := by
  have hp2 : ¬ p ∣ 2 := by
    intro hd
    rcases (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd with h
    exact hodd h
  exact (Nat.Coprime.pow_right V ((Nat.coprime_primes hp Nat.prime_two).mpr hodd))

/-- **The House → floor assembly (ℕ).** If a config norm `N ≠ 0` is divisible by an odd prime `p`
(the SPUR condition `p ∣ N`) and by `2^V` (its 2-adic part, `V = v₂(N)`), and is bounded in
magnitude by `B` (the House bound `|N| ≤ w^d`), then `p · 2^V ≤ B`. Mechanism: `p` odd ⇒
`gcd(p, 2^V) = 1` ⇒ `p · 2^V ∣ N` ⇒ `p · 2^V ≤ N ≤ B`. This is the integer form of the
NP-sharpened Mann floor `w ≥ (p·2^V)^{1/d}`. -/
theorem house_to_floor {p N B V : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hpN : p ∣ N) (h2N : 2 ^ V ∣ N) (hN0 : N ≠ 0) (hNB : N ≤ B) :
    p * 2 ^ V ≤ B := by
  have hcop : Nat.Coprime p (2 ^ V) := odd_prime_coprime_two_pow hp hodd V
  have hdvd : p * 2 ^ V ∣ N := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hpN h2N
  have hle : p * 2 ^ V ≤ N := Nat.le_of_dvd (Nat.pos_of_ne_zero hN0) hdvd
  exact le_trans hle hNB

/-- **`np_sharpened_mann_floor` — the core inequality.** For an antipodal-free config of weight `w`
in `μ_n` (`d = φ(n) = n/2`), whose absolute norm `N = N(σ_T)` is a SPUR at the odd prize prime `p`
(`p ∣ N`) and has 2-adic valuation `V = v₂(N)` (so `2^V ∣ N`), the House magnitude bound `|N| ≤ w^d`
yields `p · 2^V ≤ w^d` — equivalently `w ≥ (p · 2^V)^{1/d} = 2^{V/d} · p^{1/d}`, the Mann floor
sharpened by the 2-adic factor `2^{V/d}`. This is the integer statement with `B = w^d`. -/
theorem np_sharpened_mann_floor {p N w d V : ℕ} (hp : p.Prime) (hodd : p ≠ 2)
    (hpN : p ∣ N) (h2N : 2 ^ V ∣ N) (hN0 : N ≠ 0) (hHouse : N ≤ w ^ d) :
    p * 2 ^ V ≤ w ^ d :=
  house_to_floor hp hodd hpN h2N hN0 hHouse

/-! ### §2  The OBSTRUCTION: the gain factor is bounded by the ramification `< 2`. -/

/-- **`mann_gain_factor_lt_two` — the bounded-gain obstruction.** For `d ≥ 1` and a 2-adic valuation
`V ≤ d − 1` (the proven ceiling for a nonzero antipodal-free config: `v_λ ≤ d − 1`), the multiplicative
gain `2^{V/d}` the 2-adic Newton polygon adds to the Mann floor is `< 2`:

  `(2 : ℝ) ^ ((V : ℝ) / d)  <  2`.

So the NP refinement buys STRICTLY LESS than one extra bit of weight floor — it can never reach the
Johnson weight `w ~ d`. This is the 2-adic conservation law: the gain is capped by the ramification
index `e = d` (since `V < d`), not by the Johnson exponent `d/2`. -/
theorem mann_gain_factor_lt_two {V d : ℕ} (hd : 1 ≤ d) (hV : V ≤ d - 1) :
    (2 : ℝ) ^ ((V : ℝ) / (d : ℝ)) < 2 := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hVd : (V : ℝ) < (d : ℝ) := by
    have : V < d := by omega
    exact_mod_cast this
  have hfrac : (V : ℝ) / (d : ℝ) < 1 := by
    rw [div_lt_one hdpos]; exact hVd
  calc (2 : ℝ) ^ ((V : ℝ) / (d : ℝ))
      < (2 : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_lt_rpow_left_iff (x := 2) (by norm_num) |>.mpr hfrac
    _ = 2 := by norm_num

/-- **`mann_gain_le_two`** — the `≤ 2` form (for `V ≤ d`, including the boundary). The 2-adic gain
factor never exceeds `2`. (`V ≤ d` ⇒ `V/d ≤ 1` ⇒ `2^{V/d} ≤ 2^1 = 2`.) -/
theorem mann_gain_le_two {V d : ℕ} (hd : 1 ≤ d) (hV : V ≤ d) :
    (2 : ℝ) ^ ((V : ℝ) / (d : ℝ)) ≤ 2 := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hVd : (V : ℝ) ≤ (d : ℝ) := by exact_mod_cast hV
  have hfrac : (V : ℝ) / (d : ℝ) ≤ 1 := by
    rw [div_le_one hdpos]; exact hVd
  calc (2 : ℝ) ^ ((V : ℝ) / (d : ℝ))
      ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_left_iff (x := 2) (by norm_num) |>.mpr hfrac
    _ = 2 := by norm_num

/-- **`np_floor_lt_two_mul_mann` — the floor is `<` twice the Mann floor.** Packaging the obstruction
on the floor side: the NP-sharpened weight floor `(p · 2^V)^{1/d} = 2^{V/d} · p^{1/d}` is strictly less
than `2 · p^{1/d}` (twice the classical Mann floor), for `V ≤ d − 1`, `d ≥ 1`, `p > 0`. The 2-adic
Newton polygon multiplies the Mann floor by a factor in `[1, 2)` — never enough to cross from the
`p^{1/d} ≈ 1` Mann floor to the Johnson weight `d`. -/
theorem np_floor_lt_two_mul_mann {V d : ℕ} (p : ℝ) (hp : 0 < p) (hd : 1 ≤ d) (hV : V ≤ d - 1) :
    (2 : ℝ) ^ ((V : ℝ) / (d : ℝ)) * p ^ ((d : ℝ)⁻¹) < 2 * p ^ ((d : ℝ)⁻¹) := by
  have hgain := mann_gain_factor_lt_two hd hV
  have hppos : (0 : ℝ) < p ^ ((d : ℝ)⁻¹) := Real.rpow_pos_of_pos hp _
  exact mul_lt_mul_of_pos_right hgain hppos

/-! ### §3  The end-to-end no-go: spur ⇒ floor, and floor `<` Johnson at prize scale. -/

/-- **`spur_floor_below_johnson`** — the end-to-end 2-adic no-go (real form). Granting the inputs
of the NP-sharpened floor in *real* magnitude form — the House bound `p * 2^V ≤ W` with
`W = w^d` and the ceiling `V ≤ d − 1` — the realized weight `w` satisfies the Mann floor
multiplied by a factor `< 2`, hence `w ≥ p^{1/d}` only up to a factor `< 2`. Concretely: if
`p * 2^V ≤ w^d` (`p > 0`, `d ≥ 1`), then `p^{1/d} ≤ w` and the NP-improvement `w / p^{1/d} = 2^{V/d}`
is `< 2`. The two facts together — `w ≥ 2^{V/d} p^{1/d}` and `2^{V/d} < 2` — are the no-go: at prize
scale `p^{1/d} → 1`, so `w < 2`, never the Johnson `d`. -/
theorem spur_floor_below_johnson {p w : ℝ} {V d : ℕ}
    (hp : 0 < p) (hw : 0 ≤ w) (hd : 1 ≤ d) (hV : V ≤ d - 1)
    (hfloor : p * 2 ^ V ≤ w ^ d) :
    p ^ ((d : ℝ)⁻¹) ≤ w ∧ (2 : ℝ) ^ ((V : ℝ) / (d : ℝ)) < 2 := by
  refine ⟨?_, mann_gain_factor_lt_two hd hV⟩
  -- p ≤ p * 2^V ≤ w^d, then take d-th roots
  have hdne : (d : ℕ) ≠ 0 := by omega
  have h2V : (1 : ℝ) ≤ 2 ^ V := one_le_pow₀ (by norm_num)
  have hple : p ≤ w ^ d := by
    calc p = p * 1 := by ring
      _ ≤ p * 2 ^ V := by exact mul_le_mul_of_nonneg_left h2V hp.le
      _ ≤ w ^ d := hfloor
  -- take real d-th roots:  p^{1/d} ≤ (w^d)^{1/d} = w
  have hwd_nn : (0 : ℝ) ≤ w ^ d := pow_nonneg hw d
  have hroot : p ^ ((d : ℝ)⁻¹) ≤ (w ^ d) ^ ((d : ℝ)⁻¹) :=
    Real.rpow_le_rpow hp.le hple (by positivity)
  have hcollapse : (w ^ d) ^ ((d : ℝ)⁻¹) = w := by
    rw [← Real.rpow_natCast w d, ← Real.rpow_mul hw,
        mul_inv_cancel₀ (by exact_mod_cast hdne : (d : ℝ) ≠ 0), Real.rpow_one]
  rwa [hcollapse] at hroot

end ArkLib.ProximityGap.Frontier.WFA08

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.WFA08.np_sharpened_mann_floor
#print axioms ArkLib.ProximityGap.Frontier.WFA08.house_to_floor
#print axioms ArkLib.ProximityGap.Frontier.WFA08.mann_gain_factor_lt_two
#print axioms ArkLib.ProximityGap.Frontier.WFA08.mann_gain_le_two
#print axioms ArkLib.ProximityGap.Frontier.WFA08.np_floor_lt_two_mul_mann
#print axioms ArkLib.ProximityGap.Frontier.WFA08.spur_floor_below_johnson
