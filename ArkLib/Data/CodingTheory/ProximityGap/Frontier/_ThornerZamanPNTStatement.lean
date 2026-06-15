/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import Mathlib.Data.Nat.Totient

/-!
# [TZ24] refined PNT in arithmetic progressions: the literature statement + reduction (#334)

The in-tree [KKH26] polynomial-field ceiling (`KKH26PolyFieldCeiling.lean`,
`kkh26_mcaDeltaStar_le_of_TZ`) consumes the single analytic hypothesis

  `TZPrimeSupply n β supply : Prop := supply ≤ (tzWindow n β).card`

(`KKH26ThornerZaman.lean`) — "the window `[n^β, 2·n^β]` contains at least `supply` primes
`p ≡ 1 (mod n)`".  As phrased, this is a *raw cardinality* of the prime window; it is the
prize-regime instance of the **prime-counting function in an arithmetic progression**.  On
paper it is instantiated by **[TZ24]** (J. Thorner, A. Zaman, *Refinements to the prime
number theorem in arithmetic progressions*), whose Corollary 3.1 — applied via partial
summation to the short interval `[n^β, 2·n^β]` for the smooth modulus `n = 2^μ·m` — gives the
**effective density lower bound**

  `π(2·n^β; n, 1) − π(n^β; n, 1)  ≥  (1 − ε) · n^β / (φ(n) · log(n^β))`,           (TZ)

with an explicit, effective error term `ε = ε(n, β) = o(1)`, valid unconditionally for every
fixed `β > 12/5` (and for every `β > 1` under Montgomery's conjecture).  Here
`π(x; n, 1) = #{p ≤ x : p prime, p ≡ 1 (mod n)}` is the prime-counting function in the
progression `1 (mod n)`.

This file **grounds the in-tree hypothesis in the actual paper's statement**.  Following the
task's branch (3) — the in-tree `TZPrimeSupply` is already essentially the PNT count, so the
faithful move is to formalize the *sharper* explicit-density form `(TZ)` that [TZ24] proves,
and prove that the in-tree raw-cardinality hypothesis **follows from it**:

* `ThornerZamanPNT n β ε : Prop` — the literature statement `(TZ)`: the window
  `[n^β, 2·n^β]` of primes `≡ 1 (mod n)` has cardinality at least the TZ density expression
  `(1 − ε) · n^β / (φ(n) · log(n^β))`.  A pure `Prop`; **no axioms**; cited to [TZ24] Cor 3.1.
  The deep analytic proof (log-free zero-density / Linnik–Heath-Brown machinery for Dirichlet
  `L`-functions) is **not** formalized here — it stays this named `Prop`, exactly as the
  `Hab25Johnson` / `TZPrimeSupply` pattern prescribes.
* `tzDensityLB n β ε` — the TZ density expression `(1 − ε) · n^β / (φ(n) · log(n^β))` named
  once, so both the statement and the reduction speak of the same quantity.
* `tzPrimeSupply_of_thornerZamanPNT` — **the PROVEN reduction** (this is the genuinely
  elementary step): given the literature density bound `ThornerZamanPNT n β ε` and the
  arithmetic fact that `supply` does not exceed the density expression, the in-tree
  `TZPrimeSupply n β supply` holds.  This is the "deriving the integer supply count from the
  PNT-in-AP lower bound" arithmetic — real numbers down to a cardinality `≥ supply`.
* `tzPrimeSupply_of_thornerZamanPNT_natFloor` — the same with the `supply`-vs-density side
  condition discharged from a clean natural-number floor hypothesis `supply ≤ ⌊tzDensityLB⌋`.

**What is proven vs. what stays named (honesty).**  PROVEN, axiom-clean: the reduction
`ThornerZamanPNT → TZPrimeSupply` (the elementary real-bound ⇒ cardinality step) and its
floor variant.  NAMED-OPEN, never an axiom: `ThornerZamanPNT` itself — the deep analytic
[TZ24] theorem `(TZ)`.  We do **not** prove it, `sorry` it, or claim it.

## References

* [TZ24] J. Thorner, A. Zaman, *Refinements to the prime number theorem in arithmetic
  progressions*, Corollary 3.1.  (The effective log-free lower bound `(TZ)`.)
* [KKH26] D. Krachun, S. Kazanin, U. Haböck, *Failure of proximity gaps close to capacity*,
  ePrint 2026/782, Lemma 2 (the consumer of the supply).  Issue #334.
-/

open Finset
open scoped Nat

namespace ProximityGap.Frontier.ThornerZamanPNTStatement

open ArkLib.ProximityGap.KKH26 (tzWindow mem_tzWindow TZPrimeSupply)

/-- The **[TZ24] density expression** `(1 − ε) · n^β / (φ(n) · log(n^β))` — the explicit,
effective lower bound that Thorner–Zaman's refined PNT in arithmetic progressions gives for
the count of primes `p ≡ 1 (mod n)` in the short interval `[n^β, 2·n^β]` (Cor 3.1, via partial
summation over the interval).  `ε = ε(n, β) = o(1)` is the explicit TZ error term.

Named once so the literature statement `ThornerZamanPNT` and the reduction
`tzPrimeSupply_of_thornerZamanPNT` refer to the same quantity. -/
noncomputable def tzDensityLB (n : ℕ) (β ε : ℝ) : ℝ :=
  (1 - ε) * (n : ℝ) ^ β / ((Nat.totient n : ℝ) * Real.log ((n : ℝ) ^ β))

/-- **The named [TZ24] literature statement** `(TZ)` (`Hab25Johnson` named-hypothesis pattern;
**never an axiom**).  `ThornerZamanPNT n β ε` asserts the *effective density lower bound* that
Thorner–Zaman's refined prime number theorem in arithmetic progressions (Corollary 3.1 of
[TZ24], applied via partial summation to the short interval `[n^β, 2·n^β]`) gives: the window
`[n^β, 2·n^β]` of primes `p ≡ 1 (mod n)` has cardinality at least the density expression
`tzDensityLB n β ε = (1 − ε) · n^β / (φ(n) · log(n^β))`.

On paper this holds unconditionally for every fixed `β > 12/5` with an explicit error term
`ε = o(1)` (and for every `β > 1` under Montgomery's conjecture).  The deep analytic proof
(log-free zero-density / Linnik–Heath-Brown estimates for Dirichlet `L`-functions) is far
beyond present-day formalization; following the project convention it lives as this `Prop`,
consumed elsewhere by an explicit hypothesis — it is **not** an `axiom` and is **not** proven
in this file. -/
def ThornerZamanPNT (n : ℕ) (β ε : ℝ) : Prop :=
  tzDensityLB n β ε ≤ ((tzWindow n β).card : ℝ)

/-- **The PROVEN reduction** `[TZ24] density bound ⇒ in-tree supply hypothesis` (the genuinely
elementary step).  Given the named literature bound `ThornerZamanPNT n β ε` (the deep analytic
input) and the arithmetic fact that the requested `supply` does not exceed the [TZ24] density
expression `tzDensityLB n β ε`, the in-tree named hypothesis `TZPrimeSupply n β supply`
consumed by `kkh26_mcaDeltaStar_le_of_TZ` holds.

This is exactly the "derive the integer supply count from the PNT-in-AP lower bound"
arithmetic: chain `supply ≤ tzDensityLB ≤ #window` over `ℝ`, then descend to `ℕ`.  The deep
analytic content stays packaged in the hypothesis `hTZ`. -/
theorem tzPrimeSupply_of_thornerZamanPNT {n : ℕ} {β ε : ℝ} {supply : ℕ}
    (hTZ : ThornerZamanPNT n β ε) (hsupply : (supply : ℝ) ≤ tzDensityLB n β ε) :
    TZPrimeSupply n β supply := by
  refine ⟨?_⟩
  -- `supply ≤ tzDensityLB ≤ #window` over `ℝ`, then cast down to `ℕ`.
  have hreal : (supply : ℝ) ≤ ((tzWindow n β).card : ℝ) := hsupply.trans hTZ
  exact_mod_cast hreal

/-- **The reduction in clean natural-number form.**  If `supply` is bounded by the *floor* of
the [TZ24] density expression `⌊tzDensityLB n β ε⌋₊`, then the literature bound
`ThornerZamanPNT n β ε` yields `TZPrimeSupply n β supply`.  (The floor side condition is what a
caller actually checks — a concrete integer comparison — without manipulating the real
density expression directly.) -/
theorem tzPrimeSupply_of_thornerZamanPNT_natFloor {n : ℕ} {β ε : ℝ} {supply : ℕ}
    (hTZ : ThornerZamanPNT n β ε) (hpos : 0 ≤ tzDensityLB n β ε)
    (hsupply : supply ≤ ⌊tzDensityLB n β ε⌋₊) :
    TZPrimeSupply n β supply := by
  refine tzPrimeSupply_of_thornerZamanPNT hTZ ?_
  calc (supply : ℝ) ≤ (⌊tzDensityLB n β ε⌋₊ : ℝ) := by exact_mod_cast hsupply
    _ ≤ tzDensityLB n β ε := Nat.floor_le hpos

/-- **Soundness sanity check of the literature statement.**  `ThornerZamanPNT n β ε` always
delivers *something* nonnegative-or-better through the reduction: with `supply = 0` the
hypothesis is consumed vacuously, confirming the reduction is well-typed and non-degenerate
(the real content is in the side condition `supply ≤ tzDensityLB`). -/
theorem tzPrimeSupply_zero_of_thornerZamanPNT {n : ℕ} {β ε : ℝ}
    (hTZ : ThornerZamanPNT n β ε) (hpos : 0 ≤ tzDensityLB n β ε) :
    TZPrimeSupply n β 0 :=
  tzPrimeSupply_of_thornerZamanPNT hTZ (by simpa using hpos)

end ProximityGap.Frontier.ThornerZamanPNTStatement

/-! ## Axiom audit (expected: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`) -/
#print axioms ProximityGap.Frontier.ThornerZamanPNTStatement.tzPrimeSupply_of_thornerZamanPNT
#print axioms ProximityGap.Frontier.ThornerZamanPNTStatement.tzPrimeSupply_of_thornerZamanPNT_natFloor
#print axioms ProximityGap.Frontier.ThornerZamanPNTStatement.tzPrimeSupply_zero_of_thornerZamanPNT
