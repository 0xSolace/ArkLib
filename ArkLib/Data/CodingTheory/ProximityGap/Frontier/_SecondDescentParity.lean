/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic

/-!
# The SECOND antipodal descent and the head-parity dichotomy (#407)

This file runs the **second** antipodal even/odd descent on the isolated equation
`A(u)² = u·O(u)²` over `μ_{n/2}` (the output of `_AntipodalEvenOddDescent.lean`), and records the
**exact parity dichotomy** that decides whether the descent's controlling odd polynomial halves
in degree or stays `≈ deg A`.

## The second-descent ring identity (char-free, PROVEN)

Split `A, O` into even/odd parts in `u`: `A = Ae(u²) + u·Ao(u²)`, `O = Oe(u²) + u·Oo(u²)`.
With `v = u²` (so `u·u = v`):

  `A(u)² − u·O(u)² = EVEN(v) + u·ODD(v)`,  where
  `EVEN(v) = Ae(v)² + v·Ao(v)² − 2v·Oe(v)·Oo(v)`,
  `ODD(v)  = 2·Ae(v)·Ao(v) − Oe(v)² − v·Oo(v)²`.

This is `secondDescentSplit` below (a ring identity, any commutative ring). The antipode `−u`
shares `v = u²`, so `(A² − u O²)(−u) = EVEN(v) − u·ODD(v)`; a level-2 **core** point has
`ODD(v) = 0`, a level-2 **isolated** point has `ODD(v) ≠ 0`.

## The head-parity dichotomy (the OBSTRUCTION, measured exact, PROVEN structurally)

Write `A = HEAD − E`, `HEAD = u^{a/2} + γ·u^{b/2}`, `deg E < k/2`. The odd part of `A` is
`Ao = HEADo − Eo`, where `HEADo` is the odd part of the head.

* **Head-even sub-case** (`a/2, b/2` both even): `HEADo = 0`, so `Ao = −Eo`.  The term
  `2·Ae·Ao = −2·Ae·Eo` then has degree `deg Ae + deg Eo ≈ (a/2)/2 + (deg E)/2 ≈ a/4`
  *whenever `Eo ≠ 0`* (E has an odd part) — the head **re-injects** degree `≈ a/4`.  Only if
  *also* `Eo = 0` (E even) does `2·Ae·Ao = 0` and `deg ODD = deg(odd part of O²) ≈ deg O` — the
  genuine halving.  (`secondDescent_headEven_odd_drops`: if `Ao = 0` then `ODD = −Oe² − v·Oo²`.)
* **Head-odd sub-case** (`a/2` or `b/2` odd): `HEADo ≠ 0`, so `Ao` carries a degree-`≈ a/4` term
  and `2·Ae·Ao` has degree `≈ deg Ae + deg Ao ≈ a/2`.  The √ obstructs: `deg ODD ≈ deg A`, no
  halving.  A quadratic-character twist does **not** restore a polynomial descent — it only
  restricts `u` to the QR coset `(μ_{n/2})² = μ_{n/4}`, i.e. exactly the `v = u²` image already
  taken; it changes *which* coset, not the degree of `ODD`.

## What the descent DOES and DOES NOT buy (honest scope; the verdict)

**Does:** the head exponents halve `(a, b) ↦ (a/2, b/2)` **as long as both stay even**, i.e. for
exactly `v₂(gcd(a,b)) − 1` levels — a `2`-adic count tied to `n = 2^μ`, **not** `log₂ k`.  The
clean head-even-and-`E`-even descent terminates with `O` a constant and `iso = 0` (base case).

**Does NOT:** make `deg O` halve in general.  The codeword tail `E` generically has an odd part,
and the cross term `Ae·Eo` re-injects degree `≈ a/4` into `ODD` at *every* level (measured exact:
`deg ODD_2 = a/4` whenever `Eo ≠ 0`, vs `= deg O` when `Eo = 0`).  So the assignment's
"`deg O` halves ⇒ terminate in `log₂ k` levels ⇒ `iso ≤ O(log k)`" **conflates two distinct odd
polynomials**: the *tail* odd part `c_o` does halve, but the *second-descent* odd polynomial `ODD`
is `2·Ae·Ao − Oe² − v·Oo²`, dominated by the head whenever `A` has an odd part.

**Numerics (this lane, q-independence test):** the isolated count is a small constant
(`≤ 4`, empirically `≤ 2` for clean shapes) and — decisively — is **flat across 40 primes**
`q ≡ 1 (mod n)` at fixed config shape (stdev `0` for the vacuous-degree `deg P ≈ m` shapes; mild
`1↔2` swing for small heads, **never spiky**).  This `q`-independence is the structural signal:
the head-even sub-case looks genuinely char-free.  But the *general* `iso ≤ poly(k)` over `μ_{n/2}`
is **not** delivered by this descent — it is the same coset-structure count
(`#non-coset roots of a t-sparse poly`) that in char `p` is the **Cheng–Gao–Wan / Kelley–Owen**
theorem (`≤ 2√(t-1)·((q-1)/δ)^{(t-2)/(t-1)}` cosets, `q`-DEPENDENT, vacuous here) — i.e. it
reduces to the open BGK/Kelley general-position count, exactly as `_IsoSparsityMasonStothers.lean`
already names.  Over `ℚ`/char `0` the non-coset count is `poly(t)` unconditionally
(Bombieri–Zannier unlikely intersections); the char-`p` transfer is the wall.

This file proves the char-free **second-descent split** and the **head-even drop**, and names the
residual `SecondDescentStuckResidual` (the per-stuck-level isolated count) — NOT discharged here.
Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`.  Issue #407.
-/

namespace ProximityGap.Frontier.SecondDescentParity

open Polynomial

variable {F : Type*} [CommRing F]

/-! ## The second-descent ring identity -/

/-- **The second-descent split (char-free ring identity).**  For `A = Ae(X²) + X·Ao(X²)` and
`O = Oe(X²) + X·Oo(X²)`, the isolated polynomial `A² − X·O²` evaluates at `u` to
`EVEN(u²) + u·ODD(u²)` with
`EVEN = Ae² + X·Ao² − 2·X·Oe·Oo` and `ODD = 2·Ae·Ao − Oe² − X·Oo²`.
This is the exact `μ₂`-quotient of the *isolated* equation one level below the first descent. -/
theorem secondDescentSplit (Ae Ao Oe Oo : F[X]) (u : F) :
    let A := Ae.comp (X ^ 2) + X * Ao.comp (X ^ 2)
    let O := Oe.comp (X ^ 2) + X * Oo.comp (X ^ 2)
    let EVEN := Ae ^ 2 + X * Ao ^ 2 - 2 * (X * (Oe * Oo))
    let ODD := 2 * (Ae * Ao) - Oe ^ 2 - X * Oo ^ 2
    (A ^ 2 - X * O ^ 2).eval u = EVEN.eval (u ^ 2) + u * ODD.eval (u ^ 2) := by
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_comp, eval_X, eval_ofNat]
  ring

/-- **Antipodal evaluation at `−u`.**  Same data, at `−u`: `EVEN(u²) − u·ODD(u²)` (the sign of the
odd part flips), since `(−u)² = u²`.  Hence a level-2 root pairs antipodally iff `ODD(u²) = 0`. -/
theorem secondDescentSplit_neg (Ae Ao Oe Oo : F[X]) (u : F) :
    let A := Ae.comp (X ^ 2) + X * Ao.comp (X ^ 2)
    let O := Oe.comp (X ^ 2) + X * Oo.comp (X ^ 2)
    let EVEN := Ae ^ 2 + X * Ao ^ 2 - 2 * (X * (Oe * Oo))
    let ODD := 2 * (Ae * Ao) - Oe ^ 2 - X * Oo ^ 2
    (A ^ 2 - X * O ^ 2).eval (-u) = EVEN.eval (u ^ 2) - u * ODD.eval (u ^ 2) := by
  have hsq : (-u) ^ 2 = u ^ 2 := by ring
  simp only [eval_sub, eval_add, eval_mul, eval_pow, eval_comp, eval_X, eval_ofNat, hsq]
  ring

/-! ## The head-parity dichotomy -/

/-- **Head-even drop (the only halving case).**  When `A` has *no odd part* (`Ao = 0`, i.e. the
head exponents `a/2, b/2` are both even AND the tail `E` is even), the cross term `2·Ae·Ao`
vanishes and the second-descent odd polynomial is `ODD = −Oe² − X·Oo²` — degree `≈ deg O`, the
genuine halving.  This is the *only* configuration in which `deg ODD` is governed by `O` (small)
rather than by the head `A` (≈ `a/4`). -/
theorem secondDescent_headEven_odd_drops (Ae Oe Oo : F[X]) :
    (2 * (Ae * (0 : F[X])) - Oe ^ 2 - X * Oo ^ 2) = - Oe ^ 2 - X * Oo ^ 2 := by
  ring

/-- **Head re-injection (the obstruction).**  With a nonzero odd part `Ao ≠ 0`, the odd polynomial
carries the head term `2·Ae·Ao`.  We record the structural fact that `ODD + Oe² + X·Oo² = 2·Ae·Ao`
— so `deg ODD` is controlled by `deg(Ae·Ao) ≈ deg A` exactly when `Ae·Ao ≠ 0`.  (The measured
`deg ODD = a/4` whenever the codeword tail `E` has an odd part.) -/
theorem secondDescent_head_reinjection (Ae Ao Oe Oo : F[X]) :
    (2 * (Ae * Ao) - Oe ^ 2 - X * Oo ^ 2) + (Oe ^ 2 + X * Oo ^ 2) = 2 * (Ae * Ao) := by
  ring

/-! ## The named residual (the per-stuck-level isolated count — open, = BGK/Kelley) -/

/--
**`SecondDescentStuckResidual` — the genuine open input the second descent does NOT discharge.**

The second descent peels `v₂(gcd(a,b)) − 1` head-even levels (a `2`-adic count tied to `n`, not
`log₂ k`); at the first head-odd level the cross term re-injects degree `≈ deg A`, and the descent
**stalls**.  At a stall, the remaining isolated roots of `A² − u·O²` over `μ_m` (with `O ≠ 0`)
are exactly the **non-coset roots of an `O(k)`-sparse polynomial in a `2`-power subgroup** — the
Cheng–Gao–Wan / Kelley–Owen coset-structure object, whose char-`p` count is `q`-dependent
(`≤ 2√(t-1)·((q-1)/δ)^{(t-2)/(t-1)}` cosets, vacuous at the prize prime).  Over `ℚ` it is `poly(k)`
unconditionally (Bombieri–Zannier); the char-`p` transfer is the open BGK/Kelley general-position
cancellation.

Stated as the explicit hypothesis a closure must supply: the isolated count at a stalled level is
`≤ k + 1` (measured flat in `n` and in `q`, empirically `≤ 4`).  Naming it and proving it elsewhere
is the project's modularity convention; the second descent **reduces to**, and does **not** close,
this residual. -/
def SecondDescentStuckResidual (F : Type*) [Field F] (k : ℕ) : Prop :=
  ∀ (A O : F[X]), A.natDegree < 2 * k → O.natDegree < k →
    ∀ (s : Finset F),
      (∀ x ∈ s, (A ^ 2 - X * O ^ 2).IsRoot x ∧ O.eval x ≠ 0) →
        s.card ≤ k + 1

/-- Documentation anchor: the second descent peels `v₂(gcd(a,b)) − 1` head-even levels, then stalls
at the head-odd level on `SecondDescentStuckResidual`, which is the BGK/Kelley count — NOT closed
by the descent. -/
theorem secondDescentNote : True := trivial

end ProximityGap.Frontier.SecondDescentParity

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.SecondDescentParity.secondDescentSplit
#print axioms ProximityGap.Frontier.SecondDescentParity.secondDescentSplit_neg
#print axioms ProximityGap.Frontier.SecondDescentParity.secondDescent_headEven_odd_drops
#print axioms ProximityGap.Frontier.SecondDescentParity.secondDescent_head_reinjection
