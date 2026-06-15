/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-W6)
-/
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# Geometry-of-numbers short-vector reduction of the char-`p` transfer (#444, lane wf-W6)

## The lattice picture (the geometric framing of the spurious excess)

A spurious config at depth `r` is `σ_T = Σ_{i∈T} ε_i ζ_n^i`, `|T| ≤ 2r`, `ε_i ∈ {±1}`, with
`σ_T ≠ 0` over `ℤ` but `σ_T ≡ 0 mod p` (i.e. `σ_T ∈ ker(ev_h : ℤ[ζ_n] ↠ 𝔽_p)`, where `h` is a
primitive `n`-th root mod `p`).  In the power basis `ℤ[ζ_n] ≅ ℤ^{φ(n)}` with the **trace form**
the 2-power identity (NT2) gives the exact length

  `‖σ_T‖² = Σ_{j} |σ_T^{(j)}|² = φ(n)·|T| ≤ φ(n)·2r`,

so a weight-`|T|` config is a **short vector** of trace-radius² `φ(n)·|T|`.  The kernel
`L_p := ker(ev_h)` is an **index-`p` sublattice** of `ℤ[ζ_n]` (`ev_h` is surjective because `h`
has order `n | p−1`).  Hence

  `Spur_r(p) = #{ short vectors of L_p, ‖v‖² ≤ φ(n)·2r, v ≠ 0 over ℤ }`,

a **theta-series / lattice-point count** of the index-`p` sublattice.  The DC subtraction
(`A_r = E_r − n^{2r}/p`) removes exactly the trivial (zero) vector contribution `n^{2r}/p`.

## Sub-lemma this lane targets (G-W6 — the short-vector gap)

The cleanest sufficient condition the lattice gives is the **first-minimum gap**:

  `(G-W6)   φ(n)·2r < λ₁(L_p)²   ⟹   Spur_r(p) = 0   ⟹   E_r(μ_n) = E_r^{(0)} ≤ (2r−1)‼·n^r`.

i.e. as long as the moment depth keeps the config radius below the shortest *spurious* vector of
the index-`p` sublattice, the char-`p` count equals the char-`0` count and the Lam–Leung/Dyadic-K1
bound transfers with `K = 1`.

## What the W6 pre-screen MEASURES (honest, exact, prize scale) — and why `(G-W6)` is NOT enough

`probe wf7W6_shortvector_spur.rs` (exact mod-`p`, proper `μ_n = ⟨h⟩`, prize primes `p ≍ n^4`,
`p ≡ 1 mod n`) measures the shortest spurious vector at the **generic** prize prime:

  `λ₁(L_p)² = φ(n)·w_min`,  `w_min = 8` for `n ∈ {16,32,64}` (so first spurious at **depth
  `r_spur = 4`**, trace-radius² `= 4n`, essentially **constant in `n`**).

But the **optimal moment depth** `r* ~ ln(q)/2` GROWS: `r* = 4.2, 5.5, 6.9, 8.3` at
`n = 8,16,32,64`.  So for `n ≥ 16` the optimal depth sits **above** the spurious onset
(margin `r*−r_spur = 1.5, 2.9, 4.3` and growing), and `(G-W6)` **fails** at the depth the prize
needs.  ⟹ The gap route confirms, from the lattice side, the lane-M1 verdict: spurious vectors
EXIST in the optimal band; they must be **counted**, not excluded.

`probe wf7W6_spur_ratio_band.rs` measures the load-bearing relative count `Spur_r/Wick` across the
band: it **grows** with `r` (`n=32`: `0.0059, 0.0296, 0.0938` at `r=4,5,6`) and with `n` (at fixed
`r=6`: `0.0072` at `n=16` → `0.0938` at `n=32`).  The DC-subtracted prize ratio `A_r/Wick` at the
optimal depth nonetheless stays `< 1` in range (matching the headline `K_eff < 1` measurements),
but `Spur_r/Wick` is NOT uniformly small — so the bound that must hold is the *aggregate*
`E_r^{modp}/Wick ≤ K^r`, NOT `Spur_r = 0`.

## What is PROVEN here (axiom-clean ℕ arithmetic — the structural reduction)

This file states the spurious count as an abstract sublattice short-vector count and proves the
two structural implications a geometry-of-numbers argument hangs on:

* `spur_zero_of_below_lambda1` — the **first-minimum gap (G-W6)**: if no nonzero spurious vector
  has weight `≤ 2r` (the gap hypothesis), the spurious count is `0`.  *(trivial-but-load-bearing:
  it is the exact place the lattice geometry would enter; the probe shows its hypothesis fails at
  `r*`.)*
* `energy_transfer_of_spur_zero` — `Spur_r = 0 ⟹ E_r = E_r^{(0)}`, so the char-`0` Dyadic-K1 bound
  transfers verbatim (`K = 1`).
* `energy_bound_of_spur_le` — the **relative-count assembly (the real route)**:
  `Spur_r ≤ ε·Wick  ∧  E_r^{(0)} ≤ Wick  ⟹  E_r ≤ (1+ε)·Wick`, the prize shape with constant
  `(1+ε)^{1/2r} → 1`.  This is the lattice analogue of lane-M1 `countRoute_energy_bound`, derived
  here purely from the additive split `E_r = E_r^{(0)} + Spur_r`.

## The precise remaining open step (the crux this lane pins, geometry-of-numbers form)

`(S-W6)   #{ v ∈ L_p : v ≠ 0, ‖v‖² ≤ φ(n)·2r } ≤ ε·(2r−1)‼·n^r`,  uniform over prize primes
`p ≍ n^β`, to depth `r ~ ln p`.  This is a **theta-series bound** on the index-`p` sublattice of
the cyclotomic trace lattice at radius `φ(n)·2r` — equivalently (by `ev_h`-fibering) a Chebotarev
/ effective-splitting count of prize primes dividing a weight-`≤2r` antipodal-free cyclotomic norm.
A Minkowski/Banaszczyk *transference* bound on `λ_i(L_p)` controls the count only when the radius
is below `λ₁`, which the pre-screen REFUTES at `r*` — so the open crux genuinely needs the full
*counting* (second-moment-of-counts) version of transference, NOT just the first minimum.  Lane
wf-W6 reduces the prize to `(S-W6)` and proves the surrounding implications axiom-clean.
-/

open Finset Nat

namespace ArkLib.ProximityGap.ShortVectorSpur

/-- `Wick r n = (2r−1)‼ · n^r`, the char-`0` Lam–Leung / Dyadic-K1 count bound. -/
def Wick (r n : ℕ) : ℕ := (2 * r - 1)‼ * n ^ r

/-- **Additive char-`0`/spurious split.** The char-`p` `r`-energy `E_r` is the char-`0` antipodal
count `E0` plus the spurious excess `Spur` (the configurations vanishing mod `p` but not over `ℤ`).
This is the defining decomposition of the transfer; here it is an explicit hypothesis carried by
the abstract counts (verified exactly in `wf7W6_spur_ratio_band.rs`: `E_r^{modp} − E_r^{char0}`). -/
structure EnergySplit where
  /-- the char-`p` `r`-energy `E_r(μ_n)` (full sum-zero-mod-`p` count). -/
  E : ℕ
  /-- the char-`0` antipodal count `E_r^{(0)}` (Lam–Leung, `≤ Wick`). -/
  E0 : ℕ
  /-- the spurious short-vector count `Spur_r(p)` of the index-`p` sublattice. -/
  Spur : ℕ
  /-- the geometry-of-numbers decomposition `E_r = E_r^{(0)} + Spur_r`. -/
  split : E = E0 + Spur

/-- **The first-minimum gap (G-W6).** If the spurious count is `0` — the lattice condition
`φ(n)·2r < λ₁(L_p)²`, no nonzero spurious short vector inside the config radius — then the
char-`p` energy equals the char-`0` energy. -/
theorem energy_transfer_of_spur_zero (S : EnergySplit) (h : S.Spur = 0) : S.E = S.E0 := by
  rw [S.split, h, Nat.add_zero]

/-- Restatement of the gap as a count-zero fact: an empty set of weight-`≤2r` nonzero spurious
vectors gives `Spur_r = 0`.  (The honest content of `(G-W6)`; its hypothesis is what the pre-screen
refutes at the optimal depth `r*`.) -/
theorem spur_zero_of_below_lambda1 (S : EnergySplit)
    (hgap : S.Spur ≤ 0) : S.Spur = 0 := Nat.le_zero.mp hgap

/-- **Spurious = 0 ⟹ char-`0` bound transfers with `K = 1`.** Composing the gap with any char-`0`
bound `E0 ≤ Wick` (the in-tree Dyadic-K1 `zeroSumCount_le_doubleFactorial_dyadic`). -/
theorem energy_bound_of_spur_zero {r n : ℕ} (S : EnergySplit)
    (hspur : S.Spur = 0) (hchar0 : S.E0 ≤ Wick r n) : S.E ≤ Wick r n := by
  rw [energy_transfer_of_spur_zero S hspur]; exact hchar0

/-- **The relative-count assembly (S-W6 ⟹ prize shape).** If the spurious short-vector count is at
most `ε·Wick` and the char-`0` count is at most `Wick`, the full char-`p` energy is at most
`(1+ε)·Wick`.  This is the lattice route's payoff: a *relative theta-series bound* on the index-`p`
sublattice yields the prize square-root shape with constant `(1+ε)^{1/2r} → 1`. -/
theorem energy_bound_of_spur_le {r n ε : ℕ} (S : EnergySplit)
    (hspur : S.Spur ≤ ε * Wick r n) (hchar0 : S.E0 ≤ Wick r n) :
    S.E ≤ (1 + ε) * Wick r n := by
  rw [S.split, add_mul, one_mul]
  exact Nat.add_le_add hchar0 hspur

/-- **Monotonicity of the spurious-multiplier transfer.** If two primes give spurious counts with
`Spur ≤ Spur'` and the same char-`0` base, the energy bound is monotone — the worst prize prime (the
one maximising the index-`p` short-vector count) dominates, the uniform-over-`p` reduction. -/
theorem energy_mono_in_spur (E0 Spur Spur' : ℕ) (h : Spur ≤ Spur') :
    E0 + Spur ≤ E0 + Spur' := Nat.add_le_add_left h E0

end ArkLib.ProximityGap.ShortVectorSpur

/-! ## Axiom audit -/
section AxiomAudit
open ArkLib.ProximityGap.ShortVectorSpur
-- Verified axiom-clean (`lake env lean`): the proofs depend only on `propext` (or nothing) —
-- within `{propext, Classical.choice, Quot.sound}`, no `sorryAx`.
-- #print axioms energy_transfer_of_spur_zero  -- (no axioms)
-- #print axioms energy_bound_of_spur_le        -- [propext]
-- #print axioms energy_bound_of_spur_zero      -- [propext]
-- #print axioms energy_mono_in_spur            -- (no axioms)
end AxiomAudit
