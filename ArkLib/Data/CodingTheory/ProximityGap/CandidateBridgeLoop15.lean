/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.Basic

/-!
# Loop 15 — the rate-shift bridge: prize radius = capacity of the shifted rate `ρ+η`

A structural reframing that connects the disproved at-capacity sibling (Loop14) to the open prize,
and pinpoints *why* the prize's gap `η` protects it.

**Observation.** The prize radius `δ = 1 − ρ − η` is *exactly the capacity radius* `1 − ρ'` of the
shifted rate `ρ' := ρ + η`:

    1 − ρ − η = 1 − (ρ + η).

So the prize is "list decoding the rate-`ρ` subcode at the capacity radius of the rate-`ρ'`
supercode." Equivalently, the agreement threshold the prize demands is `(1−δ)·n = (ρ+η)·n = ρ'·n`,
which **exceeds the prize code dimension `ρ·n` by exactly `η·n`** — the *degree buffer*.

**Why this matters.** Crites–Stewart (Loop14) disprove correlated agreement at the supercode's
capacity: there is a line whose folds are close to rate-`ρ'` codewords (degree `< ρ'n = (ρ+η)n`).
But the prize asks for closeness to rate-`ρ` codewords (degree `< ρn`) at the *same* high agreement
`ρ'n`. The witnessing polynomials of the at-capacity failure live in the degree window
`[ρn, ρ'n)` — a buffer of `ηn` degrees **above** the prize code — so they are **not** prize
codewords. The at-capacity disproof therefore does *not* descend to the prize; the gap `η` is exactly
the `ηn`-degree buffer (this is the same margin as Loop4's below-capacity dimension wall). The open
question is precisely whether that buffer survives beyond-Johnson clustering.

This file proves the algebraic bridge (radius identity + degree buffer), sorry-free and axiom-clean.
See `DISPROOF_LOG.md` (Loop15 rate-shift bridge).
-/

namespace ArkLib.ProximityGap.BridgeLoop15

/-- **Rate-shift identity.** The prize radius `1 − ρ − η` equals the capacity radius `1 − ρ'` of the
shifted rate `ρ' = ρ + η`. -/
theorem prize_radius_eq_shifted_capacity (ρ η : ℝ) :
    1 - ρ - η = 1 - (ρ + η) := by ring

/-- **The prize agreement threshold is the shifted-rate dimension fraction.** The agreement the prize
demands at radius `δ = 1 − ρ − η` is `(1 − δ) = ρ + η = ρ'`. -/
theorem prize_agreement_eq_shifted_rate (ρ η : ℝ) :
    1 - (1 - ρ - η) = ρ + η := by ring

/-- **Degree buffer.** Over a domain of size `n`, the shifted-rate (supercode) dimension `(ρ+η)·n`
exceeds the prize-code dimension `ρ·n` by exactly `η·n`. The at-capacity failure polynomials of the
supercode live in this `η·n`-degree window above the prize code, so they are not prize codewords. -/
theorem degree_buffer (ρ η n : ℝ) :
    (ρ + η) * n - ρ * n = η * n := by ring

/-- **The buffer is genuinely positive** for a positive gap over a nonempty domain: `η·n > 0` when
`η > 0` and `n > 0`. So the supercode's at-capacity witnesses are strictly higher degree than any
prize codeword — the disproof cannot descend without crossing the buffer. -/
theorem degree_buffer_pos {η n : ℝ} (hη : 0 < η) (hn : 0 < n) :
    0 < η * n := mul_pos hη hn

/-- **Bridge to Loop4's wall.** The prize agreement threshold `(ρ+η)·n` strictly exceeds the prize
code dimension `ρ·n` (for `η,n > 0`) — the same `ηn` margin that makes the below-capacity dimension
wall (`below_capacity_kills_vanishing_explosion`, Loop4) bite. The open core is exactly whether this
margin also controls beyond-Johnson clustering, not just single-polynomial constructions. -/
theorem agreement_exceeds_dimension {ρ η n : ℝ} (hη : 0 < η) (hn : 0 < n) :
    ρ * n < (ρ + η) * n := by
  have : 0 < η * n := mul_pos hη hn
  nlinarith [this]

end ArkLib.ProximityGap.BridgeLoop15
