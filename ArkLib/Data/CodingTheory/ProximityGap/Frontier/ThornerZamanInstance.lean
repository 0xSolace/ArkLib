/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.KKH26ThornerZaman
import Mathlib.Tactic.NormNum.Prime

/-!
# B3 — a concrete discharge of `TZPrimeSupply` (#334)

`ThornerZamanS128.lean` flags the single analytic hypothesis `TZPrimeSupply n β supply`
(`KKH26ThornerZaman.lean`) — the window `[n^β, 2·n^β]` contains `≥ supply` primes `p ≡ 1 (mod n)`
— and its plan **(ii)** invites a concrete instance via explicit primes (a finite check; no
`native_decide`).  This file does exactly that for `n = 16`, `β = 2`:

> **`tzPrimeSupply_16_two`** — `TZPrimeSupply 16 2 6`, witnessed by the six explicit primes
> `{257, 337, 353, 401, 433, 449} ≡ 1 (mod 16)` in the window `[256, 512]`.

This is an honest, axiom-clean discharge of the named hypothesis for a concrete smooth modulus —
the route that the `kkh26_mcaDeltaStar_le_of_TZ` consumer needs, demonstrated end-to-end on a real
instance (the asymptotic `n^{β−1−o(1)}` supply is the [TZ24] analytic statement that remains the
open input for general `n`).
-/

namespace ArkLib.ProximityGap.KKH26

/-- **Concrete discharge of `TZPrimeSupply` for `n = 16, β = 2`.**  The window `[16², 2·16²] =
[256, 512]` contains the six primes `257, 337, 353, 401, 433, 449`, all `≡ 1 (mod 16)`. -/
theorem tzPrimeSupply_16_two : TZPrimeSupply 16 (2 : ℝ) 6 := by
  refine ⟨?_⟩
  have hpow : ((16 : ℕ) : ℝ) ^ (2 : ℝ) = 256 := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
  have hsub : ({257, 337, 353, 401, 433, 449} : Finset ℕ) ⊆ tzWindow 16 (2 : ℝ) := by
    intro p hp
    rw [mem_tzWindow]
    fin_cases hp <;>
      exact ⟨by norm_num, by decide, by rw [hpow]; norm_num, by rw [hpow]; norm_num⟩
  calc (6 : ℕ) = ({257, 337, 353, 401, 433, 449} : Finset ℕ).card := by decide
    _ ≤ (tzWindow 16 (2 : ℝ)).card := Finset.card_le_card hsub

end ArkLib.ProximityGap.KKH26
