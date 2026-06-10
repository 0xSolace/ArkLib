/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.ThreePrimePacketRefutation

/-!
# Issue #232 — the O70 divisor-coset window law is FALSE at three primes (O111)

The remaining window-law residue ("the t > 1 law past two primes — no
literature") gets its statement-level redteam: the O70 FORM of the law — every
windowed-vanishing subset decomposes into full `μ_d`-cosets with `d ∣ n`,
`d > t` — is provably FALSE at the first three-prime modulus, ALREADY at the
`t = 1` stratum.

`divisor_coset_law_fails_three_primes`: the O105 witness
`S = {5, 6, 12, 18, 24, 25} ⊆ [0, 30)` vanishes, yet through the point `5` NO
full `μ_d`-coset lies inside `S` for ANY divisor `1 < d ∣ 30` — so `S` admits no
divisor-coset decomposition whatsoever (every nonempty union of cosets covers
each of its points by a full coset).

Interpretation for the ledger: the two-prime window law (O97) cannot extend to
3+ primes in its coset form — its very STATEMENT dies, not merely its proof.
Any 3+-prime window law must live on a different surface; the candidate is the
ℚ-component form (O109: vanishing ⟺ prime-fiber components), with windowed
power sums constraining the components.  That reformulation is the genuinely
open mathematics; this brick pins the obstruction that forces it.
-/

namespace ThreePrimeWindowObstruction

variable {L : Type*} [Field L] [CharZero L]

omit [CharZero L] in
/-- **The divisor-coset window law fails at three primes** (`n = 30`, `t = 1`
stratum): a vanishing subset of `μ₃₀` exists through whose point `5` no full
`μ_d`-coset (`1 < d ∣ 30`) lies inside the set — the O70 coset form of the
window law has no three-prime extension. -/
theorem divisor_coset_law_fails_three_primes {ζ : L}
    (hζ : IsPrimitiveRoot ζ 30) :
    (∑ e ∈ ({5, 6, 12, 18, 24, 25} : Finset ℕ), ζ ^ e = 0)
    ∧ ∀ d ∈ Nat.divisors 30, 1 < d →
        ¬ ∀ t < d, (5 + t * (30 / d)) % 30
            ∈ ({5, 6, 12, 18, 24, 25} : Finset ℕ) := by
  refine ⟨(ThreePrimePacketRefutation.debruijn_packet_conjecture_fails_three_primes
    hζ).1, ?_⟩
  decide

end ThreePrimeWindowObstruction

#print axioms ThreePrimeWindowObstruction.divisor_coset_law_fails_three_primes
