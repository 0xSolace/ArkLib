/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CyclicPowerFiber

/-!
# The mixed weight-2 descent quadform is a binomial; its `μ_N`-root count is `gcd(|a−b|, N)`
(#444, SEAM A, gap G2)

The locked even/odd descent identity (`Sweep_A41_DescentAZForm`, `_DoorIVZLagrangeBound`) writes the
list-decoding agreement as `A + Z`, with the non-symmetric term `Z = #{y∈μ_N : P(y)² = y·Q(y)²}` =
the `μ_N`-root count of the quadform `R = Pp² − X·Qp²`, Lagrange-bounded by `deg R`.

For the **mixed weight-2 word** `u = xᵃ + xᵇ` (`a` even, `b` odd, vs the zero codeword) the even/odd
split makes `Pp = −y^{a/2}` and `Qp = −y^{(b−1)/2}` MONOMIALS, so the quadform collapses to an
explicit **binomial**
  `R(y) = P(y)² − y·Q(y)² = yᵃ − yᵇ`,
and its non-symmetric count is the binomial root count over the cyclic group `μ_N`:
  `Z = #{y∈μ_N : yᵃ = yᵇ} = #{y∈μ_N : y^{|a−b|} = 1} = gcd(|a−b|, N)`   (`N = #μ_N`).

This is the EXACT, finite, **cyclotomic/gcd** value of the non-symmetric `Z`-term on the weight-2
locus — far below the generic `deg R = max(a,b)` Lagrange ceiling: the subgroup structure of `μ_N`
genuinely constrains the binomial. For a **mixed** word `|a−b|` is ODD while `N = 2^{a−1}` is a
2-power, so `gcd(|a−b|, N) = 1`: the non-symmetric single-fibre correction is exactly `1`,
mechanistically explaining the empirical `S₁ ≤ 1` (probe `probe_444_g1_S1_scaling_law.py`). This
file locks the GENERAL gcd root-count of `y^a = y^b` over a finite cyclic group; the parity
remark `(gcd(odd, 2^k)=1)` follows as a corollary `Nat.Coprime`.

PROBE BACKING (`scripts/probes/probe_444_g2_weight2_quadform_binomial.py`): `Z = gcd(|a−b|, N)`
matches the direct `μ_N`-root count on every mixed weight-2 word, n=8..64, proper `μ_n`, `p ≫ n³`,
structured primes, never `n = q−1`.

SCOPE / honesty: an exact subgroup binomial root-count, reusing
`_CyclicPowerFiber.card_fiber_one_eq_gcd`. NOT a CORE/cancellation/completion/moment/
anti-concentration/capacity claim and NOT a G2 closure (the "worst word is weight-2" minimality
is still open). It pins the EXACT non-symmetric `Z` on the
weight-2 family. CORE OPEN. Axiom-clean (`{propext, Classical.choice, Quot.sound}`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.EvenOddDescent

open Finset

/-- In any group, `y^a = y^b ↔ y^(a−b) = 1` when `b ≤ a` (nat exponents). -/
theorem pow_eq_pow_iff_pow_sub_eq_one {G : Type*} [Group G] {y : G} {a b : ℕ} (hba : b ≤ a) :
    y ^ a = y ^ b ↔ y ^ (a - b) = 1 := by
  constructor
  · intro h
    have : y ^ (a - b) * y ^ b = 1 * y ^ b := by
      rw [← pow_add, Nat.sub_add_cancel hba, one_mul, h]
    exact mul_right_cancel this
  · intro h
    have : y ^ (a - b) * y ^ b = 1 * y ^ b := by rw [h]
    rw [← pow_add, Nat.sub_add_cancel hba, one_mul] at this
    exact this

variable {G : Type*} [CommGroup G] [Fintype G] [DecidableEq G] [IsCyclic G]

/-- **The binomial `μ_N`-root count.** Over a finite cyclic group `G` of order `N`, the number of
`y` with `y^a = y^b` (`b ≤ a`) equals `gcd(N, a − b)`. This is the exact non-symmetric `Z`-term of
the mixed weight-2 descent quadform `R = y^a − y^b`. -/
theorem card_binomial_roots_eq_gcd (a b : ℕ) (hba : b ≤ a) :
    (univ.filter (fun y : G => y ^ a = y ^ b)).card = (Nat.card G).gcd (a - b) := by
  have hcong : (univ.filter (fun y : G => y ^ a = y ^ b))
      = (univ.filter (fun y : G => y ^ (a - b) = 1)) := by
    apply Finset.filter_congr
    intro y _
    simp only [pow_eq_pow_iff_pow_sub_eq_one hba]
  rw [hcong]
  exact ProximityGap.Frontier.CyclicPowerFiber.card_fiber_one_eq_gcd (a - b)

/-- **Mixed weight-2 single-fibre count is exactly 1 over a 2-power cyclic group.** When the
exponent gap `a − b` is ODD (forced for a mixed-parity weight-2 word) and `N = #μ_N` is a
2-power, the
binomial root count is `gcd(N, a−b) = 1`. This is the mechanistic reason the non-symmetric `S₁`
correction is exactly `1` on the weight-2 mixed locus. -/
theorem card_binomial_roots_eq_one_of_odd_gap_of_twoPow
    (a b : ℕ) (hba : b ≤ a) (hodd : Odd (a - b)) {k : ℕ} (hN : Nat.card G = 2 ^ k) :
    (univ.filter (fun y : G => y ^ a = y ^ b)).card = 1 := by
  rw [card_binomial_roots_eq_gcd a b hba, hN]
  -- gcd(2^k, odd) = 1 since 2^k and an odd number are coprime
  have hcop : Nat.Coprime (2 ^ k) (a - b) := by
    apply Nat.Coprime.pow_left
    rw [Nat.coprime_two_left]
    exact hodd
  exact hcop

/-- **Even-even weight-2 spine count is a shifted binomial root count.** For an EVEN-EVEN weight-2
word the non-symmetric `Z` vanishes (`Q = 0`) and the agreement is the pure doubled symmetric spine
`2·A` with `A = #{y∈μ_N : y^{a/2} + y^{b/2} = 0} = #{y∈μ_N : y^c = −1}`, `c = |a−b|/2`. Over a
finite cyclic group the fiber of the `c`-power map over ANY target is either empty or a single
kernel-coset, so this spine count is at most `gcd(#G, c)` (and exactly `gcd(#G, c)` when `−1` is a
`c`-th power, else `0`). This is the symmetric companion to `card_binomial_roots_eq_gcd`, completing
the weight-2 census. (Probe `probe_444_g2_eveneven_spine_count.py`: `A ∈ {0, gcd(c,N)}`, n=8..64.) -/
theorem card_pow_eq_target_le_gcd (c : ℕ) (w : G) :
    (univ.filter (fun y : G => y ^ c = w)).card ≤ (Nat.card G).gcd c := by
  rw [ProximityGap.Frontier.CyclicPowerFiber.card_fiber_powMonoidHom c w]
  split
  · exact le_rfl
  · exact Nat.zero_le _

end ArkLib.ProximityGap.EvenOddDescent
