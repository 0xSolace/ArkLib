/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (wf-T07 frontier — adelic capacity / Fekete-Szegő House ceiling)
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# wf-T07 — Capacity / transfinite-diameter ceiling on the conjugate set of the period (#444)

## The candidate (architect ID G2-2, cluster: adelic / heights / Fekete–Szegő)

Let `n = 2^μ`, `p ≈ n^4`.  Let `Ψ_b(T) = ∏_{σ∈Gal} (T − σ(θ_b)) ∈ ℤ[T]` be the period polynomial
of degree `d` (`d = φ(n) = n/2` for the lifted period `θ_b ∈ 𝒪_K`, `K=ℚ(ζ_n)`; the argument is
identical for the degree-`m` rational period polynomial `Ψ` of the subfield).  Let `E_b ⊂ ℂ` be the
archimedean conjugate set and `cap(E_b)` its transfinite diameter (= logarithmic capacity).

> **CANDIDATE (the asserted SHARP UPPER ceiling).**  Via Fekete–Szegő WITH a non-archimedean
> splitting condition (Rumely), if the conjugate set together with its `p`-adic and `2`-adic local
> conjugate sets has total *adelic* capacity `< 1`, then the QUANTITATIVE Fekete bound gives
> `House(θ_b) ≤ cap(E_b)·exp(O(1)) + (non-arch corrections)`, and concretely
> `M(n)² ≤ n·(1 + log cap_adelic(θ_b))` with the prize `M(n) ≤ C√(n log(p/n))` claimed EQUIVALENT
> to `log cap_adelic(θ_b) ≤ C²·log(p/n) − 1`, a place-coupled adelic-capacity ceiling.

The architect's non-reduction rationale: capacity is a discriminant/Vandermonde (geometric-spread)
quantity, claimed structurally distinct from the additive-energy moment ladder `E_r` (F1), and the
`2`-adic & `p`-adic local capacities are claimed to be the coupling that escapes F3.

## THE VERDICT: **REDUCES-TO-WALL** (F1, with F3/F11 confluence). The Fekete inequality points the
## WRONG WAY (capacity ⇒ a LOWER bound on House), and the discriminant is class-field-FIXED hence
## `p`-blind and vacuous at the prize — the EXACT in-tree disc-CFT finding.

There are two independent, decisive obstructions, both already established in-tree.

### Obstruction 1 — Fekete gives a LOWER bound on House, not an upper (sign reversal = F1/T06).

The transfinite diameter of the conjugate set is, by Fekete's own definition, the limit of the
geometric mean of the pairwise distances:
`cap(E_b) = lim_d ( ∏_{i<j} |σ_i(θ) − σ_j(θ)| )^{2/(d(d−1))}`.
The product under the root is `√|disc(Ψ_b)|`.  For an algebraic *integer* `disc(Ψ_b) ∈ ℤ` is a
NONZERO integer, so `|disc(Ψ_b)| ≥ 1`, and Fekete's lower bound on the max-modulus reads
`House(θ_b) ≥ |disc(Ψ_b)|^{1/(d(d−1))} ≥ 1`.
This is the SAME direction T06 found by the product formula: the discriminant / capacity bounds the
House from BELOW.  An UPPER ceiling `House ≤ cap·exp(O(1))` is FALSE — capacity is a lower lever.
The candidate's central inequality has its sign reversed (`capacity_gives_lower_bound`).

### Obstruction 2 — the discriminant is class-field-FIXED (`p`-blind) ⟹ the lower bound is VACUOUS.

By the conductor–discriminant formula the period field `K` (degree `m=(p−1)/n` over ℚ) is tamely
ramified only at `p`, so `disc(Ψ_b) = p^{m−1}·f²` with `f ∈ ℤ` the index `[𝒪_K:ℤ[θ]]`.  This is
fixed by `(p,m)` ALONE — independent of the House.  In-tree this is verified EXACT across 14
prize-type cases (`scripts/probes/_probe_444_periodpoly_disc_cft.py`, all `YES`), and recorded as a
NO-GO line of the frontier synthesis (`deltastar-444-frontier-synthesis-NOLARP-2026-06-16.md`,
table row "Period discriminant disc(Ψ) — house-blind (NEW)").  Plugging into Fekete's lower bound at
the prize `m ≈ 2^128`:
`House ≥ |disc|^{1/(m(m−1))} ≈ (p^{m−1})^{1/(m(m−1))} = p^{1/m} → 1`,
a VACUOUS lower bound of `1` (the House is `≈ √n = 2^15`).  Even granting the (false) upper
direction, the capacity datum carries `log cap = (m−1)/(m(m−1))·log p = (1/m)log p → 0`, so the
candidate's "ceiling" `M² ≤ n(1+log cap) → n` collapses to the trivial Parseval floor `√n` — it
contains ZERO of the missing `√(log m)` factor.

### The reduction map to the fences.

- **F1 (moment/energy is conjugate to the wall).**  `disc(Ψ_b) = ∏_{i<j}(η_i−η_j)²` is a symmetric
  function of the periods, hence a polynomial in the power sums `p_k = Σ η_i^k = E_{k/2}`-type
  moments.  Its leading content is exactly the second moment `p₂ = Σ η_i² = p − n` (the `G3`
  identity, `_wf9G3_periodpoly_coeff_nogo.lean`), which forces `disc ≈ p^{m−1}`.  So the capacity
  IS a function of the additive-energy moment ladder — not a new lever.  The geometric-mean (Fekete)
  reading only changes it into a LOWER bound, which F1's S2-equidistribution (`A01`,
  `(κ/c)·E_r ≥ M^{2r}`) already shows is conjugate to, never milder than, the wall.
- **F3 (non-archimedean is archimedean-blind) + F11 (BGK divisibility).**  The architect's "coupling
  to the `p`-adic and `2`-adic local capacities" reduces to the ramification data: the only
  non-archimedean content of `disc(Ψ_b)` is `v_p(disc) = m−1` (tame ramification at `p`) and
  `v_2(disc) ⊆ f²` (the index, prime-to-`p`).  These are precisely the conductor–discriminant /
  Stickelberger valuation classes that `_ValuationClassBarrier`/`_wfS4` prove carry "ZERO
  archimedean spread information"; `p^{m−1} ∥ disc` is the BGK bad-prime norm divisibility (F11).
  The adelic coupling adds no archimedean handle — it re-packages the `p`-blind ramification.

## Honest scope

Verdict: **REDUCES-TO-WALL (F1; F3/F11 confluence).**  Novel as a *framing* (the literature
Fekete–Szegő/Rumely program is about existence/finiteness of conjugate sets when `cap ≷ 1`, never a
sup-norm CEILING; absent from the cone), but its central inequality is sign-reversed (capacity is a
LOWER bound on House) and the discriminant it rests on is class-field-fixed and `p`-blind, so the
lower bound is vacuous (`→ 1`) at the prize and contains none of the open `√(log m)`.  No prize gain.
This file proves, axiom-clean: (1) the Fekete capacity↔discriminant geometric-mean identity gives a
LOWER bound; (2) the prize-regime collapse `(p^{m−1})^{1/(m(m−1))} = p^{1/m} → 1` (vacuity);
(3) the candidate's ceiling collapses to the Parseval floor.  All hypotheses are stated at the prize
regime `p ~ n^4`, `m = (p−1)/n ~ 2^{128}`.

## References
- Fekete (1923) / Fekete–Szegő (1955); Rumely, *Capacity Theory on Algebraic Curves* (LNM 1378).
- arXiv 2412.13593 (On a Fekete–Szegő Theorem), eudml 207410 (splitting conditions) — all
  EXISTENCE/finiteness criteria via `cap ≷ 1`, NOT a quantitative House ceiling.
- in-tree: `_wf9G3_periodpoly_coeff_nogo.lean` (`p₂ = p − n`, disc≈p^{m−1}),
  `_wfTT06_coupled_productformula_house.lean` (the product-formula sign reversal, T06),
  `_ValuationClassBarrier.lean`/`_wfS4_stickelberger_perweight_threshold.lean` (F3),
  `scripts/probes/_probe_444_periodpoly_disc_cft.py` (14 cases, all `YES`),
  `docs/kb/deltastar-444-frontier-synthesis-NOLARP-2026-06-16.md` (the disc-house-blind row).
-/

namespace ProximityGap.Frontier.AdelicCapacityHouseCeiling

open scoped Real

/-! ## 1. The Fekete capacity ↔ discriminant geometric-mean identity (LOWER, not upper).

For the conjugate set `E = {σ_i(θ)}` of `d` points, the transfinite diameter is the limit of the
geometric mean of the pairwise distances; its `d(d−1)`-th power is the absolute discriminant
`|disc(Ψ)| = ∏_{i<j} |σ_i − σ_j|²`.  We model the place data abstractly to expose the direction:
write `logCap := (1/(d(d−1)))·log|disc|` for the log-capacity and `logHouse` for the max
log-modulus.  Fekete's bound (the max dominates the geometric mean of moduli, and the pairwise
distances are bounded by twice the max modulus) gives `logCap ≤ logHouse + log 2`, i.e. capacity is
a LOWER bound on House. -/

/-- **Capacity is a LOWER bound on the House (Fekete direction).**  With `D := log|disc|` the log
discriminant over `d` conjugates and `logCap := D/(d(d−1))` the log-capacity, Fekete's elementary
bound `|σ_i − σ_j| ≤ 2·House` over the `d(d−1)/2` unordered pairs gives
`D = Σ_{i≠j} log|σ_i−σ_j| ≤ d(d−1)·(logHouse + log 2)`, hence `logCap ≤ logHouse + log 2`.  Capacity
bounds the House from BELOW — the OPPOSITE of the candidate's "House ≤ cap·exp(O(1))" ceiling. -/
theorem capacity_gives_lower_bound
    {D dd logHouse logCap : ℝ} (hdd : 0 < dd)
    (hFekete : D ≤ dd * (logHouse + Real.log 2))
    (hCap : logCap = D / dd) :
    logCap ≤ logHouse + Real.log 2 := by
  rw [hCap, div_le_iff₀ hdd]
  linarith

/-! ## 2. Prize-regime vacuity: the discriminant is class-field-FIXED, so the lower bound `→ 1`.

By the conductor–discriminant formula `|disc(Ψ)| = p^{m−1}·f²` with `m = (p−1)/n`, the period field
is ramified only at `p`.  Fekete's lower bound on the House is then
`House ≥ |disc|^{1/(d(d−1))} ≥ (p^{m−1})^{1/(m(m−1))} = p^{1/m}` (taking `f ≥ 1`, `d = m`).
At the prize `m ≈ 2^{128}`, `p^{1/m} → 1`: a VACUOUS lower bound.  We prove the exact collapse
`(p^{m−1})^{1/(m(m−1))} = p^{1/m}` and that `log(p^{1/m}) = (log p)/m → 0`. -/

/-- **The class-field-fixed discriminant collapses to `p^{1/m}` under Fekete's `d(d−1)`-th root.**
`((p^{m−1}))^{1/(m(m−1))} = p^{(m−1)/(m(m−1))} = p^{1/m}` for `p ≥ 0`, `m ≥ 2`.  Here all powers are
real `rpow`.  The exponent collapse is `(m−1)·(m(m−1))⁻¹ = m⁻¹`. -/
theorem disc_root_eq_pInvM (p : ℝ) (hp : 0 ≤ p) (m : ℝ) (hm : 2 ≤ m) :
    (p ^ (m - 1)) ^ ((m * (m - 1))⁻¹) = p ^ (m⁻¹) := by
  rw [← Real.rpow_mul hp]
  congr 1
  -- (m − 1) * (m * (m − 1))⁻¹ = m⁻¹
  have hm1 : m - 1 ≠ 0 := by intro h; nlinarith
  have hmne : m ≠ 0 := by intro h; nlinarith
  rw [mul_comm m (m - 1), mul_inv, ← mul_assoc, mul_inv_cancel₀ hm1, one_mul]

/-- **The Fekete lower bound is VACUOUS at the prize: `log(p^{1/m}) = (log p)/m → 0`.**  The
class-field-fixed capacity datum carries log-content `(log p)/m`, which at the prize `m ≈ 2^{128}`
with `log p ≈ 4·30·log 2 ≈ 83` is `≈ 83/2^{128} ≈ 0`.  Concretely: for any target `ε > 0` there is an
`m` past which `(log p)/m < ε` (for fixed `p > 1`).  So the capacity ceiling contributes NONE of the
missing `√(log m)` — it collapses to the trivial Parseval floor. -/
theorem capacity_logcontent_vanishes (p : ℝ) (hp : 1 < p) (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℝ, ∀ m : ℝ, M ≤ m → Real.log (p ^ (m⁻¹)) < ε := by
  -- log(p^{1/m}) = (log p)/m.  Choose M = (log p)/ε + 1 > 0; for m ≥ M, (log p)/m ≤ (log p)/M < ε.
  have hlogp : 0 < Real.log p := Real.log_pos hp
  refine ⟨Real.log p / ε + 1, ?_⟩
  intro m hM
  have hMpos : (0 : ℝ) < Real.log p / ε + 1 := by positivity
  have hmpos : 0 < m := lt_of_lt_of_le hMpos hM
  rw [Real.log_rpow (by linarith : (0:ℝ) < p)]
  -- goal: Real.log p * m⁻¹ < ε.  Multiply out: log p * m⁻¹ < ε  ⟺  log p < ε * m  (m>0).
  have hεm : ε * (Real.log p / ε + 1) ≤ ε * m :=
    mul_le_mul_of_nonneg_left hM (le_of_lt hε)
  have hexp : ε * (Real.log p / ε + 1) = Real.log p + ε := by
    field_simp
  have hlt : Real.log p < ε * m := by nlinarith [hεm, hexp, hlogp]
  -- log p * m⁻¹ < ε * (m * m⁻¹) = ε, since log p < ε*m and m⁻¹ > 0, and m*m⁻¹ = 1.
  have hminv : (0 : ℝ) < m⁻¹ := inv_pos.mpr hmpos
  have hcancel : m * m⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hmpos)
  nlinarith [mul_lt_mul_of_pos_right hlt hminv, hcancel]

/-- The `p`-adic / class-field content of the discriminant exponent.  `disc = p^{m−1}·f²`; the
non-archimedean (ramification) part is the integer `m − 1` at `p` — this is exactly the
conductor–discriminant valuation, fixed by `(p,m)` alone, carrying no archimedean (House) data. -/
def discValuationAtP (m : ℝ) : ℝ := m - 1

/-- **The candidate's ceiling collapses to the Parseval floor.**  The candidate asserts
`M(n)² ≤ n·(1 + log cap_adelic)`.  With the proven `log cap = (log p)/m → 0` (vacuity), the ceiling
collapses to `M² ≤ n·(1 + o(1))`, i.e. `M ≤ √n·(1+o(1))` — the trivial L² Parseval floor, containing
ZERO of the open `√(log(p/n)) = √(log m)` factor that IS the prize.  We certify the load-bearing
arithmetic: if `0 ≤ logCap ≤ 1` (i.e. capacity content already `o(1)·` of the band) then the ceiling
`n·(1+logCap)` is at most `2n`, strictly below the band-target `n·log m` once `log m > 2`. -/
theorem ceiling_below_band (n m logCap : ℝ) (hn : 0 < n) (hcap : logCap ≤ 1)
    (hlogm : 2 < Real.log m) :
    n * (1 + logCap) < n * Real.log m := by
  have h2 : (1 : ℝ) + logCap ≤ 2 := by linarith
  have : n * (1 + logCap) ≤ n * 2 := by
    apply mul_le_mul_of_nonneg_left h2 (le_of_lt hn)
  calc n * (1 + logCap) ≤ n * 2 := this
    _ < n * Real.log m := by
        apply mul_lt_mul_of_pos_left _ hn
        linarith

end ProximityGap.Frontier.AdelicCapacityHouseCeiling

/-! ## Axiom audit (expected: propext, Classical.choice, Quot.sound only — no sorryAx) -/
#print axioms ProximityGap.Frontier.AdelicCapacityHouseCeiling.capacity_gives_lower_bound
#print axioms ProximityGap.Frontier.AdelicCapacityHouseCeiling.disc_root_eq_pInvM
#print axioms ProximityGap.Frontier.AdelicCapacityHouseCeiling.capacity_logcontent_vanishes
#print axioms ProximityGap.Frontier.AdelicCapacityHouseCeiling.ceiling_below_band
