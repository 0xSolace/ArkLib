# Attacking the target `E_{r+1} ≤ (2r+1)·n·E_r` from every angle (#444)

The localized prize: prove the char-`p` step bound `E_{r+1}(μ_n;F_p) ≤ (2r+1)·n·E_r` (⟺ `E_r ≤
(2r−1)‼·n^r`, the Wick/sub-Gaussian bound) to depth `r ≈ log p`. Every angle attacked directly
(machine `crossterm_attack.py`/`crossterm2.py`, no sub-agents — weekly-capped).

## The cross-term decomposition (exact)
`E_{r+1} = n·E_r + cross_r`, where `cross_r = Σ_{t≠0} N_r(t)·c_2(t)`, `N_r(t) = #{Σx−Σy=t}`,
`c_2(t) = #{(a,b)∈μ_n²: b−a=t}`. So the target ⟺ **`cross_r ≤ 2r·n·E_r`**. Two exact identities:
`Σ_t N_r(t)² = E_{2r}` and `Σ_t c_2(t)² = E_2`.

## Angles attacked
- **[STRUCTURAL FACT] `max_{t≠0} c_2(t) = 2`** — μ_n is "Sidon-except-negation": every nonzero difference
  has ≤ 2 representations (two unit circles meet in ≤ 2 points). Machine-verified. A clean, exploitable
  input — but not enough alone (below).
- **[FAILS] Cauchy–Schwarz** `cross_r ≤ √(E_{2r}−E_r²)·√(E_2−n²)`: machine-verified the ratio to target
  GROWS `0.95, 1.11, 1.37, 1.74, 2.31, 3.15` (r=2..7) — too lossy (`√E_{2r}` is far too big; C–S ignores
  that `N_r(t)` concentrates near `t=0`). Ruled out.
- **[FAILS] crude max-multiplicity** `cross_r ≤ 2·(n^{2r}−E_r)`: bounds by `~n^{2r} ≫ 2rn·E_r`. Ruled out.
- **[★ NEW REDUCTION] step-ratio monotonicity.** Machine-verified the step ratio
  `R(r)=E_{r+1}/((2r+1)nE_r)` is `< 1` and **monotonically DECREASING** (`0.847 > 0.791 > 0.740 > 0.695 >
  0.656 > 0.623`, r=2..7) at prize-scale primes. **This reduces the entire char-`p` Wick bound to: a
  finite base case `R(r₀)≤1` (machine-checkable) + the single inequality `R(r+1) ≤ R(r)` (monotonicity).**
  Sharper than the in-tree `_wf7W3` (which needs `R(r)≤1` pointwise ∀r); here only monotonicity + one base.
  **LANDED** as `_StepRatioMonotone.stepRatio_le_one_of_antitone_base` (axiom-clean): antitone + base ⟹
  `R(r)≤1 ∀r≥r₀`, with the energy bridge `stepRatio_le_one_iff_energy`. The monotonicity is the open input.
- **[REDUCES] hypercontractivity / log-Sobolev** for the dyadic group `ℤ/2^μ`: `R(r)≤1` is a
  hypercontractive moment inequality; but the deterministic (non-random) cancellation it needs is the
  sub-Gaussian structure = the wall. Notes the dyadic log-Sobolev constant as the would-be input.
- **[REDUCES] SOS/positivity** `Wick_r − E_r ≥ 0`: char-0 SOS certs exist in-tree (the E_r closed forms);
  the char-`p` SOS certificate is the open wall.

## Honest status
The target is now reduced to **monotonicity of the step ratio** `R(r+1) ≤ R(r)` (+ a finite base case) —
a strictly sharper, lower-dimensional open input than "bound a character sum at every depth", and one the
data strongly supports (the ratio decreases cleanly). The monotonicity reduction is LANDED axiom-clean
(`_StepRatioMonotone`); proving the monotonicity itself for `μ_{2^μ}` in char `p` is the remaining wall.
Cauchy–Schwarz and crude-multiplicity are machine-ruled-out. `max c_2 = 2` is the clean structural fact
to build on. No fabricated closure.

> Machine-verified `probe_crossterm_attack.py`; the monotonicity reduction is the new landable handle.
