# I031 Step (b): the deterministic→Gaussian sup-comparison for the cyclotomic Gauss-period frame (#389)

**Status:** promising-partial. The comparison `M ≤ C·E sup_b|G_b|` is structurally pinned and
empirically holds with a bounded constant, but its *derivation* reduces to the same per-period
sub-Gaussian-tail (BGK/Lamzouri) wall — chaining buys only the index reduction, not a moment-free
route. Refutation-tested; honestly scored. NOT a closure. Author: δ* lane, 2026-06-15.

## The object

`M(μ_n) = max_{b≠0} ‖η_b‖`, `η_b = Σ_{x∈μ_n} e_p(b·x)`, `μ_n ⊂ F_p^×` the 2-power subgroup
(`n=2^μ`, `n|p−1`, `p≫n³`, `m=(p−1)/n`). Step (b) of the I031 handle: compare `M` to the expected
sup `E sup_b|G_b|` of the matched centered Gaussian `G_b = Σ_x g_x e_p(b·x)` (`g_x` iid std complex
normal), aiming to recover the floor exponent `1/2` from Dudley/Slepian on the orbit quotient.

## (i) Covariance structure — PINNED EXACTLY (axiom-clean Lean)

`Cov(b,b') = E[G_b conj G_{b'}] = Σ_{x∈μ_n} e_p((b−b')x) = η_{b−b'}` — **the covariance is the period
at the difference frequency** (a subgroup correlation). Variance `Cov(b,b)=η_0=n`. The L² chaining
metric is `d(b,b')² = 2n − 2 Re η_{b−b'}`.

Formalized: `ArkLib/Data/CodingTheory/ProximityGap/I031MatchedGaussianCovariance.lean` —
`matchedCov`, `matchedSqMetric`, `matchedCov_diag`, `matchedSqMetric_{diag,symm}`,
`matchedCov_conj_symm`, `matchedSqMetric_nonneg_le` (`0 ≤ d² ≤ 4n`), and the flat-metric certificate
`matchedCov_l2_average` (`Σ_c ‖η_c‖² = q·n` from the second-moment substrate). All
`[propext, Classical.choice, Quot.sound]`, no Weil.

## (ii) The chaining metric is FLAT — chaining = union bound, NOT multi-scale geometry

`probe_i031_metric_flatness_vs_collapse.py` measures `d` directly over quotient reps:

| n | √(2n) | d_med | d_max | frac<½diam | frac<¼diam |
|---|---|---|---|---|---|
| 4 | 2.83 | 2.83 | 3.98 | 0.163 | 0.031 |
| 8 | 4.00 | 3.99 | 5.58 | 0.077 | 0.002 |
| 16 | 5.66 | 5.65 | 7.61 | 0.012 | 0.000 |
| 32 | 8.00 | 7.99 | 10.37 | 0.000 | 0.000 |
| 64 | 11.31 | 11.32 | 13.34 | 0.000 | 0.000 |

`d_med ≈ √(2n)` exactly, and the close-pair fraction `→ 0` as n grows. **The metric is flat.** This
independently reconfirms the Salem–Zygmund self-refutation
(`deltastar-salem-zygmund-gausssum-chaining-2026-06-13.md`): the I031 "collapse log q → log m" is the
**index-count reduction** (union bound over `m=q/n` orbit reps), NOT a Talagrand multi-scale chaining
gain. There is no multi-scale geometry to exploit. (`matchedCov_l2_average` is the rigorous half:
the avg of `‖η_c‖²` is exactly n, so the avg squared metric is the flat `2n` and close pairs vanish.)

## (iii) The comparison HOLDS empirically with a bounded constant

`probe_i031_det_vs_random_transfer.py` / `probe_i031_deeptail_anomaly.py`: deterministic `M` vs
matched-Gaussian `E sup|G_b|` (200 trials, orbit reps):

| n | M/E sup|G| |
|---|---|
| 4 | 1.29 | 8 → 1.31 | 16 → 1.29 | 32 → 1.39 | 64 → 1.26 | 128 → 1.29 |

`M/E sup|G| ∈ [1.26, 1.39]`, **no growth** to n=128 — the deterministic worst case is tracked by the
matched-Gaussian sup within a bounded factor. This is the I031 decider's "bounded transfer constant."

## (iv) The OPEN content: the per-period sub-Gaussian tail at depth — the BGK/Lamzouri knife-edge

Flat metric ⟹ `M ≤ C·E sup|G_b|` reduces to ONE inequality: the per-index period
`Re(ζ̄ η_c)` is sub-Gaussian with proxy `O(n)`, **uniformly in n at the deep tail** the union bound
over m indices probes. The matched Gaussian has this with proxy exactly n at every depth; the
deterministic side is the question. Read the proxy off the actual max: `sig_eff² := M²/(2 log m)`,
sub-Gaussian-at-depth ⟺ `sig_eff²/n` bounded.

`probe_i031_deeptail_anomaly.py` (single prime, n=8..512): `sig_eff²/n ∈ [0.57, 0.92]`, non-monotone.
`probe_i031_proxy_creep_regression.py` (denoised, 3 primes/n, n=8..128):

| n | ⟨sig_eff²/n⟩ |
|---|---|
| 8 | 0.588 | 16 → 0.698 | 32 → 0.687 | 64 → 0.683 | 128 → 0.726 |

Regression fits over n=8..128:
- constant `c=0.676`, SSE 0.0110;
- `a + b·log log n`: `b=+0.131`, SSE 0.0033 (best);
- `a + b·log n`: `b=+0.038`, SSE 0.0041.

**The honest knife-edge.** The proxy is flat to ~0.68–0.73 from n=16 (non-monotone — n=32, 64 dip
below n=16), strongly disfavouring a `(log n)^c` power creep. But a faint `log log n` drift fits ~3×
better than a pure constant. Extrapolating to the prize `n=2^30`: the `log log n` model gives
proxy → 0.92 (bounded < 1); the `log n` model gives → 1.33 (bounded, modest). **Over the accessible
16× range the data cannot distinguish a bounded constant from an extremely slow `log log n` creep** —
and a slow creep is precisely the BGK/Lamzouri `n^{o(1)}` signature. The β-sweep (thinning the
subgroup, the BGK-harder regime) shows NO inflation: `sig_eff²/n` *decreases* 0.70→0.59 as β goes
3.0→5.0 at fixed n=16.

## Verdict (honest)

- The deterministic→Gaussian **comparison holds with a bounded constant** in the accessible range, and
  its structure is now fully pinned (covariance = period-at-difference, flat metric, axiom-clean Lean).
- Chaining gives **NO moment-free shortcut**: the flat metric collapses Dudley to the union bound, so
  the comparison reduces to exactly the per-period sub-Gaussian tail = the same even-moment wall the
  campaign already faces. This refutes the sub-hope that generic chaining beats the moment route.
- Whether the comparison constant is genuinely bounded or creeps as `n^{o(1)}` is the **open core**,
  empirically a knife-edge (constant vs `log log n` indistinguishable to n=128). This IS the prize.

**Self-ranking:** novelty 6 (covariance/flat-metric Lean is new; the wall identification echoes the
Salem–Zygmund note) · insight 8 (cleanly separates what chaining buys — index reduction only — from
the open per-period tail) · proximity 9 (exact prize frame) · feasibility 4 (the residual is the BGK
wall, no genuine reduction; chaining adds nothing the union bound did not).

## Adversarial verification (2026-06-15)

Independent re-run reproduced all primary probes exactly: metric flatness (frac<½diam
0.163→0.077→0.012→0→0), `sig_eff²/n ∈ [0.57, 0.92]` (n=8..512), `M/E sup|G| ∈ [1.26, 1.39]`,
β-sweep *decreasing* 0.70→0.59. The Lean file rebuilt clean: real `lake build` (3312 jobs,
`autoImplicit=false`), all six theorems on `[propext, Classical.choice, Quot.sound]`, no `sorryAx`,
no Weil. The file honestly proves ONLY Step (i) — six algebraic facts about two `noncomputable def`s
(`matchedCov`, `matchedSqMetric`); it does NOT claim the sup-comparison or the orbit-reduction as a
theorem and hides no content in a hypothesis.

NEW out-of-sample test of the knife-edge (`probe_i031_creep_adversarial_verify.py`, 3 primes/n):
fit `sig_eff²/n` on n≤64, predict held-out n=128. **The constant model wins decisively** — held-out
abs err: const 0.030, loglog 0.164, logn 0.195. The octave slopes are non-monotone with a *negative*
last step (+0.086, +0.024, +0.102, **−0.140** for n=64→128: sig_eff²/n drops 0.80→0.66). The
in-sample "loglog fits 3× better" finding does NOT survive out-of-sample: the apparent creep was a
noisy single-point rise at n=64. This does not *prove* boundedness (the BGK `n^{o(1)}` residual is
genuinely open and the accessible range is small), but it removes the empirical support for a creep —
the bounded-constant (`isHandle`) reading is the one the data favors. **Verdict: faithful,
not overclaimed.** The Lean is axiom-clean and correctly scoped; `isHandle=true` is defensible for
the *structural* deliverable (covariance pinned, chaining = union bound), with the honest caveat that
the *quantitative* exponent-1/2 claim still rests on the open BGK/Lamzouri per-period tail.

## Artifacts
- `ArkLib/Data/CodingTheory/ProximityGap/I031MatchedGaussianCovariance.lean` (axiom-clean)
- `scripts/probes/probe_i031_metric_flatness_vs_collapse.py`
- `scripts/probes/probe_i031_deeptail_anomaly.py`
- `scripts/probes/probe_i031_perperiod_subgaussian_tail.py`
- `scripts/probes/probe_i031_proxy_creep_regression.py`
- `scripts/probes/probe_i031_creep_adversarial_verify.py` (held-out / octave-slope verification)
- prior: `probe_i031_det_vs_random_transfer.py`, `probe_i031_quotient_chaining.py`,
  `deltastar-salem-zygmund-gausssum-chaining-2026-06-13.md`
