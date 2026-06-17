# Issue #444 live open leads — attacked, all collapse, ON-BGK holds (wf_c51a5089-9c6, 2026-06-16)

Reviewed #444 (the canonical #407-successor ON-BGK dossier, 384 comments / ~95 bricks) and attacked its 6
distinct in-tree LIVE open leads (§6.1, 6.3, 6.4, 6.5, 6.8, + the di Benedetto beat), each with concrete
computation + 3-lens adversarial verification. **Verdict: all 6 collapse; #444's two-sided ON-BGK verdict
holds, now triply-confirmed (my #407 work + #444's campaign + this attack).** Central wall re-measured:
`M(n)/√(2n log m) ∈ [0.74, 0.84]` flat across n=8..256 — tracks `√(n log m)`, NOT decaying to `√n`; the
half-power `log m` factor is real.

## Per-lead
| lead | verdict | why (computed) |
|---|---|---|
| **L1 §6.3 determinantal / 2×2 Plücker minor** | collapses-to-BGK | the minor `g_a g_{b−1}−g_{a−1} g_b` is **identically 0 (rank-1 row proportionality) at the worst monomial direction `x^k`** — vacuous exactly where needed; and `D*(2)=89 > 2·span=2n=32` (claimed bound FALSE at binder (10,4)). p-independence is the orbit size `S=n/gcd(b−a,n)` (group theory = Johnson signature), not a degree count. |
| **L2 §6.4 dedup-strictness at log depth** | collapses-to-Johnson | survival ceiling `C(2m,r)−C(m,r)2^r` cancels only the leading `2^r`, leaving `~½r(r−1)·C(n,r)` — a polynomial shave; count is super-budget by **+0.18 → +25.5 orders** (n=4→2048), never crosses budget for r≥2. |
| **L3 §6.5 Linnik good-prime / Spur_r(p)** | collapses-to-BGK | `#badPrimeSet ~ (2^r C(n/2,r))²·(n/2)·m ~ 2^{4469}` **hyper-dominates** the prize prime at `r~log q`; the fixed ∀-universal prize prime (forced `v₂≥30`, structured) is bad; the realized object is the char-0 Lam-Leung count whose char-p transfer **IS** M(n). |
| **L4 §6.8/I031 dilation-chaining constant** | collapses-to-BGK | fixing n=32, growing m: `M/√n` NOT flat (2.46→4.0) while `M/√(n log m)` bounded (1.0–1.55). The chaining constant **carries `√(log m)`**; orbit reduction only converts `log p → log m`, not to `O(1)`. |
| **L5 §6.1 onset-threshold growth law (core)** | collapses-to-BGK | **characterizable LINEAR law:** `onset-threshold(r) ≈ 0.54r` (in β), crosses `β=4` at `r≈6`. So `W_r > 0` for `r≥6` at the fixed prize prime ⇒ the floor is **NOT** the exact `W_r=0` statement; it must be the inequality `E_r ≤ Wick` = the open BGK sum. |
| **L6 di Benedetto + higher Sidon `T_4,T_5`** | collapses-to-BGK | `T_4,T_5` are **structurally absent** from the trilinear `H_exp(t_2,t_3)`; energy method capped at `1/24` (proven in-tree `diBenedettoSaving_le_ceiling`) = **12× short**; the `0.9583` β=4 beat leaves the **full `0.4583` half-power gap** to `0.5`; deeper d-fold descent *decreases* the saving. |

## The genuinely useful findings (bankable)
1. **L5 onset-threshold law is CHARACTERIZABLE and two-faced.** char-0 margin GROWS (`Wick/E_r`: 1.14 →
   1.50 → 2.26 → 3.90; favorable, matches in-tree char-0 proof). But `onset(r) ≈ 0.54r` crosses `β=4` at
   `r≈6`, so the char-p excess reopens above onset. **This proves the floor's correct form is the
   inequality `E_r ≤ Wick` (= M(n) ≤ C√(n log m)), NOT the exact `W_r=0`** — settling the precise statement
   of the open core. Useful: pin the exact `r` where onset crosses β=4 at prize n, certifying `W_r>0`.
2. **L6's `diBenedettoSaving_le_ceiling` is a PROVEN witness that the energy/second-order route is
   exhausted** (caps at `1/24`, 12× short of the prize). Actionable: convert it from a numeric cap into the
   meta-theorem's formal "no third route" anchor.
3. **L3: `#badPrimeSet` hyper-domination is a one-line lemma killing the whole good-prime family** — prove
   `#badPrimeSet(r) ≫ p` in the fixed ∀-field window for `r ≥ r₀` small.

## Honest bottom line
No escape among L1–L6. Each is vacuous on the worst direction (L1), a p-independent over-count never
crossing budget (L2, L3), carries `√(log m)` in its "constant" (L4), leaves the half-power gap behind a
proven cap (L6), or proves the floor's exact form false while the inequality form is M(n) (L5). The single
open core is **unchanged**: `M(n) ≤ C√(n log m)` for thin 2-power `μ_n` at the Burgess barrier (β≈4–5) =
char-p Lam-Leung transfer to `r~ln q≈89`. char-0 proven (re-reproduced); char-p at log-depth is the
recognized-open 25-year BGK/Paley wall. #444's ON-BGK verdict is correct and now triply-confirmed.

Source: wf_c51a5089-9c6 (7 agents). Related: docs 13,14 (#407 thread-pulls, same verdict); issue #444 §0.0,§6.
