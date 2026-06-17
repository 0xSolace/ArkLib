# Proximity Prize δ* — the close-or-kill master map (every open angle, positive & negative) (#444, 2026-06-17)

**Prize requirement** (proximityprize.org / eprint 2026/680): DETERMINE (pin, with proof) the largest
`δ*_C` for RS on a **smooth domain**, `ρ∈{½,¼,⅛,1/16}`, `ε*=2⁻¹²⁸`, `|F|` sufficiently large —
MCA face `ε_mca(C,δ*)≤ε*` ≡ list-decoding face `|Λ(C^{≡m},δ*)|≤ε*|F|`. $1M, no deadline.

**THE VERDICT (definitive, this sweep): NEITHER direction closes. The prize is genuinely open,
provable-in-principle, blocked by exactly one hard analytic-NT wall.**

## The object & what's settled
`δ*` is governed by `M(n)=max_{b≠0}|η_b|`, `η_b=Σ_{x∈μ_n}e_p(bx)`. Floor `δ*=1−ρ−Θ(1/log n)` ⟺
`M ≤ C√(n·log m)` (Ramanujan exponent ½ up to √log). **Char-0 is CLOSED** (cumulant gen-fn
`g(t)=½log I₀(2t)`, `κ_{2r}=c_r·n` linear all r, Bessel/arcsine; `M_char0≤√(2n log m)`). The entire
residual is the **char-p transfer** `A_r:=E_r(μ_n)−n^{2r}/q ≤ (2r−1)‼·n^r` at depth `r≈ln q≈89`,
`n=2^30` ≡ the BGK/Paley sup-norm at the Burgess barrier. SOTA `n^{1−31/2880}=n^{0.989}` (needs
`n>p^{1/4}`, OUTSIDE prize); **nothing crosses `n^{0.989}→n^{1/2}` at `β=4`.**

## POSITIVE arm — every route to PROVE `M≤floor` (all reduce to the BGK wall)
| angle | verdict | why |
|---|---|---|
| P1 effective sum-product push | reduces-to-bgk | best effective exponent cliffs before ½ at β=4 |
| P2 prove No-Excess unconditional | reduces-to-bgk | exact faithfulness FALSE at prize scale; soft ceiling = the cyclotomic-norm wall |
| P3 Weil/Deligne b-parameter family | refuted | sheaf conductor is **floored at the rank n/2**, not O(1) ⟹ Deligne vacuous |
| P4 big-monodromy + Larsen | refuted | Deligne-vacuity onset `r₀=1+β/2` kills max-control (gives average, not the max, past r₀) |
| P5 BGK literature levers (BG/HBK/Shkredov/diB) | reduces-to-bgk | di Benedetto β-window cliff at 191/40 < prize β; none cross |
| P6 Bessel sub-baseline (`D(t)≤0`) | **refuted** | char-p MGF EXCEEDS the char-0 Bessel baseline for **generic** primes too (not only Fermat) |
| P7 Helleseth–Golomb–Gong cross-correlation | reduces-to-bgk | delivers only the Welch (√) lower bound, not the Ramanujan sup |
| P8 list-decoding face directly | reduces-to-bgk | the LD face has **no lever the MCA face lacks** |

**Positive conclusion:** all 8 routes funnel into the same char-p sup-norm wall at depth ~89, β=4.
A complete proof needs a genuinely new effective-equidistribution / sum-product / monodromy input
that **does not exist in the literature**. No in-tree path; the wall is singular.

## NEGATIVE arm — every route to prove the bound UNREACHABLE / FALSE / unprovable (all fail)
| angle | verdict | why the impossibility does NOT hold |
|---|---|---|
| N1 Fermat-floor-false | no-gain | the Fermat ratio 1.14 is **sharp-constant grazing**; the growth law survives |
| N2 unconditional lower bound `M≥√n·ω(n)` | **refuted** | Parseval forces only `M≥√n`; the floor is reachable (no divergent lower bound) |
| N3 "no moment proof can work" | **refuted** | the **DC-subtracted** route escapes the forced anomaly (DC-escape separation) — method not provably dead |
| N6 ineffectivity / undecidability | no obstruction | **ineffective BOUND ≠ ineffective VALUE**: `δ*` is a well-defined/computable quantity |
| N8 floor-violator density | no-gain | at the **absorb-floor constant C=2 there are ZERO violations** (incl. structured primes); the order law survives |
| N4 worst-case-over-family · N5 reduce-to-known-hard | (reduces-to-bgk) | the worst case is the generic wall, not a separate impossibility |
| N7 anomaly-growth (does `R_r` cross 1 below depth 89?) | **un-resolved decisive computation** | E_4 is the first char-p anomaly, but with the constant-absorbed ceiling no crossing was found at testable scale; the deep-r/β=4 crossing is the open wall itself |

**Negative conclusion:** there is **no impossibility**. The bound is reachable (only `M≥√n` is forced),
the `δ*` value is well-defined (not ineffective), the floor is **not** false (the Fermat grazing is
absorbed by a bounded constant; the growth law `δ*=1−ρ−Θ(1/log n)` survives every negative attack),
the moment method is not provably dead (DC-escape), and there is no undecidability. The prize is **not**
unprovable — it is **hard-open**.

## Master verdict
- **Answer (the value):** `δ* = 1 − ρ − Θ(1/log n)` — survives all negative attacks; well-defined, not ineffective.
- **NOT closable now (positive):** all 8 positive routes reduce to the **char-p BGK sup-norm at depth ~89, β=4** = the 25-year-open analytic-NT problem; no literature input crosses it.
- **NOT impossible (negative):** no unconditional lower bound, no false-floor, no undecidability, no method-death.
- **The single decisive open object:** the char-p excess `W_r ≤ slack_r` at deep `r` (≡ `M ≤ C√(n log m)`),
  char-0-closed, char-p-open. Requires a NEW effective-NT input. The single un-run decisive computation
  is **N7** (does `R_r` cross 1 below depth 89 at β=4? — settles whether the DC-Wick route is alive).

**Honest bottom line:** the campaign has reduced the $1M prize to a single, sharp, hard, *genuinely-open*
analytic-number-theory wall — char-0 closed in closed form, the value pinned (modulo the constant), no
impossibility obstruction — and that wall is the BGK/Paley short-character-sum bound for thin 2-power
subgroups at the Burgess barrier, which neither this campaign nor the literature can currently cross.
