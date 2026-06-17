# Prove-BGK strategies (recovered) + consolidated verdict across both attacks (2026-06-16)

The standard-proof workflow (7 strategies) ran 28 agents / 1.6M tokens then crashed at the synthesis step
on a JS field-missing bug; the math survived in the journal. Recovered below + merged with the novel-math
verdict (doc 16) into the consolidated answer to "prove BGK / attack with non-reducing novel math."

## Recovered standard-strategy results
| strategy | best bound | conditional close? | new partial result |
|---|---|---|---|
| **S1 moment method** | `M ≤ (1+o(1))·n` (useless; = trivial) | only the `W_r ≤ Slack_r` bound itself (circular, = BGK two-sided) | **divisor-threshold lemma** on the *average* spurious energy excess over `P_β={p=mn+1 : n^β≤p<2n^β}` |
| **S2 Stepanov / HBK** | `M ≤ n^{1−o(1)}` (= the SOTA, no improvement) | no standard conjecture (Stepanov takes no L-function input) | **dyadic-fold triangle-tightness** lemma |
| **S3 Katz/Deligne monodromy** | `M ≤ C√p` (trivial Weil ceiling) | **a log-free/power-saving *effective Deligne equidistribution at polynomial conductor depth*** (NOT a standard conjecture — a new Katz-type statement) | **vertical/horizontal dichotomy** quantifying exactly what monodromy can/can't do |
| **S4 Stickelberger / Gross-Koblitz** | `M ≤ √p` (trivial) | none — GRH improves *incomplete* sums, not the *complete* subgroup sum | exact `M(n) = (n/(p−1))·DFT(Gauss sums)` identity |
| **S5 sum-product / additive energy** | `M ≤ 3^{1/4} n^{3/2}` (worse than SOTA, lossy) | none | **EXACT additive energy** closed form for thin `μ_{2^a}` at the Burgess barrier |
| **S6 dyadic / FRI fold** | `M ≤ √(pn) ~ n^{2.5}` (worse) | none — cross-term carries the full sum | **exact cross-term law** for the coset fold |
| **S7 GRH-family conditional** | no improvement under GRH | **NONE — GRH family is STRUCTURALLY INERT (no-go lemma)** | the closing input is OUTSIDE the GRH family: a *cyclotomic Sato-Tate* (Frobenius-equidistribution `E_r(μ_n)=(2r−1)‼·n^r` in char-p at fixed p) — itself the open problem restated |

## The decisive new finding: NO standard conjecture closes it
**S7's no-go lemma is the important result:** GRH / GLH / Lindelöf / log-free zero-density are *structurally
inert* for this prize, because the target is a **complete** sum over the subgroup `μ_n` (a closed orbit),
whereas the entire GRH family controls **incomplete** character sums `Σ_{x≤N} χ(x)` (Montgomery–Vaughan
`√p log log p`). There is no place to feed zero-distribution information. So **even conditionally on the
strongest standard conjectures, the prize stays open.** The ONLY statement that closes it is a Katz-type
*effective/horizontal cyclotomic Sato-Tate equidistribution at the fixed prime* (S3's conditional + S7's
identification agree) — which is **not a standard conjecture; it is the open BGK problem in equidistribution
clothing** (the proven version is *vertical*, q→∞; the prize needs *horizontal*, fixed q).

## Consolidated verdict (both attacks: 7 standard strategies + 7 novel frameworks)
1. **No genuine escape and no non-reducing route.** Novel-math (doc 16): all 7 reduce; the *two-column
   orthogonality theorem* proves WHY — all cancellation is archimedean PHASE, invisible to p-adic /
   cohomology / rep-theory; phase cancellation `= E_r =` 2nd-order = meta-capped at Johnson.
2. **No standard-conjecture conditional close.** Prove-BGK (this doc): GRH family structurally inert; the
   closing input is itself open (effective horizontal equidistribution).
3. **Best unconditional bound is unchanged:** `n^{1−o(1)}` (Konyagin/Stepanov), off from `√n` by a power.
4. **The two-sided `prize⟺M(n)` equivalence is airtight for the prize code** (proven `RadiusOneExact`); the
   only non-reducing object (curve-decodability) is inert for `μ_n` RS and lives only for *subspace-design*
   codes — so the single genuinely-different direction is **change the code**, not bound `M(n)`.
5. **The live target, pinned and unchangeable:** does a short (`≤2 ln q`-term) `±1`-relation of `2^μ`-th roots
   of unity vanish mod the prize prime? (= `Spur_r` = `Ξ_k` = char-p Lam-Leung transfer = BGK). char-0-true
   (proven), char-p-open at `n=2^30`; proven for `n ≲ 40` by the norm gate.

## Genuinely-new partial results banked (worth keeping)
- Exact additive energy of `μ_{2^a}` at the Burgess barrier (S5) — a clean closed form.
- The divisor-threshold lemma on average spurious-energy excess (S1) — controls the *average* (not sup).
- The monodromy vertical/horizontal dichotomy (S3) + the GRH-inert no-go (S7) — sharp negative results
  pinning exactly which analytic input is missing.
- The two-column orthogonality theorem (N1) — proves cohomological methods structurally cannot reach the sup.

## Bottom line
Across 14 independent attacks (7 standard proof strategies + 7 highly-novel frameworks), each adversarially
verified: **the prize is the irreducible 25-year BGK/Paley wall, no escape, no standard-conjecture close,
best bound `n^{1−o(1)}`.** A proof requires a genuinely new effective horizontal equidistribution for thin
2-power-subgroup Gauss periods at the Burgess barrier — which does not exist in current mathematics and is
not implied by any standard conjecture. The matching sibling memory ("#444 no-escape terminal": 71 non-BGK
theorems refuted, 0 survivors) independently confirms this. Source: wf_b204afc8 (recovered) + wf_5576da1e.
