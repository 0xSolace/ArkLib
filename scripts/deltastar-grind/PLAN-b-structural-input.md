# Plan (b) — the real structural input (the breakthrough; low odds, fully honest)

**Goal.** Make progress on the *actual* prize: the one structural input no elementary angle supplies
— the **per-frequency `√q·B` INCIDENCE cancellation** over the annihilator hyperplane:

    I(δ) ≤ |G| + √q · B,   B = max_{b≠0} ‖η_b‖,   η_b = Σ_{x∈μ_n} e_p(b·x).

This is `ShawOperator.MCAShawConjecture` = **BCHKS Conjecture 1.12** (the generalized-Paley-graph /
Ramanujan bound at cancellation exponent **½**), open ~25 years.

> **The two-input correction (verified in-tree — don't re-trip it).** The bare sup-norm bound
> `M(μ_n) = max_{b≠0}‖η_b‖ ≤ C√(n·log(p/n))` is *necessary context but **provably insufficient** by
> itself* — it feeds only the additive-energy lane, and its sole route to incidence pays the **naive
> `q·B`** triangle (`I ≤ |G| + q·B`), which at the prize budget `q·ε* ≈ n ≈ |G|` forces `B ≈ 0`
> (vacuous). In-tree: `Frontier/_PrizeFloorOfBGK.lean`, `CharSumBudgetVacuity.lean`. The prize-bearing
> input is the **`√q`** (not `q`) incidence upgrade. (B1 resolved: a weaker bound gives no shortcut.)

This plan does **not** promise a proof. It promises the sharpest *honest* progress possible
without new mathematics: a crisper reduction and a precisely-named missing fact.

## Why this is the real thing (and why grinding can't reach it)

Plan (a)'s `w(n)` lives on the over-determined far-line = the Johnson/Plotkin **proxy** face,
computable at `p ≈ n⁴`. The genuine prize is **`p`-dependent** — invisible until cryptographic `p`.
The 8-angle assault (#444) showed every elementary route is circular, tautological, or
object-confused, and that the proven entropy ceiling provably *can't* decide it (wrong inequality
direction). So this is hard analytic NT, not compute.

## Steps (deliverables that are real even though the core stays open)

1. **Use the in-tree named `def : Prop`** — `ShawOperator.MCAShawConjecture S B` (equivalently
   `OpenCoreConditionalPin.WorstCaseIncidenceBounded`), the per-frequency `√q·B` incidence bound —
   **NOT** the sup-norm Prop (proven insufficient). The conditional `that Prop ⟹ prize` is *already*
   landed axiom-clean (`Frontier/_PrizeFloorOfBGK.lean` `prizeFloor_window_of_BGK_and_incidence`,
   `_PrizeReducesToBCHKS.lean`). The deliverable is to **sharpen/minimize** that reduction — not
   re-derive a (vacuous) `sup-norm ⟹ prize` conditional.

2. **Minimize the reduction.** Reduce the open core to the *smallest* named statement that closes
   it, so the dossier presents **one crisp conjecture**, not a family. (Much of this is done: the
   walled-set audit already collapsed ~15 routes onto this one object.)

3. **Record the literature gap (settled, not open).** di Benedetto et al. give the PROVEN
   power-saving `M(μ_n) = O(n^{1−31/2880})`; the tree records this as **NOT prize-closing**
   (`CharSumDeltaStarBridge.lean`, `CharSumBudgetVacuity.lean`) — it sits *below* cancellation
   exponent ½, and a weaker provable bound gives **no shortcut** (B1 resolved). The residual is the
   gap from `~0.989` down to **exactly ½ at the `√q`-incidence level** (not the sup-norm level); no
   sub-½ successor closes the window. The char-0 face is **CLOSED** in exact closed form
   (Bessel `g(t)=½·log I₀(2t)`); the genuine open gap is the **char-`p` departure** from that closed
   char-0 shadow at depth `r ≈ ln q`. Update `PAPERS_NEEDED.md`.

4. **Probe for structure, honestly.** The 2-power/antipodal/Frobenius/Lam–Leung structure is fully
   characterized (O183/O184) and provably accounts for *everything except* the residual orbit count.
   Any genuinely new handle would have to bound an **off-diagonal** `(r−1)`-dimensional variety count
   that no diagonal/partition-rank/Stepanov method delivers (the named gap from O179). Treat any
   "lead" with the adversarial completeness critic before believing it.

5. **Never fabricate.** The correct output is a sharper conditional + the precise missing analytic
   fact. If a step looks like it closes the core with elementary means, it is almost certainly
   circular — re-audit it.

## Honest status

This is the genuine $1M math. Realistic deliverables are **conditional Lean bricks** and a
**sharper named conjecture**, not a closure. Closing it needs new analytic number theory that does
not yet exist. That is not a failure — pinning a $1M problem to one crisp open conjecture with every
escape walled *is* the honest summit of a reduction.
