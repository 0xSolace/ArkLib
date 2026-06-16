# Plan (b) — the real structural input (the breakthrough; low odds, fully honest)

**Goal.** Make progress on the *actual* prize: the one structural input no elementary angle supplies
— **uniform per-rung orbit-count decay up the 2-power tower**, equivalently the cryptographic-`p`
sup-norm bound

    M(μ_n) = max_{b≠0} | Σ_{x∈μ_n} e_p(b·x) |  ≤  C · √( n · log(p/n) ).

This is **BCHKS Conjecture 1.12 = the BGK / Burgess-endpoint (α=¼) / Paley-graph wall**, open ~25
years. This plan does **not** promise a proof. It promises the sharpest *honest* progress possible
without new mathematics: a crisper reduction and a precisely-named missing fact.

## Why this is the real thing (and why grinding can't reach it)

Plan (a)'s `w(n)` lives on the over-determined far-line = the Johnson/Plotkin **proxy** face,
computable at `p ≈ n⁴`. The genuine prize is **`p`-dependent** — invisible until cryptographic `p`.
The 8-angle assault (#444) showed every elementary route is circular, tautological, or
object-confused, and that the proven entropy ceiling provably *can't* decide it (wrong inequality
direction). So this is hard analytic NT, not compute.

## Steps (deliverables that are real even though the core stays open)

1. **State the missing lemma as one clean `def : Prop`** in Lean — the per-rung orbit-count decay /
   the sup-norm bound — and prove the **conditional** `that Prop ⟹ prize` axiom-clean. A real,
   landable brick (an honest reduction), independent of whether the Prop is ever proven.

2. **Minimize the reduction.** Reduce the open core to the *smallest* named statement that closes
   it, so the dossier presents **one crisp conjecture**, not a family. (Much of this is done: the
   walled-set audit already collapsed ~15 routes onto this one object.)

3. **Quantify the literature gap.** di Benedetto et al. give `M(μ_n) = O(n^{1−31/2880})`, whose
   power-saving **vanishes exactly at `β = 4`** (the prize regime `n ~ p^{1/4}`). Pin, exactly, how
   much of `0.989 → 0.5` that and its 2024–26 successors cover, and what residual remains. Update
   `PAPERS_NEEDED.md`.

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
