# I_∞ campaign — decay-rate attack verdict + reconciliation (wf_bf3b69a6-74c, 2026-06-15)

14-agent workflow attacking the multiplier decay rate `m(w)` past capacity from 10 angles, with a
core-stratified EXACT measurement (n=32 full curve, no feasibility wall) and adversarial judging.
**Verdict: 0 closures. All 10 angles reduce to the open Gauss-period/Paley bound. This SUPERSEDES
the over-optimistic "floor holds with margin" headline of doc 05 (see correction below).**

## The honest decay characterization (replaces "flat at n/4−1")
Exact core-stratified decomposition, e1-disjoint/additive, verified at all 23 measured (n,w):
`I_pure(w) = Σ_c D_c(w,n)`, with **two strata PROVEN closed on their support**:
- `D₁(w,n) = n` (core=1, support w≡1 mod 4) — multiplier exactly 1 = budget.
- `D₂(w,n) = n²/4 − n = n·(n/4−1)` (core=2 "backbone", support w≡0 mod 4) — CONSTANT from w=4
  through capacity and beyond; truncates only at the support edge.
- `D_c, c≥3` (the "excess") — appears near/past capacity, peaks AT capacity (n=32, w=16: m=38,
  I=1216 > n²=1024), dies largest-core-first. **No closed form; the decay lives entirely here.**

Shape facts (killing the old "flat" story): m(w) is NOT flat — it RISES to a peak at capacity
w=n/2, is symmetric about capacity on the w≡0 band (I(8)=I(24)=224, I(16)=1216 at n=32), then decays.
Peak multiplier grows superlinearly: n=8→1, n=16→3, n=32→38.

## THE FLOOR VERDICT — reduces to the open core (agrees with 72-sweep)
- All 9 substantive angles (A1–A8,A10) → `reduces-to-open`; A9 (large-deviation) → `refuted-dead`
  (LDP counts subsets not distinct values; n=16 w=9: 80 subsets vs 48 distinct, off).
- The decay rate reduces to ONE open quantity: `B = max_{b≠0}|Σ_{x∈μ_n} e_p(bx)| ≤ 2√n` on the thin
  2-power subgroup (best proven BGK `n^{1−o(1)}`, gap ~n^{0.4}). Floor holds ⟺ `m(w*)→O(1)` ⟺ B≤C√n.
- **For the PURE object the data points the WRONG way:** window-edge multiplier GROWS `1 → 13`
  (n=16→32) at `w*=ρn+n/log₂n`; only ~1/3 of the peak→budget drop is realized over the backoff.
  So even the pure sub-object does NOT self-quench to budget at reachable scales.

## RECONCILIATION with doc 05 (Q-workflow "floor holds with margin") — doc 05 was TOO OPTIMISTIC
- Doc 05's positive read rested on the WORST-direction "quench at the edge", which was a `j`-indexed
  **extrapolation** of an `exp(c·n)` fit that never measured the exact n=32 edge cell.
- This workflow's judge (angle A2, the only `fits:true` angle) shows that "worst dies before capacity
  at n≤32, so pure is extremal, so floor holds" is **non-closure twice over**: (i) it silently asserts
  √n-cancellation of the worst far-pencil character sum (the open wall — the `Θ(n/log n)` offset is
  literally invisible at n≤32); (ii) even granting pure-extremality, the pure m(w*) grows 1→13.
- **Correction to the famous "3504" worst-direction spike:** at n=16 w=5 the count (3984) is
  **char-p POLLUTED** (3936/3968/3984 across primes) — NOT the char-0 prize object. The char-0
  worst-direction at the relevant near-window bands is at budget (m≈1: n=16 w=7,8→16; n=32 w=6..9→n+1).
  So neither the optimistic nor the "3504" pessimistic figure is the real asymptotic; the asymptotic
  `limsup_n m_worst(w*)` is the open Gauss-period quantity, full stop.

## What is GENUINELY NEW (bankable; not in the 72-sweep)
1. **Two proven closed strata** `D₁=n`, `D₂=n²/4−n`, e1-disjoint — the decay is localized ENTIRELY to
   `c≥3`. A real reduction in the support of the open part.
2. **A clean NEGATIVE:** pure window-edge multiplier grows (1→13), `I_peak(32)>n²` — the floor cannot
   be salvaged from the pure object alone. The 72-sweep did not establish this.
3. **A SECOND open input:** A5 shows the equivalence `m(w*)=O(1) ⟺ B≤C√n` is two-sided FALSE (converse
   numerically fails: n=32 m_worst(window)=0 but B/√n≈4.06); the converse needs a second open hypothesis
   (syndrome-space PeriodIncidenceCoupling / additive-energy coupling). **The floor rests on TWO open
   inputs, not one.**

## Only honest forward moves (no closure available)
- **Engineering:** reach n=64 for a SECOND `c≥3` data point (the "no closed form" verdict rests on c≥3
  having exactly one populated case, n=32) — via the sketched third-level fold / subset-sum DP over the
  μ_{n/2} square-multiset (naive 2·4^16=8.6e9 half-states exceeds memory).
- **Modular (Lean):** state A5's FORWARD conditional as one named hypothesis — `B(μ_n)≤C√n ⟹ m_worst(w*)=O(1)
  ⟹ floor` — axiom-clean, per the project's "named residual = modularity" convention. Drop the false converse.

Tools/data: /tmp/prize_attack/decay/ (core_mitm2.c, driver2.py, worstdir_decay.py, DATA.md).
Related: [[arklib-407-multiplier-decay]], [[arklib-407-72-conjecture-sweep]], [[arklib-407-bchks-admissibility]].
