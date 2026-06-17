# CANDIDATE PIN: multi-round FRI commit-phase soundness = c(ρ)/|F|, O(1)/|F| with explicit constants (#444)

The strongest positive result of the campaign, on the CORRECT object (multi-round commit-phase soundness,
where the prize `O(1)/|F|` is claimed — not the single-fold proxy, which grows with N).

## Model (canonical BCIKS reconstruction; PDF-independent)
`f_0` δ-far from RS[N,k], dyadic domain `D=⟨ω⟩`. Fold through ALL rounds `N→N/2→…→2→1` with challenges
`(λ_1,…,λ_{nr})`. A challenge tuple is **bad** (adversary "accepted") if proximity is maintained at every
round: `f_j` within the **matched relative radius** `⌊δ_0·|D_j|⌋` of `RS_j` for all `j`. Worst-case over
**genuine above-Johnson leaders** (true distance `= wmin = ⌊(1−√ρ)N⌋+1`, verified by exact min-distance,
not the buggy column-set filter). Exact folded distances throughout. Probe:
`scripts/probes/probe_commitphase_multiround.py`.

## Result: soundness = c(ρ)/|F|, q-independent integer constant
N=8, exact-distance leaders, worst-case commit-phase bad-count / total:

| ρ | q=17 | q=41 | q=73 | **c(ρ) = ratio·\|F\|** |
|---|---|---|---|---|
| 1/2 (k=4) | 289/17³ = 1/17 | 1681/41³ = 1/41 | 5329/73³ = 1/73 | **1** |
| 1/4 (k=2) | 1734/17³ = 6/17 | 10086/41³ = 6/41 | — | **6** |

- Bad-count `= c(ρ)·q^{nr−1}`, total `q^{nr}` ⇒ **soundness ratio `= c(ρ)/|F|`**, an exact `O(1)/|F|`.
- **`c(ρ)` is q-INDEPENDENT** (verified across 2–3 fields per rate): `c(1/2)=1`, `c(1/4)=6`.
- This is the prize's claimed `O(1)/|F|` above-Johnson behavior, **with an explicit, computable,
  rate-dependent integer constant** — a candidate exact pin of the commit-phase soundness.

## Structure of the constant (why O(1), not O(n))
The `nr` rounds split into "slack" rounds (matched radius `≥1`) and the final fold-to-exact-constant round
(radius `0`, one linear `1/q` condition). For the worst-case far word, the slack rounds are *fully passable*
(it stays radius-close for many challenges), and the binding content is `c(ρ)` surviving configurations
times the single `1/q` collapse. `c(½)=1` (one slack round, fully passable ⇒ only the `1/q` binds);
`c(¼)=6` (two slack rounds ⇒ `6×` surviving configs). This is exactly the **O(1)/|F|** the single-fold proxy
*could not* exhibit (it grew with N), recovered by the multi-round composition — consistent with 2026/861's
claim that the action-orbit (multi-round) structure removes the `n` factor of the BCHKS `a=O(n/η⁵)` bound.

## Honest scope (what is NOT yet established)
1. **N-independence is the crux and is NOT rigorously verified.** `c(1/2)=1` also appeared at N=16 (in an
   earlier run with the buggy filter), which is *suggestive* of N-independence, but a clean N=16 (and N=32)
   confirmation with the exact-distance leader check is pending (expensive: `C(16,8)` per candidate). If
   `c(ρ)` is truly N-independent, this **pins** the prize-regime commit-phase soundness; if `c(ρ)` grows
   with N, it is not `O(1)`.
2. Canonical BCIKS reconstruction, not 2026/861's exact commit-phase / action-orbit definition (gated PDF).
3. The matched radius uses `⌊·⌋`; the exact constants may depend on this normalization.
4. **It is a computation, not a proof.** A proof would derive `c(ρ)` (closed form) and the N-independence
   from the fold algebra + cyclic (action-orbit) symmetry — that derivation is the remaining open content
   (= Conj 7.1's dominance, now on a concrete computable target).

## Next
- N=16/32 commit-phase with exact-distance leaders (compiled enumerator) ⇒ verify N-independence of `c(ρ)`.
- Derive the closed form `c(ρ)` (the surviving-configuration count through the slack rounds) and prove
  N-independence ⇒ a complete pin of the commit-phase soundness in the prize regime.
