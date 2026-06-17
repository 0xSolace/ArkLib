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
1. **N-independence is the crux and is INCONCLUSIVE (not verified).** N=16 with the *correct*
   (probabilistic) leader check gives ratios 0.0159 (ρ=½) and 0.263 (ρ=¼) — *lower* than N=8's 0.0588 and
   0.353 — but these runs are **badly under-sampled** (~1000 random leaders vs a `q^{N/2}`-size coset
   space), so they are only loose *lower* bounds on the true worst case and cannot establish constancy or
   growth. (An earlier N=16 run that gave a clean `c=1` used the *buggy* `≤2-column` filter, i.e. it was
   contaminated by below-Johnson cosets — discard that.) So the clean `c(ρ)` law is established only at
   **N=8** (small enough to sample densely). Whether `c(ρ)` is N-independent — the difference between a
   genuine `O(1)/|F|` pin and a finite-size effect — needs a worst-case search at N=16/32 that pure-Python
   sampling cannot deliver (compiled/GPU enumerator or an analytic worst-case construction required).
2. Canonical BCIKS reconstruction, not 2026/861's exact commit-phase / action-orbit definition (gated PDF).
3. **The exact constants are convention-dependent (integrity note).** The model uses matched radius `⌊·⌋`
   AND floors the degree bound at `kdeg = max(1, k/2^L)` — so deep fold levels become *repetition codes*
   rather than the true `RS[size, k/2^L]` (which becomes the *zero* code once `k/2^L < 1`, where the real
   FRI stops and the verifier checks the final constant against the claimed value). The binding rounds
   (radius < covering radius) and hence the exact values `c(½)=1, c(¼)=6` depend on these choices. What is
   **robust** across the runs is the *shape*: bad-count `= c · q^{nr−1}`, i.e. soundness `= c/|F|` with a
   numerator constant in the field — the `O(1)/|F|` behavior. The exact `c(ρ)` requires 2026/861's precise
   commit-phase/degree-stop and acceptance definition (gated PDF).
4. **It is a computation, not a proof.** A proof would derive `c(ρ)` (closed form) and the N-independence
   from the fold algebra + cyclic (action-orbit) symmetry — that derivation is the remaining open content
   (= Conj 7.1's dominance, now on a concrete computable target).

## Next
- N=16/32 commit-phase with exact-distance leaders (compiled enumerator) ⇒ verify N-independence of `c(ρ)`.
- Derive the closed form `c(ρ)` (the surviving-configuration count through the slack rounds) and prove
  N-independence ⇒ a complete pin of the commit-phase soundness in the prize regime.
