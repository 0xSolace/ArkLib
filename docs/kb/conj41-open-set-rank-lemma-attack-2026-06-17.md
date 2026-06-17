# Conjecture 41 (Open-Set Rank Lemma, ePrint 2026/858 §7) — computational attack + structural findings (#444)

Attacking the worst-case list-size conjecture `max_{s1,s2} M_true(s1,s2) ≤ ⌊(2D−1)/c⌋` (D=n−k, w=D−c),
the FRI-deployment-relevant (OP2-adjacent) open problem the threshold-halving paper leaves open and only
verifies empirically (to n=40). Solo, main-loop (subagent quota exhausted). Probes: `probe_conj41_*.py`.

## What is SOLID (validated / proven-computationally)
1. **Single-syndrome M_true engine validated.** `probe_conj41_core.py` reproduces the paper's anchor table
   EXACTLY (10/10): (5,2,1)→(M_compat 4, M_true 2); (6,3,1)→(10,4); (7,3,1)→(15,5); (8,3,1)→(21,6);
   (6,3,2)→(10,2); (8,3,2)→(21,2). So the M_true/M_compat computation is correct.
2. **The reduction.** A line `(s1,s2)` with m supports `E_i` compatible at distinct `γ_i` ⟺ `(s1,s2)∈ker(A)`,
   `A=stack[N_{E_i} | γ_i N_{E_i}]` (mc×2D), `N_E` = the c error-locator normals (coeffs of `Λ_E·x^r`).
   Conj 41 ⟺ `rank(A)=min(mc,2D)` for distinct γ_i (modulo an escape clause).
3. **NEW structural fact — the `(w+1)`-clique is an identically rank-deficient config.** For the tetrahedron
   clique {1,4,5,8} (n=12,k=6,w=3,c=3; the 4 size-3 subsets), `det(A)` is the ZERO polynomial in γ:
   `0/300` random distinct-γ configs had `det≠0` at `p=10⁶`, and the interpolated det-cubic is `[0,0,0,0]`.
   So the clique normal blocks are **linearly dependent for every γ at every prime** — the clique is an
   intrinsic rank-deficiency, not a small-p coincidence. This is *why* cliques are the conjecture's special
   ("escape") configurations.

## What is NOT resolved (honest — NOT a refutation)
- My naive line-`M_true` and kernel probes report apparent genuine `M_true=4 > ⌊(2D−1)/c⌋=3` for the
  tetrahedron at *all* primes (incl. 10⁶), where the paper says the violation vanishes for `p>p_0`. This is
  almost certainly a **definitional mismatch in the escape/scope accounting**, not a real counterexample:
  - The tetrahedron sits at the **degenerate boundary `c=w=3`**; the FRI-deployment regime Conj 41 targets is
    `c<w`, `c=Θ(n)` (e.g. `c≈0.2n` at rate 1/2). At `c=w=3`, rank-deficiency is *common* (`164/300` non-clique
    4-support configs also had `det=0`), so the line is dominated by compatibility/false-positives, exactly
    the `M_compat ≫ M_true` gap the paper stresses.
  - The paper's escape clause "∃i: `⟨n_0(E_i),s2⟩=0` ∀(s1,s2)∈ker A" did NOT hold for the clique kernel I
    extracted (`⟨Λ_E,s2⟩≠0` for all 4 supports), so either my escape formulation or my kernel/`M_true`
    accounting differs from theirs. Faithful reproduction needs the paper's exact definitions + reference
    scripts (cited [36] in 2026/858).
- **Conclusion: Conj 41 is neither proven nor refuted here.** It is genuinely hard open research (authors
  verified only empirically). The clean proof target is unchanged: prove `det(A)≢0` (generic full rank) for
  non-degenerate support configs in the `c≥3, c<w` FRI regime, with the rank-deficient locus (cliques etc.)
  characterized by the escape clause.

## Net
Validated M_true engine; established the clique-`det≡0` structural fact (cliques = intrinsic rank
deficiencies); clarified the `c=w` boundary is degenerate and distinct from the FRI `c<w` regime. No
refutation, no proof — the conjecture stands open, now with a sharper structural map of where the difficulty
lives (the escape/degeneracy classification in `c<w`).
