# Bourgain's Problem 5 & the prize: literature reading + gleaned ideas (2026-06-15)

**Question:** can we solve Bourgain's Problem 5, and what novel ideas does the literature offer for the
prize dual object `max_{χ} |Σ_{ζ∈μ_n} χ(1+ζ)| ≤ C√(n log m)`?

## What Bourgain's Problem 5 actually is (Gong 2014, from Chang's list [C, Problem 5])
> Obtain a nontrivial bound on `Σ_{x∈H} χ(x+a)` for `H < F_p*`, `|H| ~ √p`, `a ∈ F_p*`.
- Gong (arXiv:1401.4618) Thm 2: `max_a |Σ_{x∈H}χ(x+a)| < p^{1/2}` (Vinogradov bilinear) ⟹ power-saving
  `p^{-ε}|H|` ONLY for `|H| > p^{1/2+ε}`.
- **KEY: Bourgain's Problem 5 targets `|H|~√p`. The prize is `|H|=n≈p^{1/4}` — far THINNER and HARDER.**
  At `|H|=p^{1/4}`, Gong's `p^{1/2}` bound is WORSE than the trivial `|H|` — useless. So the prize is a
  strictly harder cousin, not Bourgain's Problem 5 itself. Solving the prize ⟹ solving (a hard case of) it.
- Status of Problem 5 proper (`|H|~√p`): solved (Gong/Vinogradov, marginal); power-saving for `|H|>p^{1/4+ε}`
  (Konyagin/BGK). The THIN `|H|≤p^{1/4}` + SQUARE-ROOT-cancellation case (= prize) is OPEN; no 2024–2026
  breakthrough; expository BGK account arXiv:2401.04756.

## Ideas gleaned (and honest transfer assessment)

1. **Alon–Bourgain "Additive Patterns in Multiplicative Subgroups"** — a subgroup of size `≥ q^{3/4}` MUST
   contain `x+y=z`, but sum-free subgroups of size `Θ(p^{1/3})` exist. Since `|μ_n|≈p^{1/4} < p^{1/3}`, μ_n
   can be **sum-free / Sidon-like** ⟹ clean structural confirmation of the in-tree `E_2(μ_n)=3n²−3n`.
   TRANSFER: controls r=2 only; deep `r≈log m` energy is uncontrolled (the wall). Not an escape.

2. **Shkredov–MacCourt–Shparlinski (arXiv:1701.06192)** — collinear-triples / multiplicative-energy bound
   to beat Weil `max_i k_i · p^{1/2}` for SPARSE (trinomial) sums via arithmetic of the exponents.
   TRANSFER: our `χ(1+ζ)` over `ζ^n=1` is sparse-structured, but the energy→sum step loses a √ (fatal for
   the `√n` target ⟹ sub-Johnson). Confirms the √-loss barrier; not an escape.

3. **Gong mean-value estimates** — the AVERAGE over shifts `a` is small ("suggests extremely short sums
   exist"). TRANSFER: average ≠ worst-case sup (matches in-tree 2nd-level Parseval: average √, sup wall).

4. **Gorodetsky–Kovaleva 2024 (arXiv:2307.01344) — THE freshest, most aspirationally-relevant.** They push
   equidistribution of `Tr(g^k)`, `g∈GL_n(F_q)`, from the classical Montgomery–Vaughan depth `log k=o(n)` to
   **`log k=o(n²)`** — going FAR beyond GRH — by reducing to function-field character sums and exploiting a
   **special symmetry** (Lemma 3.8: `Σ_f Λ(f)χ_{k,ψ}(f)` depends on `k` only via `k'=gcd(k,q^n−1)`, since
   `x↦x^k` and `x↦x^{gcd}` share image/kernel; improving Weil `q^{n/2}k → q^{n/2}gcd(k,q^n−1)`).
   WHY IT MATTERS: "extend cancellation depth via a symmetry" is EXACTLY the prize's unmet need (deep-moment
   char-p transfer at depth `r≈log q`, where the campaign's Montgomery–Vaughan attempt (wf-NB) failed).
   HONEST TRANSFER VERDICT: (a) it is an AVERAGE/family result (over g / monic f), not a worst-case sup, so
   it lands on the campaign's already-mapped "average is fine, worst-case is the wall" side; (b) the specific
   gcd-symmetry is about the POWER MAP `x↦x^k`, not character powers `χ_1^t` (distinct t = distinct
   characters, no gcd-collapse); (c) the Galois-orbit reframing it suggests — the m autocorrelations
   `A(t)=Σ_ζ χ_1^t(1+ζ)` group into `~log m` orbits by character-order, each a Galois orbit whose HOUSE is
   the max — is a clean new structural view, BUT the worst case (primitive χ, order m) is exactly where the
   gcd-symmetry gives NO improvement. So G-K is the right SHAPE ("symmetry extends depth") but the specific
   tool does not transfer to the worst-case number-field sup-norm. Aligns with in-tree "HD+reflection = the
   complete archimedean relation set."

## Net
Bourgain's Problem 5 is real, named, and heavily researched (BGK, Konyagin, Bourgain–Garaev, Gong, Shkredov,
Shparlinski, MacCourt); the prize is its THINNER, HARDER cousin (`p^{1/4}` vs `√p`, square-root vs power-
saving). The literature reading gleaned clean confirmations (Sidon-ness, √-loss, average-vs-sup) and one
genuinely fresh 2024 technique (G-K symmetry-extends-depth) whose SHAPE matches the prize's need but whose
specifics are average-case and do not transfer to the worst-case sup-norm. No idea escapes the wall.
The one aspirational lead worth keeping: find a symmetry of the prize's deep-moment / autocorrelation that
extends the energy bound past depth `log n` for the PRIMITIVE (worst-case) character — the G-K analog the
campaign has not produced (and HD/reflection completeness suggests may not exist archimedean-ly).

Sources: arXiv:1401.4618 (Gong), arXiv:1701.06192 (Shkredov–MacCourt–Shparlinski), arXiv:2307.01344
(Gorodetsky–Kovaleva), Alon–Bourgain "Additive Patterns in Multiplicative Subgroups", arXiv:2401.04756
(BGK expository), Shparlinski "Open Problems on Exponential and Character Sums".
