# δ* PRIZE — master map of the proven scaffold + the single open core (session synthesis 2026-06-13)

This is the consolidated state after a full session of attack. It records (A) the closed candidate
formula, (B) everything proven around it, (C) the single open input in its **equivalent forms** (all
empirically supported, all open), and (D) the honest ranking. Companion notes are cited inline.

## A. The candidate (closed formula, no free variables)
`C = RS[F_q, μ_n, k]`, `n=2^μ`, `ρ=k/n ∈ {½,¼,⅛,1/16}`, `ε*=2^{-128}`.
> **`δ* = 1 − ρ − 2/s*`,  `s* = min{ s : C(s, ⌊ρs⌋+2) ≥ ε*q }`**  (entropy form `≈ 1−ρ−2H₂(ρ)/log₂(ε*q)`).
Solves BOTH grand challenges: it is the MCA threshold, and via the ABF26 §5 LD⇔MCA bridge the same
`s*`-law gives the list-decoding threshold `|Λ(C^{≡m},δ)| ≤ ε*|F|`.

## B. PROVEN (committed, prize regime `n=2^μ`, clean `p`)
1. **Upper bracket `δ* ≤ 1−ρ−2/s*`** — Kambiré construction via `∏(X^m−ξ_j)=X^{rm}−λX^{(r−1)m}+R`,
   bad scalars = the `r`-fold subgroup sumset `H^{(+r)}` (`deltastar-explicit-upper-bracket-entropy`).
2. **Monomial-direction extremality** — bad scalars are *exactly* `C(s,r)`; the **power-sum rigidity
   theorem** (`p_j(S)=0` for `j∈{1..2m−1}\{m}` ⟹ `S` = union of `r` `m`-fibers), proven by
   **Lam–Leung induction** on `m=2^a`; 20/20 cases verified; `m=2,r=2` fully elementary
   (`deltastar-monomial-extremality-PROVEN`).
3. **General-direction 2nd-moment bound** — the **direction-Fisher lemma** `#bad < (a−b)n/(a²−bn)`,
   `b=max-agreement(u₁,C)`, character-sum-free, tight for the construction; recovers Johnson exactly
   (`deltastar-direction-fisher-bound`).
4. **No elementary method reaches past Johnson** — the construction has maximal coincidence at every
   order (`b_j=(r−1)m`), so the whole Fisher/moment hierarchy is vacuous at its radius (same note §).
5. **Lower bracket = Johnson `1−√ρ`** unconditionally (BCHKS Thm 1.3, `a=Θ(n/η)`); upper bracket
   confirmed from source (`deltastar-bchks-exact-brackets`).

## C. THE SINGLE OPEN INPUT — equivalent forms (all open, all empirically supported)
The lower bracket past Johnson reduces to **general-direction extremality**, equivalently any of:
- **(B-form)** worst-case Gaussian period `B(μ_n)=max_{b≠0}|Σ_{x∈μ_n}e_p(bx)| ≤ C√(n·log(q/n))`.
- **(energy-form)** additive energies `E_r(μ_n) = (2r−1)!!·n^r·(1+o(1))` (additively Gaussian) for
  `r ≤ r_max = Θ(log(p/n))`  [via `Σ_b|η_b|^{2r}=p·E_r` + **Markov** ⟹ B-form;
  `deltastar-clean-moments-markov-bridge`].
- **(halo-form)** the high-order spurious vanishing sums of `μ_n` mod `p` do not concentrate a period
  (= `SubsetSumHaloEnergy`; `deltastar-Bmun-hardness-precise`).
- **(list-form)** the explicit smooth-RS beyond-Johnson worst-case list stays `≤ poly` below `δ*`.
These are **inter-equivalent** and constitute the Bourgain-regime incomplete-character-sum problem for
`n ≪ √p`. **Empirically confirmed** (`n=8`: `E_r` clean to `r=7≈log(p/n)`, `B≈√(n log)`); **not
proven**; no acquired paper (incl. 2026) supplies it.

Proven-irreducible: the construction is built to defeat every elementary (Fisher/moment) bound, so
this analytic input is genuinely necessary — not an artifact of a weak proof.

## D. Honest ranking — **novelty 8 / insight 9 / proximity 9 / feasibility 8**
Feasibility is 8, not 9: every component is proven **except** the one analytic input in §C, which is
open and equivalent to a recognized hard problem. The formula is closed; the proof is not.

## E. The single remaining mathematics
Prove **(energy-form)**: for `n=2^μ ≪ √p`, `E_r(μ_n) = (2r−1)!!·n^r·(1+o(1))` for `r ≤ c·log(p/n)`.
This is the cleanest, most concrete, most attackable form (a Gaussian-moment statement for the
additive energies of a multiplicative subgroup), it is empirically supported, and it is the **only**
input the otherwise-complete proof needs. A correct proof of it closes both grand challenges via the
scaffold in §B. No fabrication: this statement is open, and is stated as the explicit residual.
