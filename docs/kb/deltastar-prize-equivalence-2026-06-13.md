# The prize is (R) ⟺ explicit-RS beyond-Johnson list-decoding — research synthesis 2026-06-13

Decisive literature + computational synthesis of where the proximity prize (δ* for smooth-domain
RS) actually stands, after the governing-law reduction to the far-line incidence (R).

## THE EQUIVALENCE (the prize is a recognized major open problem)

**Ben-Sasson–Carmon–Haböck–Kopparty–Saraf, "On Proximity Gaps for Reed-Solomon Codes"
(ePrint 2025/169), Theorem 1.9.** For `C = RS[F_q, D, k]`, `k=(1−δ)n`, with `τ = LDR(δ)+2/n`
(just past the list-`q` decoding radius): there exist `f,g:D→F_q` with
`|{z : Δ(f+zg, C) ≤ τ}| ≥ q/(2n)` yet `Δ([f,g], C²) ≥ 1−1/n`. **Consequence: improving the
proximity-gap (= line–ball incidence = our (R)) radius beyond Johnson for ANY RS code IMPLIES
list-decoding that code beyond Johnson with list ≤ q.** The two are equivalent.

- They **DISPROVE** the `n^γ`-bounded proximity-gaps conjecture for all `γ=O(1)`, and (with
  ePrint 2025/2046, Crites–Stewart) the **correlated-agreement-up-to-capacity (BCIKS) and
  mutual-correlated-agreement-up-to-capacity (WHIR) conjectures are FALSE**. The corrected
  statements go only up to the **list-decoding-capacity boundary** `H_q^{-1}(1−ρ)`, NOT the
  rate `1−ρ`.
- Their **negative constructions use the smooth-domain structure**: Thm 1.6 over F₂-linear
  domains; the prime-field limitations (§1.4.3, Conj 1.12) use multiplicative subgroups +
  sumset growth. **Smoothness of μ_n is currently a source of COUNTEREXAMPLES, not positive
  bounds** — a serious warning for any "(R) holds" hope.

**Kumar–Ron-Zewi survey (arXiv:2603.03841, 2026):** explicit beyond-Johnson list-decoding of
plain fixed-domain RS is "a major open problem" with ZERO positive results. Capacity is reached
ONLY by folded/multiplicity (subspace-design) or random/random-puncture RS. JH01/BSKR06 give a
partial LOWER-bound obstruction (some RS need large list strictly between Johnson and δ).

## THE THREE UNWORKED SURFACES ARE ALL VACUOUS (prize-regime arithmetic, n=q^{1/4}=2^32)

1. **Kong–Tamo point-variety incidence (arXiv:2408.10977).** Spectral (expander-mixing) bound
   `|I−|P||V|/q^d| ≤ q^{n/2}√(|P||V|)·…`. Two fatal mismatches: (a) `S_w` (image of a Hamming
   ball under H) is NOT a function-graph variety in their class; (b) a single `q`-point line vs
   a single target is the bound's worst case. The companion **Tamo (arXiv:2312.12962) Thm 5.1**
   IS the RS instantiation — and it tops out at **Johnson** `1−√R` (the error term is a
   domain-AGNOSTIC `√(|L||P|·Q)` quantity with NO character-sum factor, so it cannot exploit
   smoothness). Vacuous for (R) by ~`q^{10⁹}`.
2. **Finite-field Littlewood–Offord** for `γ↦wt(s₀+γs₁)`. Right shape, but all LO/small-ball
   results (Tao-Vu, Nguyen-Vu, Halász) need GENERIC coefficients; here `s₁` is near-code
   (structured) — the inverse-LO regime where anti-concentration FAILS. Needs a NEW
   direction-sensitive inverse-LO theorem. None exists.
3. **Intermediate deep-holes / sumset structure of μ_n.** The honest frontier (BCHKS Conj 1.12),
   but the character-sum technology is ~10⁸ orders too weak and currently yields counterexamples.

## CHARACTER SUMS AT THE PRIZE THRESHOLD ARE TRIVIAL

di Benedetto et al (arXiv:2003.06165) Thm 3.1: for `q^{1/2} > |H| > q^{1/4}`,
`B(H) ≤ |H|^{1−31/2880}`. At the exact prize boundary `|H|=n=q^{1/4}=2^32`: saves **0.34 bits**
(`2^{31.66}` vs `2^32`), and the theorem **degenerates exactly at `q^{1/4}`** (invalid below).
For `n < q^{1/4}` (larger fields q≈2^160) NO nontrivial single-character bound is known
(Heath-Brown–Konyagin / BGK barrier). The energy wall (`E ≲ n^{2.45}` MRSS, `n^{5/2}` HBK) is
2026-confirmed; nothing beats trivial for `n ≥ q^{2/3}`.

## MY COMPUTATIONAL FINDING (the structured adversary determines δ*, q-independently)

Faithful small smooth-domain RS (μ_n, exact list-decode each γ). Measured worst-case far-line
incidence / list profile, sweeping `q`:
- The structured (antipodal pencil `u₁=x^{n/2}` / nodal `x^k+γ/x`) adversary's δ* is
  **q-INDEPENDENT** (e.g. `a₂ = n/2+1` exactly at n=8 AND n=16, ρ=1/4; worst-case δ* identical
  across q ∈ {73…241} and {97…241}). Random directions sit at the trivial agreement `k+1`.
- The structured δ* sits **strictly between Johnson and capacity** (n=16: ρ=1/4 → δ*≈0.625 vs
  Johnson 0.5, capacity 0.75; similar at ρ=1/2,1/8,1/16). The gap to Johnson is a q-independent
  STRUCTURAL quantity — the concrete realization of the BCHKS counterexample mechanism on μ_n.

This confirms the corrected picture: **δ* is pinned by the explicit algebraic adversary's
list-decoding radius (q-independent, char-0), strictly below rate-capacity.** The "average-term"
conjecture `δ*=H_q^{-1}(1−ρ−log_q(1/ε*)/n)` is an UPPER bound on δ* that the structured adversary
does NOT achieve (worst < average by the structural gap) — consistent with BCHKS disproving the
capacity conjectures.

## HONEST STATE FOR THE PRIZE

The prize δ* = the explicit-μ_n-RS list-decoding radius for list ≤ `q·ε*=n` (BCHKS equivalence).
The closed form is the structured-adversary radius (computable, q-independent), but proving it is
the EXACT value (the optimality = nothing beats the algebraic family) IS the recognized open
problem, with the smooth structure currently giving counterexamples not bounds. No accessible
technique (incidence/spectral, energy/character-sum, LO) discharges it. The genuinely-new input
required: a direction-sensitive inverse-Littlewood–Offord / beyond-Johnson explicit-RS
list-decoding theorem. DO NOT fabricate closure.
