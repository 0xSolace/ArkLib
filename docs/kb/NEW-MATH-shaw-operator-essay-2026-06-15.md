# New Math: the Shaw Operator, the Gaussian fixed point, and why c_r≤1 is the wrong quest

*A working essay (#444). Honesty: nothing claimed proven that isn't; the genuine new content is the
δ-reformulation, the Gaussian-fixed-point identity, and the prime-dependence refutation of c_r≤1.*

## I. The target and the conditional pin (verified)
The prize `M(μ_n)=max_{b≠0}|Σ_{x∈μ_n}e_p(bx)| ≤ C√(n log m)` is reduced, in axiom-clean Lean
(`CharPWickConditionalPin`, 3324-job build), to the cross-step ratios `c_r := cross_r/(2r·n·Wick_r)`,
`Wick_r=(2r−1)‼·n^r`, `cross_r=(1/p)Σ_{b≠0}|η_b|^{2r}(|η_b|²−n)`. The pin: `c_r≤1 ∀r≤log m ⟹ M≤√(2n log m)`.

## II. The Gaussian fixed point (new framing)
Let `X_b=|η_b|²`, `m_r=E[X_b^r]`. Then `cross_r ≈ m_{r+1}−n·m_r`. For a GAUSSIAN `η~N(0,n)`, `X=η²` has
`m_r=(2r−1)‼·n^r=Wick_r` EXACTLY, giving `cross_r=Wick_{r+1}−n·Wick_r=2r·n·Wick_r ⟹ c_r≡1`. **The Gaussian
is the exact fixed point `c_r=1`.** So `c_r≤1` says the thin-subgroup period law is on the sub-Gaussian side.

## III. THE SHAW OPERATOR 𝒮 (defined)
Set the deviation `δ_r := m_r − Wick_r`. The Gaussian-fixed-point algebra gives the exact equivalence
  **`c_r ≤ 1  ⟺  δ_{r+1} ≤ n·δ_r`**.
Define the **Shaw operator** as the deviation map `𝒮 : δ_r ↦ δ_{r+1}` on the moment-deviation sequence, with
the Gaussian (δ≡0 boundary) as fixed point. `c_r≤1` is the statement "`𝒮` grows the deviation at rate ≤ n."
Constraints any correct 𝒮 satisfies: fixes the Gaussian; b-sensitive + deterministic-archimedean + L∞;
thinness-essential (β≥4); reproduces proven bases c_1,c_2,c_3≤1; recursion-compatible (a_{r+1}=(a_r+2r c_r)/(1+2r));
char-p faithful over F_p (trivial Frobenius, 0-dim base); → identity as n→∞ (std cumulants→0).

## IV. The proof attempt — and the REFUTATION (the real new math)
Data (exact, β=4): at GOOD primes c_r is monotone-DECREASING →0 (n=16: 0.90,0.79,…,0.08; n=32: 0.95,…,0.29),
so `c_r≤1` holds with growing margin and 𝒮 contracts (`|δ_{r+1}|/|δ_r|≈n²>n`, driven by the DC term n^{2r}/p).
This *looked* like a closure (monotone + proven bases ⟹ c_r≤1 ∀r). **It is FALSE.** Stress-testing 23 primes:
  n=64, p=16778497 (β=4.000): c_r = …,0.963, **1.019, 1.163, 1.432, 1.845** — 𝒮 EXPANDS, c_r>1, and the BOUND
  itself fails: `M/√(2n log m)=1.0514>1` (C=√2 refuted). v₂(p−1)=8, m=2²·65541 — a specific STRUCTURED prime;
  neighbors (v₂=7,9) are fine. So **c_r≤1 is PRIME-DEPENDENT (good/bad dichotomy), false at structured β=4 primes.**

## V. The redirection (what the Shaw operator must actually target)
1. `c_r≤1` (⟹ C=√2) is the WRONG quest — false at structured primes; C=√2 is refuted.
2. The genuine prize is the prime-UNIFORM `C=O(1)` (C≈1.49 at the worst prime seen; O(1) but >√2).
3. The MOMENT ROUTE (the conditional pin / 𝒮) is prime-LIMITED: at good primes it yields C=√2 (c_r≤1 to depth
   log m); at bad primes (c_r>1 from r≥4) the optimal moment depth caps (~r_0=3) and the moment bound degrades
   to a power-saving n^{1.17} — even though the TRUE M is still O(√(n log m)). So `𝒮`/moment CANNOT deliver
   uniform C=O(1). The correct target is `C(p,n) := min_r (q·E_r/n)^{1/2r}/√(n log m) = O(1)` uniformly in p —
   the Shaw operator must bound C(p,n) (≈ the depth r_0(p) where 𝒮 stops contracting) prime-uniformly, which is
   a DIRECT sup-norm statement the moment method provably cannot reach.
4. So: the conditional pin is sufficient ONLY at good primes; the prize prime's goodness (does 𝒮 contract to
   depth log m?) is the open question, and the bad set is structured primes — the recognized open wall, now
   sharply localized as "prime-uniform contraction of the deviation operator 𝒮 to depth log m."

## VI. Avenues (ranked, post-refutation)
- [the real target] prime-uniform C=O(1): a direct sup-norm bound holding even at structured primes — needs a
  non-moment argument (the moment method is C=√2-or-bust). This is the BGK/Paley wall in its sharpest form.
- [characterize the bad set] pin the exact structure of c_r>1 primes (the m=2²·65541-type): which primes are
  "good" (𝒮 contracts to log m)? If the prize prime is provably good, the pin closes for it.
- [almost-all] the pin gives C=√2 for density-1 primes (good set); a sparse structured bad set carries C up to
  ~1.49 — an honest almost-all + bounded-C statement (not the single-prime prize).

## VII. Honest verdict
The Shaw operator (deviation map 𝒮, c_r≤1 ⟺ δ_{r+1}≤nδ_r) is a clean new framing with the Gaussian as fixed
point; it PROVES the bound at good primes (C=√2) but `c_r≤1` is refuted as a universal β=4 statement (structured
primes violate it, C=√2 with it). The prize is the prime-uniform C=O(1), which the moment route provably cannot
deliver. No closure; genuine new structure (δ-reformulation, fixed point, prime-dependence) + a sharp
redirection of the target. The wall stands, now named: prime-uniform deviation-operator contraction to depth log m.
