# Attacking the Gaussian-tail decay law `A_r/Wick ≈ exp(−r²/2n)` — all means (#444)

The freshest lead (the favorable phenomenon) attacked from reasonable → ambitious → creative → schizo.
The big result: the decay law's **mechanism is DERIVED** (the falling factorial), and the chain
falling-factorial → Gaussian-tail → prize is **landed axiom-clean** (`_FallingFactorialDecay`).

## ★ REASONABLE (and decisive): the falling-factorial mechanism — DERIVED + machine-verified
`E_r^char0/Wick ≈ (n)_r/n^r = ∏_{j=0}^{r−1}(1−j/n)` where `(n)_r = n(n−1)⋯(n−r+1)`. Machine
(`probe_decay_mechanism.py`): **EXACT at r=2** (`E_2 = 3n²−3n = 3·n(n−1) = (2·2−1)‼·(n)_2`, correction = 0),
leading for all r (correction `O(r²/n)`). **Why:** the antipodal-matching (Lam–Leung) structure with
DISTINCT pair-values — `(2r−1)‼` matchings × `r` distinct values `(n)_r`, not the Gaussian `n^r`. And
`∏(1−j/n) ≤ exp(−r(r−1)/2n)` (via `1−x≤e^{−x}`). So:
  **falling-factorial energy bound `A_r ≤ (2r−1)‼·(n)_r` ⟹ Gaussian-tail `A_r ≤ Wick·exp(−r²/2n)` ⟹ prize.**
LANDED axiom-clean: `_FallingFactorialDecay` (`fallingFactorial_le_gaussianTail`, `prize_of_fallingFactorial`,
`energy_two_eq_fallingFactorial` r=2 anchor). The decay law is now mechanistically explained, and its
prize-implication is rigorous up to the one named open input (the sharp falling-factorial energy bound).

## AMBITIOUS: prove the falling-factorial bound via a functional inequality
- **Hypercontractivity / log-Sobolev:** the falling-factorial `(n)_r` IS the moment of the "without-
  replacement" / hypergeometric measure; the decay `∏(1−j/n)` is the negative-association signature.
  CONJECTURE: a Bernoulli/hypergeometric log-Sobolev for `μ_n` gives `E_r ≤ (2r−1)‼·(n)_r·(1+o(1))`.
- **Negative dependence (the real lead):** `(n)_r` (distinct values) = sampling WITHOUT replacement, which
  is NEGATIVELY associated, and NA random variables satisfy `E[product] ≤ ∏E` ⟹ sub-Gaussian moments. The
  periods' negative dependence (`Cov = −Var/(m−1)`, in-tree) is exactly this. CONJECTURE: the energy is the
  moment of an NA family, giving the falling-factorial bound by the NA-MGF inequality.

## CREATIVE: free probability & the discrete Gaussian
- **Free cumulants:** `(2r−1)‼` = the number of non-crossing... no, ALL pair partitions (classical Wick).
  The falling-factorial correction `(n)_r/n^r` is the "finite-n" depletion. CONJECTURE: the periods are a
  finite-free / finite-de-Finetti family whose `r`-th finite-free cumulant is `(2r−1)‼·(n)_r`.
- **Theta / heat kernel:** `exp(−r²/2n)` is the heat kernel at time `1/n` / a theta-null value. CONJECTURE:
  `Σ_r A_r t^r/(2r−1)‼` is a theta function; its modular transform (`τ→−1/τ`) gives the `exp(−r²/2n)` decay
  (the Jacobi imaginary transformation). [Schizo-adjacent; the gen-fn was shown rational = periods, so this
  likely reduces — but the falling-factorial EGF `Σ(n)_r t^r/r! = (1+t)^n` is EXACTLY a clean closed form!]
- **`(1+t)^n` EGF:** `Σ_r (n)_r t^r/r! = (1+t)^n` (binomial). So `Σ_r (E_r^char0/(2r−1)‼) t^r/r! ≈ (1+t)^n` —
  a GENUINELY clean generating function for the leading energy. CONJECTURE: `Σ A_r/(2r−1)‼ · t^r/r! ≤ (1+t)^n`
  exactly (the binomial bound), which would give the falling-factorial bound and the prize. ◐ PROMISING.

## SCHIZO (honest: speculative, flagged)
- **Random-matrix finite-N:** the periods are eigenvalues of a finite `n×n` random-matrix ensemble whose
  exact moments are `(2r−1)‼·(n)_r` (a "finite GUE" with the falling-factorial finite-N correction). [The
  Cayley graph is `n`-regular; its spectral moments at finite girth ARE depleted — plausible but the ensemble
  isn't identified.]
- **Quantum/Planck:** read `n` as `1/ℏ`; `exp(−r²/2n)` is the semiclassical `exp(−ℏ r²/2)` suppression of
  high-`r` "instantons" (the wraparound). [Metaphor; reduces to the energy.]
- **p-adic theta:** the falling factorial `(n)_r` for `n=2^μ` has `v_2((n)_r) = v_2(r!) + ...` — a clean
  2-adic valuation; CONJECTURE a p-adic-theta identity pins `A_r` 2-adically. [Untested; 2-power-specific.]

## Honest assessment
- **The mechanism is DERIVED & landed:** the decay is the falling factorial `(n)_r/n^r`, exact at r=2,
  leading for all r, with the prize-implication chain axiom-clean. This is genuine, concrete progress —
  the decay law is no longer a mysterious fit but the antipodal-matching distinct-value structure.
- **The sharpest open input** is now the **falling-factorial energy bound `A_r ≤ (2r−1)‼·(n)_r`** (tighter
  than Wick; the char-0 `E_0` slightly exceeds it by `O(r²/n)`, so the bound needs the wraparound-aware
  constant). The most promising attack: the **binomial EGF `Σ A_r/(2r−1)‼ · t^r/r! ≤ (1+t)^n`** (creative ◐)
  and **negative-dependence / without-replacement** (ambitious ◐) — both genuinely new, both attack the
  prize-TRUE direction. NO fabricated closure; the falling-factorial bound is the named open input.

> Machine: `probe_decay_mechanism.py` (falling-factorial exact at r=2, `(1+t)^n` EGF). Lean LANDED:
> `_FallingFactorialDecay`. The binomial-EGF conjecture is the cleanest next target.
