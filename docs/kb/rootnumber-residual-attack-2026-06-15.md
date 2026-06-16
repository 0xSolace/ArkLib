# Root-Number-Flatness Residual (#444): Synthesis & Honest Verdict

**Object.** The prize bound `M(n) ≤ C√(n log m)` is, by the exact Fourier-duality identity
`DFT_m(ε(χ_·))[β] = m·η_β` (verified ≤1e-11), equivalent to the **L∞ spectral flatness** of the
Dirichlet root-number sequence `s_k = ε(χ_k) = g(χ_k)/√q`, `k ∈ Z/m`, over the n-th-power-character
family (`m=(p−1)/n`, `n=2^μ`, prize `m≈2^128`): `max_{β≠0}|DFT_m(s)[β]| ≤ C√(m log m)` at **FIXED q**.

**Proven brick (in-tree, axiom-clean):** the sequence has conjugate symmetry `s_{m−k}=conj(s_k)`
(from `χ_k(−1)=+1`) ⟹ the DFT is REAL. (Correction from the probes: the right statement is
conjugate-symmetry `s_{m−k}=conj(s_k)`, NOT the additive `θ_{−k}=−θ_k` — the latter fails
numerically at 2.0; this corrects the CONTEXT phrasing.) The residual is the post-symmetry L∞ bound.

Ten mechanisms (+ two all-other sweeps) were developed and numerically probed against exact Gauss
sums. **Independent re-verification this session** (from-scratch numpy, discrete-log Gauss sums,
proper μ_n, n∈{8,16}, p up to 7681): all load-bearing identities reproduced — `unit_err~1e-16`;
DFT-flatness `Fmax/tgt = 1.05–1.26`; the Jacobi autocorrelation identity EXACT to `1e-15`; Weil
vacuity ratio `weil/need = 3.0–8.8` **diverging** with m.

---

## 1. Did any approach give fixed-q, non-circular flatness (unconditional or conditional-on-standard)?

**No approach gives an UNCONDITIONAL fixed-q flatness bound.** Ranked by what they DO deliver:

| Rank | Approach | fixed-q | non-circ | L∞? | Best status |
|---|---|---|---|---|---|
| 1 | **phase-sidon-energy** (Jacobi autocorrelation) | ✓ | **✗ (circular)** | yes-but | EXACT reduction to `max_χ|Σ_{ζ∈μ_n}χ(1+ζ)|`; **CONDITIONAL on subconvexity** for that short subgroup-shift sum. Cleanest new face. |
| 2 | **metaplectic-theta** | ✓ | ✓ | yes-but | Same autocorrelation reduction; honest CONDITIONAL on subconvexity. m=2 provably flat (trivial). |
| 3 | **weil-index-hilbert** | ✓ | ✓ | no | NEW exact lemma (HD 2nd-difference = explicit Jacobi phase) but reduces to Katz-vacuous. |
| 4 | **kronecker-gamma** | ✓ | ✓ | no | Quadratic Stirling term removable, shaves CONSTANT ~30%, does NOT change the order. |
| 5 | **grh-conditional** | ✓ | ✓ | no | **GRH proven IRRELEVANT** (Pearson(arg ε, |L(1/2,χ)|)=0.0000): GRH does not bite the object. |
| 6 | **large-sieve** | ✓ | ✗ | L²-only | Parseval pins RMS=√m exactly; L²→L∞ step IS the deep moment at depth log m (dead). |
| 7 | **stationary-vandercorput** | ✓ | ✓ | no | Premise FALSE: Δ²θ_k is uniform-on-circle (var π²/3), maximally non-smooth. |
| — | sweep-other-1/2 (PFR-digits / CRT / spectral-gap / dual-Weil) | ✓ | mostly ✗ | no | All empty or circular; one new datum (root-number Walsh-quasirandomness). |

**Legitimate conditional result achieved (real, not larp):**

> **THEOREM (conditional).** Subconvexity / a Burgess-beyond-`p^{1/4}` bound for the short
> multiplicative character sum `max_χ |Σ_{ζ∈μ_n} χ(1+ζ)| ≤ C√(n log m)` over the thin subgroup-shift
> `1+μ_n` ⟹ the prize bound `M(n) ≤ C√(n log m)` ⟹ root-number L∞ flatness at fixed q.

This is a genuine "prize follows from X" statement with X a standard-named open conjecture (the
Paley Graph Conjecture / subconvexity for these sums). It is **fixed-q** and the reduction step is
exact and Lean-formalizable. It is NOT a closure (X is open) and NOT independent of the recognized
wall — but stating the prize as conditional on a NAMED conjecture is a legitimate deliverable.

---

## 2. The MOST PROMISING — phase-autocorrelation → Jacobi-sum (assessed hardest)

**Does A(h) genuinely become a Jacobi-sum phase sum? YES — exactly.** This is the strongest finding,
and it survives the hardest scrutiny as a mathematical IDENTITY:

- `g(χ)conj(g(ψ)) = ψ(−1)·J(χ,ψ̄)·g(χψ̄)`, and `χ_k(−1)=+1` for every n-th-power character ⟹ the
  sign drops. With `χ_{k+h}χ̄_k = χ_h` fixed:
  `A(h) = Σ_k s_{k+h}conj(s_k) = s_h · Σ_k (J(χ_{k+h},χ̄_k)/√q)`.
- The Jacobi average collapses (geometric-sum orthogonality `Σ_k χ_1(y)^k = m·1[y∈μ_n]`) to:
  **`|A(h)| = (m/√q)·|Σ_{ζ∈μ_n} χ_1^h(1+ζ)|`** — verified `1e-15` this session across all primes.

**Is THAT bounded/tractable? NO unconditionally.** Three structural escape-hatches the route was
designed to test are all REFUTED with hard numbers:

1. **Geometric/arithmetic-progression structure: ABSENT.** Jacobi-phase increments
   `θ_J(k+1)−θ_J(k)` have std ≈1.8–2.5 rad — not a closable progression.
2. **Sidon set: NO.** Max phase-difference multiplicity grows ≈m (not O(1)); the sequence is not a
   Sidon set, so no additive-energy collapse.
3. **Weil/Deligne on the Jacobi average: VACUOUS.** `Σ_{ζ}χ(1+ζ) = (1/m)Σ_j J(χ_1^j,χ)`; Weil gives
   only `√p`. The ratio `√p / √(n log m)` is `3.0–8.8` in my probe and **DIVERGES monotonically**
   (= `√(m/log m) → ∞`), the Burgess barrier `n ≈ p^{1/4}`. At the prize `β≥4`, `n ≤ p^{1/4}`, so
   even Burgess is vacuous; only subconvexity remains.

**Verdict on the cleanest lever.** The reduction is EXACT, NEW-to-state cleanly, and
Lean-formalizable (it is the in-tree `_RootNumberAutocorrelation.lean` step 2, re-confirmed to
1e-15). But it is **CIRCULAR in the way that matters**: `Σ_{ζ∈μ_n}χ(1+ζ)` is the *multiplicative
dual* of the same thin-subgroup √-cancellation object `M(n)` — same wall, new name. The object
`|S(h)|/√n = 1.9–3.3` tracks √(log m) above √n with no algebraic margin (random-like). So the route
is a **legitimate conditional-on-subconvexity result and the cleanest dual face**, but not an escape.

---

## 3. Why each failing approach fails (precise reason)

- **large-sieve** — *L²-only.* Dual large sieve = Parseval = `Σ|F|²=m²` exactly (RMS=√m, blind to
  the log). The L²→L∞ step is Halász at depth r~log m = the deep-moment/additive-energy statement,
  DEAD at structured primes. r=2 (the only free level) gives `m^{3/4}`, diverges by `m^{1/4}/√log m`.
- **weil-index-hilbert** — *Katz-vacuous.* HD telescope leaves Θ(m) free orbit phases (not O(log m));
  the max is carried by HIGH-order chars outside the 2-power Weil tower; the dual is over thin `1+μ_n`
  ⟹ only the vacuous Weil √p. (NEW exact lemma: HD doubling 2nd-difference = explicit Jacobi phase.)
- **stationary-vandercorput** — *premise false.* `Δ²θ_k` is uniform-on-circle (var π²/3), maximally
  non-smooth, growing MORE random with n; consistent with Katz equidistribution. No smooth part.
- **kronecker-gamma** — *constant-only.* Quadratic Stirling/Lerch term is removable but the log-log
  scaling exponent is unchanged (0.640 full vs 0.648 residual); shaves ~30% constant, not the order.
- **grh-conditional** — *GRH does not bite.* `Pearson(arg ε, |L(1/2,χ)|)=0.0000` exactly: the
  root-number phase is the functional-equation CONSTANT, orthogonal to all GRH-controlled data
  (|L|, zeros). The relevant hypothesis is subconvexity/Burgess, NOT GRH. GRH⇒flatness is FALSE.
- **metaplectic-theta** — *no archimedean structure for m≥3 / circular.* The Weil quadratic-exponential
  fit captures no more than a random odd null (excess −0.8 sd) and decays with m; matches the in-tree
  Gross-Koblitz no-go (Γ_p unit has no archimedean shadow for m≥3). Reduces to the same autocorrelation.

---

## 4. The all-other sweep — any fresh non-archimedean angle survive?

**No survivor.**
- **PFR/GGMT over root-number index digits (F2^t):** at prize-shaped β=4 (Fermat n=16, m=4096) the
  root-number phase is **Walsh-QUASIRANDOM** in its 12 index bits (degree-mass tracks binomial ±0.01).
  This is a genuinely new datum and independently closes the PFR-over-digits hope on the index side
  (no low-degree structure for an inverse theorem to grab) — but quasirandomness is what flatness
  NEEDS, not a PROOF of it.
- **CRT factorization of the autocorrelation:** VACUOUS at the prize (m=2^128 is a prime power);
  the autocorrelation does not factorize even for composite m (tensor bound 100–200× lossy).
- **Jacobi-sum spectral-gap operator:** gapless, perfectly unimodular (`|J|=√p`), full-rank = the
  in-tree C47/C27 unimodular-cocycle no-go (pins only L²/Johnson). Circular.

---

## 5. Honest bottom line

This **confirmed the wall** for an unconditional bound, and **delivered one legitimate
conditional-on-standard-conjecture result** plus a clean new exact reduction.

- **Genuine path opened? Unconditional: NO.** Every route reaches the recognized thin-subgroup
  √-cancellation wall (Paley Graph / BGK `n^{1−o(1)}` → the half-power gap at the Burgess barrier).
- **Conditional-on-named-conjecture: YES (legitimate).** Subconvexity (equivalently the Paley Graph
  Conjecture) for `max_χ|Σ_{ζ∈μ_n}χ(1+ζ)| ≤ C√(n log m)` ⟹ the prize. GRH is proven IRRELEVANT
  (orthogonality measurement), so this is the CORRECT conditional hypothesis, not GRH.
- **Cleanest NEW reduction (valuable even though not a closure):** the EXACT autocorrelation collapse
  `A(h) = s_h·(m/√q)·Σ_{ζ∈μ_n}χ_1^h(1+ζ)`, machine-verified to 1e-15. It (a) explains WHY the
  arithmetic phases "look random with diffuse extra" — they ARE M(n) in a Fourier hat; (b) supplies a
  Lean-formalizable lemma; (c) relocates the prize to a *multiplicative* short character sum (the
  Burgess/subconvexity object) rather than the additive period — a cleaner dual face for any future
  subconvexity input to attach to.
- **Two corrections logged:** (i) the real-DFT brick is conjugate-symmetry `s_{m−k}=conj(s_k)`, not
  additive `θ_{−k}=−θ_k`; (ii) GRH is the WRONG conditional hypothesis (Pearson=0); subconvexity is right.

No larp: identities are exact and independently re-verified; the verdict is an honest negative for an
unconditional escape with a real conditional-on-subconvexity deliverable.
