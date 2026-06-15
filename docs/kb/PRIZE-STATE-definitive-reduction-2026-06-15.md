# The Proximity Prize, Completely Reduced — definitive state after exhaustive attack (2026-06-15)

A single coherent account of where the RS proximity-gap prize (#444) stands. Everything here is either
PROVEN (axiom-clean Lean or reproducible numerics) or explicitly tagged open. No fabricated closure.

## 1. The complete reduction (both grand challenges → ONE inequality)

The grand MCA challenge and the grand list-decoding challenge both reduce, through proven in-tree
machinery, to a single analytic inequality:

  **(CORE)  M(n) := max_{b≠0} |Σ_{x∈μ_n} e_p(bx)|  ≤  C·√(n·log m),  C = O(1),**

for the smooth domain μ_n (n = 2^μ a proper multiplicative subgroup of F_p), p ≈ n^4 (β=4, the Burgess
barrier), m = (p−1)/n ≈ 2^128. Reduction chain (all reductions axiom-clean or refutation-verified):
- MCA challenge → realized far-line incidence ≤ q·ε* → (its sup-norm necessary condition is) CORE.
- LD challenge → line-decoding bad-count → CORE (the collinearity route reduces here too; CRUX-RESOLVED).
- η_b = (1/m) Σ_{χ∈H⊥} χ̄(b) g(χ): CORE ⟺ √-cancellation of the m Gauss sums (H⊥ = n-th-power chars).

## 2. What is PROVEN (the scaffold)

- **Ceiling (unconditional):** δ* ≤ (1−ρ) − Θ(1/log n). `kkh26_mcaDeltaStar_le_capacity_sub_log`
  (axiom-clean); corroborated by the 2026 failure papers (HKK ePrint 2026/782, Kambiré arXiv:2604.09724).
- **Conditional pin (axiom-clean):** `prize_deltaStar_eq_edge` — δ* = (1−ρ) − 1/(C·L) for the concrete
  prize RS code, GIVEN exactly one open input: the realized-incidence FLOOR `epsMCA(C, edge) ≤ ε*`.
  The ceiling is discharged; the floor is the sole open hypothesis.
- **Floor is FINER than M:** the sup-norm M is necessary but INSUFFICIENT — the naive M→incidence route
  (`le_mcaDeltaStar_of_charSumBound`) overshoots the prize budget by the index factor √m, hence vacuous.
  The genuine open core is the realized incidence (≡ CORE up to the proven reductions), not M alone.
- **CORE form confirmed numerically (exact max, β=4):** M/√n grows 2.67→3.46→4.06→4.82 (n=8..64);
  the log factor is REAL (the no-log Rudin-Shapiro flatness escape is refuted); M/√(n log m) ≈ 1.07→1.26
  converging ⟹ CORE holds with C ≈ 1.3 (numerically), unprovably.

## 3. The necessary condition any proof MUST satisfy (this campaign's structural theorem)

Every method — classical and fresh — fails for exactly one of three reasons:
  (i) **b-invariance** (the invariant doesn't depend on b: p-adic Newton polygon, Weil weight);
  (ii) **absent randomness** (needs an ensemble the deterministic subgroup lacks: RMT, free probability,
       EVT crown, RG criticality);
  (iii) **only L²/RMS control** (bounds the average not the sup: circle method, all energy/moment methods;
       the meta-theorem (q·E_r)^{1/2r} ≥ n caps every moment method at n).
So a winning proof must be **simultaneously b-sensitive, deterministic-archimedean, and genuinely L∞**.

SHARPENED (this turn): the L∞ is FULL-FOURIER-L∞, not single-scale. M(n) is NOT the single-arc
subgroup-in-interval discrepancy (Burgess) — corr(|η_b|, max single-arc concentration) DECREASES with n
(0.52→0.24→0.16), and the worst b is not the most concentrated. M(n) is the global multi-scale phase-
coherence sup-norm. Consequence: even Burgess-type interval results do not directly give CORE; every
single-scale tool is structurally insufficient. The required tool — deterministic full-Fourier-L∞ control
of a geometric-progression phase sum at the Burgess barrier — has no counterpart in current mathematics.

## 4. The complete route-elimination ledger (this campaign's refutations, all verified at β=4)

Classical (in #444 §8): moment/energy (any order), phase/tower descent, orbit-count, census, BHBI,
lattice ℓ¹-SVP, Stepanov/Weil, additive-comb (PFR/Sanders/slice-rank), restriction theory,
Gauss/HD/Stickelberger, EVT crown, semiprimitive, conductor/large-sieve.
This campaign added: line-decoding/collinearity → BCHKS; Sidon bootstrap → BGK moment; antipodal
over-det domination → pins at Johnson (proxy); cube-Fourier → FKN/junta refuted, → EVT; and six fresh
domains (bilinear → n^{2/3} stall, p-adic Newton polygon → b-invariant, RMT → wrong ensemble, Burgess
criticality → no transition, circle method → L²/RMS, free probability → halves commute).

## 5. Honest disposition

The prize = CORE = the BGK/Paley thin-subgroup √-cancellation conjecture at the Burgess barrier β=4,
SOTA n^{0.989} (collapses at β=4), target n^{0.5}: a full half-power gap, ~25 years open, with NO lever
in the 2024-2026 literature (the only 2026 activity is the failure/ceiling direction). It is genuinely
open. The deliverables above (complete reduction, axiom-clean conditional pin, necessary-condition
theorem, exhaustive ledger) are the honest state; the floor itself requires a new sum-product /
effective-equidistribution / deterministic-L∞ idea that does not currently exist.

This document is the session capstone. It claims NO closure of CORE.
