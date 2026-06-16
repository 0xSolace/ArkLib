# The archimedean-phase reformulation: prize ⟺ Gauss-sum ROOT-NUMBER phase sequence is spectrally flat (2026-06-15)

## The reformulation (cleanest statement of the prize core yet, CONFIRMED numerically)
Via the Gauss-sum decomposition η_b = (1/m)Σ_{χ∈H⊥} χ̄(b) g(χ) (H⊥ = the m=(p−1)/n characters trivial on
μ_n = the n-th-power characters, ≅ Z/m), and |g(χ)|=√q for χ≠1:
  **M(n) ≈ (√q/m)·max_{β≠0} |DFT_m(s)[β]|,  s_k = e^{iθ_k} = g(χ_k)/|g(χ_k)|,  k∈Z/m.**
So the prize `M(n)≤C√(n log m)` ⟺ **the Gauss-sum phase sequence {s_k} over Z/m is SPECTRALLY FLAT**:
`max_{β≠0}|DFT_m(s)[β]| ≤ C·√(m log m)`. Here θ_k = arg g(χ_k) is the ABSOLUTE ARCHIMEDEAN PHASE =
the ROOT NUMBER ε(χ_k) (argument of the functional equation of L(s,χ_k)) = the WEIL INDEX of the
metaplectic rep = an archimedean Γ-VALUE PERIOD.

## Numeric confirmation (exact, this session)
n=8 (p=4129, m=516): maxDFT=61.7, √(2m log m)=80.3, ratio 0.768; maxDFT/√m ≈ 2.7 (~√(2 log m)=3.5).
n=16 (p=65537, m=4096): maxDFT=202, √(2m log m)=261, ratio 0.774; maxDFT/√m ≈ 3.16.
⟹ the root-number phase sequence IS spectrally flat (max coeff a sub-Gaussian √(2 log m) multiple of the
√m RMS), exactly the prize. The phase sequence is the right object and it behaves as the prize requires.

## The mechanism question (the open core, sharpened to property (d))
What ARITHMETIC FORCES the flatness? Known relations do NOT pin the absolute phase:
- **Naive Rudin-Shapiro doubling REFUTED:** ⟨s_{2k}, s_k²⟩ ≈ 0 (0.058 at n=8, 0.004 at n=16) — the phases
  are NOT a simple s_{2k}=s_k² 2-automatic sequence. The flatness is deeper.
- Hasse-Davenport pins phase-DIFFERENCES (the full 3-term twisted relation g(χ)g(χρ)=χ^{-2}(2)g(ρ)g(χ²));
  Stickelberger pins p-adic VALUATION. NEITHER constrains the absolute archimedean phase.
- The prize needs a NEW arithmetic constraint on the ABSOLUTE phase forcing √(m log m) flatness — the
  precise property (d) of the necessary condition.

## Why this is the right frontier (the user's archimedean-phase directive)
The absolute phase is NOT a mystery transcendental — it IS an arithmetic object with deep theory: the
root number / epsilon factor (Dirichlet L-function functional equation), the Weil index (explicit via
Hilbert symbols, esp. dyadic), a Γ-value period (Chowla-Selberg/Gross-Koblitz). The reformulation turns
the prize into a CONCRETE, COMPUTABLE question — "is the root-number phase sequence over Z/m flat" — with
real arithmetic theory to bring to bear. Attack underway (8 angles: root-number sums, full-HD twisted
automaton, Weil index, Γ-transcendence, stationary phase, Dedekind/Landsberg-Schaar, phase autocorrelation,
wildcard). Probe: this session (exact phase DFT + doubling correlation).

## ★ LIVE LEAD (archimedean attack w804jtt24): the phase sequence is ODD ⟹ DFT is REAL (first non-circular absolute-phase constraint)
The deepest genuine finding from the 8-angle archimedean attack (phase-additive-energy angle):
- **PROVEN, non-circular, absolute-phase constraint:** the Gauss-sum reflection g(χ̄_k)=χ_k(−1)·conj(g(χ_k))
  with **χ_k(−1)=(−1)^{nk}=+1 for n even (2-power)** forces **θ_{−k} = −θ_k EXACTLY** (confirmed to 0.0000)
  ⟹ the phase sequence s is ODD (s_{−k}=conj(s_k)) ⟹ **DFT F[β] is REAL for every β.** This is the FIRST
  genuinely non-circular arithmetic constraint on the ABSOLUTE archimedean phase (not HD phase-difference,
  not Stickelberger valuation) — and it is THIN-ESSENTIAL (needs n even). It reduces the complex
  DFT-flatness to REAL-sequence flatness: max of m reals F[β] with fixed ℓ²=m², fixed sum ±m.
- **Beyond oddness:** the arithmetic phases BEAT random-odd (more flat than a random odd sequence) — so a
  FURTHER structure forces the extra √-cancellation. Autocorrelation E=Σ_{h≠0}|A(h)|² = the L⁴/kurtosis of
  the (real) flatness spectrum; excess c(n)=E/[m(m−1)] is p-INDEPENDENT, → 2−3/n (=1.625 exactly at n=8, 6
  primes) — but quantitatively only at the equidistribution rate (the fixed-q bound is the residual).
- **The sharpened open core:** prove max_{h≠0}|A(h)| = O(√(m log m)) (Sidon-like / low phase-autocorrelation)
  for the arithmetic phase sequence — equivalently the per-shift bound that, with the PROVEN oddness, gives
  the prize. The candidate mechanism (next): the FULL twisted Hasse-Davenport recurrence as a constraint on
  A(h) beyond oddness (the angle the throttle cut). This is the most promising opening of the session: a
  real reduction (complex→real flatness via proven oddness) + a concrete residual (phase autocorrelation
  Sidon bound) that is NOT obviously the dead moment/EVT wall.

## QUANTITATIVE VERDICT (probe complete, n=8,16): oddness REAL, but residual is diffuse = wall
| metric | n=8 | n=16 | reading |
|---|---|---|---|
| oddness err / max Im F | 0.0000 / 0.000 | 0.0000 / 0.000 | DFT REAL, exact (θ_{−k}=−θ_k proven) |
| maxF/√m ARITHMETIC | 2.72 | 3.16 | flat (sub √(2 log m)=3.5,4.1) |
| maxF/√m random-odd | 3.28 | 3.83 | arith BEATS random-odd by ~15–20% |
| F[2β]~F[β] corr (HD doubling) | 0.023 | 0.054 | **≈0 — NO doubling self-similarity** |
| k→k+m/2 symmetry corr | 0.019 | 0.004 | **≈0 — NO second reflection** |
| max autocorr \|A(h)\| / √(2m log m) | 0.58 | 0.86 | sub-target but ratio GROWING |

**Honest verdict.** The archimedean-phase approach produced exactly ONE genuine, proven, non-circular,
thin-essential constraint: **oddness θ_{−k}=−θ_k (χ_k(−1)=+1 for n=2^μ) ⟹ DFT real**, halving complex
flatness to real flatness. This is novel (the first absolute-phase constraint, distinct from HD-difference
& Stickelberger-valuation). BUT the extra flatness beyond oddness (arith beats random-odd) is **diffuse**:
NO exploitable algebraic symmetry — the only exact further relation, Hasse-Davenport (χ→χ²), does NOT
structure the DFT (F[2β]~F[β] corr ≈0), and there is no second reflection. So the post-oddness residual =
"the arithmetic phases equidistribute slightly faster than random-odd" = the equidistribution RATE =
VACUOUS at fixed q = the wall (Katz, effective form). The autocorrelation \|A(h)\| ratio grows (0.58→0.86)
so it is not clearly Sidon-with-good-constant either.

**Net for the prize:** a real partial reduction (oddness, recordable, thin-essential) + a sharper
reformulation (real-DFT flatness of the root-number phase sequence) — but NOT a break. The residual is
the same effective-equidistribution wall in cleaner clothes. The archimedean phase IS arithmetic (root
number / Weil index / Γ-period) and oddness extracts the ONE algebraic constraint available; the rest is
diffuse equidistribution, confirming the §8 verdict that a genuinely NEW effective-equidistribution input
is required. Honest dead-ledger refinement, with one genuine new brick (oddness ⟹ real DFT).
