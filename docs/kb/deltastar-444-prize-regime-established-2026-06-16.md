# δ* — what is ESTABLISHED in the prize regime (#444 dossier, 2026-06-16)

**Purpose.** Collect every result that *holds in the prize regime* (thin dyadic `μ_n`, `n=2^μ~2^30`,
`q=n^β` β≈4–5, `ε*=2^-128`, window interior `1−√ρ < δ* < 1−ρ`), the new discoveries that reframe the
problem, and the precise open frontier. Companion to the empirical-formula spec
(`deltastar-444-empirical-formulas-and-bridges-2026-06-15.md`, the E1–E7 + bridge ledger §A–§G).
**This file is the "what we've solved" half; the bridge ledger is the "how it reduces" half.**

This draft is from high-confidence memory + in-tree bricks; the comment-review workflow augments it
with buried/missed findings and the adversarial re-verification of every value (no laundering).

---

## I. THE REFRAMING — δ* is p-INDEPENDENT (the central new discovery)

The single most important shift since the issue body was written: **δ* is p-independent**, decoupled
from the p-*dependent* analytic BGK/Paley sup-norm `max_{b≠0}|η_b|`.

- The governing object is the **distinct-γ far-line union count** `D*(m) = |⋃_R {γ_R}|` (a `Finset.card`
  of forced ratios `γ_R = −h_{a−k}(R)/h_{b−k}(R)`), NOT the coincidence-multiplicity / character sum.
- **Exact incidence is identical across primes** `p > n^4` (verified n=8–64, multiple primes;
  `ResolveFieldIndependent.lean`: the count bound `(s−w)·N ≤ s` is field-cardinality-independent).
- The far-line incidence has a **CLIFF**: over-determined (`s−k ≥ 2`) is p-INDEP with a closed form;
  under-determined (`s−k ≤ 1`) is p-dependent but `≫ budget≈n`, so the binding always sits in the
  p-independent over-det regime. ⟹ **δ* is governed by a combinatorial, field-independent object.**
- Consequence: the prize is NOT the analytic BGK sup-norm wall (a sufficient-but-not-necessary
  p-dependent handle). It is the p-independent **growth law of D\*** = **BCHKS Conjecture 1.12**.

This is the discovery that "opened up a lot of directions": the problem is now combinatorial/
arithmetic-geometric (determinantal varieties, orbit counts, generating functions), OFF the 25-year
analytic-NT BGK wall.

## II. SOTA IMPROVED — the di Benedetto exponent BEAT (holds in prize regime)

Specializing di Benedetto Thm 3.1 (arXiv:2003.06165) to `μ_n` with the **Sidon-floor energies**
`T_2 = 3n²−3n` (`t₂=2`) and `T_3 = 15n³−45n²+40n = O(n³)` (`t₃=3`) gives `H_exp = 7`, hence
> `max_a |Σ_{x∈μ_n} e_p(ax)| ≪ |H|^{1−1/24} p^{1/72}`, nontrivial for `|H| > p^{1/7}`.

- **β=4** (prize edge): exponent **0.9583**, beating di Benedetto's generic **0.9892** — a saving of
  `1/24` vs `31/2880`, ~3.9× better.
- **β=5**: gives `H^{35/36}` NONTRIVIAL exactly where di Benedetto's generic bound VANISHES.
- Substitution validated (T_m = energy of `H` itself, verbatim `defT_m`; 5 adversarial obstructions
  refuted). Linchpin machine-verified exact to `n ≤ 64` (incl. structured `v₂ ≤ 25`).
- **CONDITIONAL on ONE lemma:** `T_3 = O(n³)` for all `n` (the "No-Excess r=3" / char-0 in-tree
  result extended to all n; `E_3` p-invariant). **UPDATE 2026-06-16 [VERIFIED]:** the needed
  `W_3=0` (char-p No-Excess at r=3) HOLDS for ALL prize-scale primes `p≳n⁴` (computed n=16: W_3=0 at
  70657/196657/786433; nonzero only at small p<threshold) — governed by an ONSET THRESHOLD not
  Fermat-ness. So the `T_3=O(n³)` conditional is **discharged at prize scale**; the residual is only
  the all-n char-0 cubic identity. The deeper wall is `W_r` at `r≈log q≈89` (deep onset threshold).
- **HONEST scope:** 0.9583 ≫ 1/2; this is *SOTA-closeness*, NOT prize closure (reaching the `1/2`
  Paley exponent = beating the `p^{1/4}` prefactor = the BGK wall, on the HIGH side). It is a genuine,
  verified improvement over the published SOTA in the prize regime.

## III. EXACT δ* VALUES (machine-checked / probe-validated)

⚠️ **Convention (corrected — see audit §A):** `δ = 1 − s/n` (s = agreement count), the
incidence-correct form. orbcount's `1−(s−1)/n` column label is an off-by-one display bug.

- `δ*(RS[F₅, 4, 2], ε*=2/5) = 1/4` — first exact pin (`DeltaStarExactPinF5.lean`).
- `δ* = 1/4` on `ε* ∈ [2/17, 7/17)` at `RS[F₁₇,⟨2⟩,4]` — maximal second pin (`DeltaStarSecondPinF17*`).
- `δ* = j/n` closed form on granularity bands (`3(j−1)+k ≤ n`), any smooth RS (`GranularityLadderRS`).
- **`δ*(RS[μ₈, ρ=¼], budget=n) = 3/8 = 0.375`** — binder (5,2), **BELOW Johnson 0.5** [VERIFIED].
- **`δ*(RS[μ₁₆, ρ=¼], budget=n) = 9/16 = 0.5625`** — **one rung past Johnson**, binder s*=7
  (exact, probe-validated, p-indep over-det) [VERIFIED].
- First exact explosion-band value `ε_mca(C84, 1/4) = 7/17` (`FarCosetExplosion.lean`).

## IV. THE far-line δ* PROXY — Johnson-LOCKED (CORRECTED; the "climb to capacity" was an artifact)

⚠️ **CORRECTED (audit §A0):** the over-det far-line δ* is a **Johnson-locked PROXY**, NOT a climb to
capacity. The earlier "cascade → capacity, m*~log n" was an engine direction-cap (`b<s`) artifact.

- **Master gap identity** (audit §A.1): `δ* = 1 − ρ − m*/n`, i.e. `capacity − δ* = m*/n` (the
  `(m*−1)/n` form was off-by-one; `_BridgeB01/B04` now corrected). This identity is exact.
- **The Johnson-lock law** [VERIFIED, full-direction `orbcount`]: **`δ*_farline = 1/2 + 1/n → 1/2`**
  (Johnson from above), **`m* = n/4 − 1` (LINEAR)**:
  - `n=16`: s*=7, **δ* = 9/16 = 1/2+1/16**, m*=3=n/4−1
  - `n=20`: s*=9, **δ* = 11/20 = 1/2+1/20**, m*=4=n/4−1
  - `n=24`: s*=11, **δ* = 13/24 = 1/2+1/24**, m*=5=n/4−1
  - `n=8`: s*=5, δ* = 3/8 (small-n anomaly — plateau exceeds budget; below the 1/2+1/n line).
- **The far-line is a PROXY** (`ε_mca ≥ farline/q`, so `δ*_MCA ≤ δ*_farline → 1/2`): it does NOT reach
  the beyond-Johnson window interior. The true worst-case MCA floor (`δ*_MCA ≥ Johnson`, the prize)
  is the SEPARATE, harder BCHKS/BGK object. **There is no in-tree evidence δ*_MCA climbs to capacity.**
- **D*(1) is p-DEPENDENT** (the m=1 edge); only the over-det `m≥2` count is p-independent.
- **Leading value** `D*(1) ≈ n³` (n=16: 3936≈16³); geometric decay ≈ `n/2..n/4` per depth.
- **Orbit closed form** (E3, `OrbitCountCrossingLaw`): `D = z + S·O`, `S = n/gcd(b−a,n)`, crossing
  `D ≤ n ⟺ O ≤ gcd(b−a,n)`. At the binding the worst direction is **primitive** (d=1) and the bad
  set is a *partial* orbit.
- **EXACT FFT-graded recursion** (E6, `_Close07c` CLOSED odd half + `_Close43` base instance by
  `decide`): `#bad_{2n}(k,2m') = #bad_n(k/2,m')`, odd→0. ⚠️ This `cf` object ≠ the prize cascade `D`
  (they diverge at n=32); it closes E6 structurally but does NOT settle m*-growth.

## V. THE COMPLETE TIGHT REDUCTION (prize ⟺ BCHKS 1.12, axiom-clean)

`_CoreReductionComplete.prize_reduces_to_BCHKS` + `_CoreA7.prize_iff_BCHKS_at_scale`: the
window-interior conclusion `1−√ρ < δ* < 1−ρ` follows from EXACTLY ONE named hypothesis
`hBCHKS = BCHKS 1.12` (distinct r-fold subset-sum `|Σ_r(μ_s)| ≤ q·ε*` at `r ≈ log m`). Both
directions (`BCHKS_necessary`): **BCHKS 1.12 is necessary AND sufficient** — the prize is *exactly*
this one p-independent combinatorial conjecture. The ~45-brick bridge program + 7 core angles all
feed this single reduction (see bridge ledger §A–§G). The wall is provably unavoidable in-tree.

## VI. THE TWO GENUINE NON-BCHKS LEVERS (the open frontier worth pursuing)

1. **Determinantal / Plücker-minor count** (`_CoreA6/_CoreA6deep`): `D*(2) ≤ 2·span` via the
   degree-2 (Bézout) minor polynomial, with `bezout_beats_choose_two` (`2n < C(n,2)` ∀n≥6) — a
   p-independent determinantal-variety count that genuinely beats the trivial bound IF the
   single-parameter minor factorization holds for the worst direction. Tractability via Lang–Weil on
   the degree-2 determinantal variety is the open question. Machine-certified DIFFERENT from BCHKS
   subset-sum (`plueckerMinor_ne_subsetSum`: the 2×2 minor is `−xy`, a product not an additive sum).
2. **Dedup-strictness at log depth** (`_CoreA3`): `BCHKS ⟹ WeakestSuff` holds unconditionally via the
   dedup domination `D ≤ Σ_r`; the reverse needs `Σ ≤ D` (false pointwise, B33). Whether the dedup
   `D ≤ Σ_r` is STRICT at `m ≈ log n` is the precise open question — strict ⟹ prize needs less than
   full BCHKS; equal ⟹ wall. P-independent, off the MGF wall, UNSETTLED (in-tree evidence leans wall;
   the toy "escape" theorems are vacuous — do not cite them as escapes).

## VII. WHAT IS DEAD (do NOT re-attempt) — from the meta-theorem

Every second-order / moment / probabilistic-EVT method is proven dead as a *theorem*
(`moment_ladder_exceeds_prize`): no moment method of any depth reaches `√(n log(q/n))`. Periods are
exchangeable white-noise (`Cov = −Var/(m−1)`, distance-independent) → kills log-correlated /
FHK / GMC / branching-random-walk / Coulomb-gas. Modern NT tools (decoupling, VMVT, restriction,
sum-product) need curvature; `μ_n` is flat 0-dim → all reduce, none beat `n^{0.989}`. The analytic
BGK sup-norm route is SUFFICIENT but NOT necessary (superseded by the p-independent framing).

---

## VIII. NEW RESEARCH DIRECTIONS — the open avenues worth pursuing (from the 283-comment review)

Surfaced and de-duplicated from the comment fan-out. Grouped by tractability. The two **non-BCHKS
levers** (§VI) plus these are where a continuing agent should spend effort.

**A. Decisive numerical (would settle m*-growth / the curve):**
- **Plateau-width law `w(n)`** of the worst-dir over-det cascade — *the single most decision-relevant
  computation* (bounded w ⟹ m*=O(log n) ⟹ δ*→capacity). n=64 GPU run of `min_m D*(m)` is the
  decisive test (n=32 already ambiguous; brute is GPU-infeasible — needs the orbit-count recursion).
- **Uniform per-rung orbit-count decay up the imprimitive d=2 tower**; discharge the imprimitive
  analogue of `_Close26` (B27 plateau).
- **Binding-codim / `j*=2` persistence as n→∞ at fixed ρ** (`SchurMinorStaircase`).

**B. The energy / Wick ladder (the analytic crux, off-BGK via DC-subtraction):**
- **Char-p transfer of Lam–Leung `E_r(μ_n) ≤ (2r−1)‼·n^r` at depth `r≍log q`** — the single named
  open Prop behind the moment route (`SL-M4`, `S-M1'`). **Use the DC-SUBTRACTED `A_r = E_r − n^{2r}/q`**
  (the raw `E_r ≤ Wick` is FALSE at the prize — DC term dominates; only `A_r ≤ Wick` is non-vacuous).
- **Exact `E_{r+1}` closed forms for r≥5** (the open "producer" brick; E_2..E_5 done — see §IV-data).
  **DONE (2026-06-16):** E_2..E_6 in-tree (`_CharZeroEnergyClosedForm.lean`); **E_7 LANDED** axiom-clean
  (`_AvL2_E7ClosedForm`): `E_7(μ_n)=135135n⁷−2837835n⁶+26801775n⁵−141891750n⁴+433726293n³−708996288n²+471556800n`
  (leading (2·7−1)‼=135135, 2nd coeff −C(7,2)·135135, SOS deficit cert; cross-validated by independent
  exact values E_7(4)=11778624, E_7(8)=16993726464). E_8+ is the next producer rung.
- **`GaussianStepLaw` `E_{r+1} ≤ (2r+1)·n·E_r`** local per-step reduction (front-runner enabler).
- **Effective-Chebotarev count of `Spur_r(p)` at depth `r~log q`** (the bad-prime wraparound count;
  Lagarias–Odlyzko / `p≡1 mod 8` density-1/4 surviving class).
- **Open input `W_3 ≤ Cn³`** (fixed-weight-6 r=3 char-p bad-prime count) → discharges the di
  Benedetto `T_3=O(n³)` conditional (§II) AND the r=2 moment rung.

**C. The determinantal / combinatorial route (p-independent, off the analytic wall):**
- **Distinct-γ union-count growth law** `|⋃_R {γ_R}|` — generating-function / polynomial-method
  bound (the reframed combinatorial core, parallel to BCHKS-1.12).
- **`deg(#bad_r) < r`** for general r (the growing-slack mechanism) — would give the decay.
- **Bound the divided-difference RATIO image** of the agreement pencil; supply `P` (distinct-γ cap)
  and `M` (per-scalar multiplicity cap) for the incidence factorization.
- **Exact spectrum cardinality `|{Σ_{z∈S} z : S∈powersetCard r μ_n}|` growth law** (the subset-sum
  spectrum size — the BCHKS object directly).

**D. Promising-but-untested external tools (need a prize-regime test):**
- Effective sum-product with QUANTIFIED constants (Lens 1); Murphy–Rudnev–Shkredov 49/20 energy
  (arXiv:1712.00410) → entropy/Kesten route; OSV short-Weil curve-blend (arXiv:2211.07739) for the
  dilation family; Liu–Zhou subgroup-restriction eigenvalue recursion up the dyadic tower; theta-FE
  for the quadratic reparametrization `x↦x²` (metaplectic self-similarity); FKMS bilinear-below-PV
  (arXiv:2511.094xx) via the m-fixed 2-power coset structure.

## IX. BAD RESULTS — re-testable in the prize regime (double-checked per the user's ask)

Most refuted routes are **definitively dead** (reduce to the BGK/BCHKS wall — see the issue-body
DEAD ledger §8). The handful genuinely worth a *prize-regime* re-test:
- **M2 Stickelberger/Chebotarev generic route** — failed generically, but the `p≡1 mod 8` (m≥3)
  surviving class (density 1/4) is the prize-prime class; the divisibility count there is untested.
- **Wasserstein/Kowalski–Untrau (KU25) effective equidistribution** — the no-go was at thick scale;
  the W_1 extreme-value upgrade of the Gauss-period family law is untested in the thin regime.
- **`E_{r+1} ≤ (2r+1)n·E_r` monotonicity** — refuted as a literal global inequality, but the
  DC-subtracted `A_{r+1} ≤ (2r+1)n·A_r` per-step form is the live, untested variant.
- **Plotkin δ*=1/2 ceiling / antipodal route** — the half-cap was RETRACTED (audit §C); but the
  far-line-as-Plotkin-proxy (→1/2, below Johnson for ρ<1/4) is a *correct* structural fact isolating
  the hard residual to asymmetric words — worth re-deriving cleanly.
- **Energy-ratio / cumulant routes** — all refuted as literal full-energy forms; the DC-subtracted
  `A_r`-form ladder is the surviving re-test.

## X. AUDIT — laundered values / phantom bricks / bugs
See `deltastar-444-audit-corrections-2026-06-16.md`. Highlights: the **δ* off-by-one** (corrected
above), **D*(1) p-dependence** (laundered as p-independent), **phantom bricks** (`Sweep_A41-A48`,
`_DefectOnsetOvershoot`, `SubsetSumThreePowExact` cited as landed but ABSENT), the **retracted**
`_AntipodalPlotkinHalfCap`, the **n=32 dispute**, and the **`V_r` 0-dimensional ⟹ Lang–Weil vacuous**
caveat (which softens — but does not break — the A6 determinantal lever: it's a Bézout root-count,
not a Lang–Weil point-count).
- named Props/axioms still to solve
