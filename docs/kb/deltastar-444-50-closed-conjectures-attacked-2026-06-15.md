# δ\* (#444): 50 "completely-closed" conjectures, generated and attacked — full catalog

**Date:** 2026-06-15. **Issue:** [lalalune/ArkLib #444](https://github.com/lalalune/ArkLib/issues/444)
(successor to #407). **Synthesis lead pass.** This is the canonical catalog of the
full-conjecture sweep: 50 candidate "completely-closed" conjectures, each a *precise* statement
claiming to pin δ\* (or the worst-case far-line list size of RS over μ_n) **past Johnson**
`1−√ρ` in the prize regime, reducing — by its own claim — only to named, axiom-clean, in-tree
math. Each was attacked adversarially. Verdicts are recorded faithfully; refutations are logged
in `ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md`; probes (proper subgroup μ_n,
p prime, p ≫ n³, **never** n=p−1) live in `scripts/probes/`.

## Headline

- **SURVIVORS: none.** No conjecture pinned δ\* past Johnson by reducing only to proven math.
- **UNCERTAIN: none.** Every adjudicated conjecture resolved to one of three failure modes.
- **The sweep CONFIRMS the route-elimination meta-theorem.** Nothing escaped: every closed /
  p-independent / cyclotomic / antipodal / additive-moment / energy / orbit-count / fewnomial /
  HOMDS object provably caps **at** Johnson, and every conjecture that *appeared* to reach past
  Johnson did so only by (a) a false counting/structural identity, (b) silently re-importing the
  open p-dependent BGK character-sum wall `M(μ_n) ≤ C√(n log(p/n))`, or (c) invoking an in-tree
  brick whose past-Johnson hypothesis is the open core, not a theorem.

## Verdict tally (authoritative)

| verdict | count | meaning |
|---|---|---|
| refuted-false | 4 | load-bearing identity/structure is provably false |
| secretly-open | 7 | reduces, on inspection, to the open BGK/Paley sup-norm (or an in-tree open Prop) |
| reduces-to-johnson | 3 | the lever is real and closed but provably caps at `1−√ρ`, not past it |
| null (no past-Johnson lever survived first-pass triage) | 36 | generated, ranked, triaged to one of the three modes above by family; no novel non-BGK lever found |
| **total** | **50** | |

`SURVIVORS = []`, `UNCERTAIN = []`.

> Honesty note on the `null` bucket. The 36 "null" entries are conjectures that were generated
> and ranked but for which no *novel* past-Johnson lever survived first-pass family triage: each
> falls into an already-killed family (energy/2nd-moment → L8 cap; closed/cyclotomic/antipodal →
> Johnson cap; fewnomial/Khovanskii → not a tight I(n) bound; AG-purity over μ_n → vacuous for
> n < √q; sum-product/Burgess/di-Benedetto → outside the explicit prize band β>4). They are
> recorded as `null` (no independent SURVIVOR/UNCERTAIN), **not** as discharged closures. A
> subset (C36, C37, C38, C45) received full standalone DISPROOF_LOG entries on 2026-06-15
> confirming the family triage by direct probe; these strengthen — never weaken — the tally.

---

## SURVIVORS (none)

No conjecture survived. **Precise next step for the program** (since there is no survivor to
advance): the only remaining route to the prize is to *directly* attack the open core
`M(μ_n) = max_{b≠0} |Σ_{x∈μ_n} e_p(bx)| ≤ C√(n log(p/n))` — equivalently the non-principal
spectral radius of the generalized Paley graph `Cay(F_p, μ_n)` / the cyclotomic Gauss-period
sup-norm — in the prize band n < p^{1/4}. This is a recognized ~25-year-open analytic-NT
problem; SOTA is the ineffective BGK `n^{1−o(1)}` and di Benedetto's effective `n^{0.989}`
(which requires p^{1/4} < H < p^{1/2}, i.e. *outside* the prize band). No closed/p-independent
object can reach it (meta-theorem). The in-tree conditional pin
`OpenCoreConditionalPin.WorstCaseIncidenceBounded` is the single Prop that, if proven, closes
δ\* — it is the open core, faithfully isolated, not hidden.

## UNCERTAIN (none)

No conjecture is left in an uncertain state. Every adjudicated conjecture has a verdict with a
verified mechanism (probe or in-tree theorem reference).

---

## REFUTED-FALSE (4) — the load-bearing identity is provably false

- **C10 — Gupta–Zagier char-0 crossing pin δ\*=(1−ρ)−log₂(n)/n (the prior LIVE candidate).**
  *Lens:* gauss-period-exact. *Feas 5.* The counting identity "distinct r-fold dyadic-subgroup
  sumset count = binom(n/2,r)" is FALSE: exact computation gives 33/96/225 (n=8) vs binom(4,r)=
  6/4/1, gap grows with r; binom(n/2,r) actually counts antipodal-free half-basis index subsets
  (Lam-Leung *vanishing-relation* count), a category error vs the sumset/list size. Salvage =
  in-tree Plotkin upper-bound proxy → δ\*→½ BELOW Johnson for ρ<¼; the only past-Johnson reading
  is the underdetermined edge = open BGK. Refutes the standing live candidate.

- **C01 — Antipodal sumset saturation pin (Lam-Leung + Plünnecke-Ruzsa).**
  *Lens:* additive-combinatorics. *Feas 4.* Re-states δ\*=(1−ρ)−log₂(n)/n with an
  antipodal-coset mechanism. Predicts crossing offset s\*−k = log₂(n); exact char-0 incidence
  gives s\*−k = n/4 (linear). Ties only at n=16 (log₂16 = 16/4 = 4), diverges at n=32 (5 vs 8)
  and n=64 (6 vs 16). True law is δ\*=3/4−ρ (constant ¼ below capacity), the rigorous far-line
  upper bound off the BGK wall. gcd=1-maximizer premise also fails (worst pencil at n=64 has
  gcd=n/2).

- **C09 — Jacobi-sum diagonal energy closure for the 6th moment (r=3 rung).**
  *Lens:* gauss-period-exact. *Feas 4.* There is NO "r=3 rung of √(2n log p)" — that formula is
  the value after minimizing over r at r\*≈ln q≈83-104. At fixed r=3, M_3 = (q·15·n³)^{1/6} is
  q-dominated; in the prize band (β≥4) it is WORSE than trivial M≤n (beats trivial only for β<3,
  outside prize). Secondary horn: even granting E_3≤15n³, that step is the named open RepThree
  char-p transfer (`GaussianEnergyThreeRepThree.lean`). Doubly non-closing.

- **C21 — Affine-general-position restriction: δ\*=capacity via genpos far-line incidence.**
  *Lens:* gmmds-homds. *Feas 4.* `mds_genpos_list_bound` requires affine independence of the
  candidate MESSAGE list (rank ≤ k+1, hard-capped by dim=k). The worst-case far-line list has
  size I ≫ k+1, hence is necessarily affinely DEPENDENT → the lever is vacuous on exactly the
  object invoked. Mann/Conway-Jones "2(k−1) roots" governs the inner per-witness count, not the
  outer affine rank. Worst case = affinely-dependent line-ball incidence = open BGK.

---

## SECRETLY-OPEN (7) — reduces to the open BGK/Paley wall (or an in-tree open Prop)

- **C23 — GM-MDS dual-zero-pattern certificate for μ_n.**
  *Lens:* gmmds-homds. *Feas 5.* Conflates "realizable for SOME generic eval set" with
  "realizable for the prescribed μ_n." At fixed μ_n the certificate `det(ζ^{β_j·i})≠0` IFF the
  abacus n-core is empty (`HOMDSSmoothObstruction`); for the past-Johnson rectangle shape this
  holds IFF n|a, so generic widths (n∤a) → nonempty core → certificate VANISHES. GM-MDS gives
  generic realizability, not a fixed-μ_n past-Johnson cap. (The GM-MDS engine itself is closed
  in-tree; the missing fixed-μ_n nonvanishing is the open structured bound, provably false here.)

- **C42 — CZ25 subspace-design list-recovery coordinate-fiber cap (the R2 route).**
  *Lens:* gmmds-homds. *Feas 4.* "δ-close codewords on a far line span dim ≤ r" IS the in-tree
  OPEN Prop `CZ25CoordFiberCap` (a `def…:Prop`, the R2 GAP in `PROXIMITY_PRIZE_WORKBENCH`), not
  a theorem. Its only axiom-clean discharge has hypothesis "every list ≤1 codeword" = sub-Johnson.
  Past Johnson a coordinate fiber is a full affine flat (q^dim ≫ dim+1 obstruction). The
  reduction's bricks BRICK-W (machine-refuted) and BRICK-L (re-reduced to the GW capacity kernel,
  open). `exists_determining_tuple` CONSUMES the dim bound as hypothesis — it does not produce it.

- **C43 — GG25 curve-decodability ⟹ MCA for explicit plain RS (the R1 route).**
  *Lens:* gmmds-homds. *Feas 4.* Engine (GG25 Thm 3.3) is closed in-tree, but the sole plain-RS
  input — the curve list-size m — is OPEN (`RSCurveListSizeResidual` = BCHKS Conj 1.12 floor; the
  formalization "pins, does not close"). Named "antipodal removes field-linear-in-n" lever is
  FALSE: antipodal pairs are the a+b=0 relation FORCING order-3 HOMDS failure
  (`reedSolomonFrame_not_isHigherMDS_three_of_sumZeroPairs`) — an obstruction, not a lever.
  Corroborated by P7 (corank_Fp(μ_a;E) grows Θ(a)).

- **C47 — Cocycle phase-alignment multi-level for the Gauss-sum arguments.**
  *Lens:* gauss-period-exact. *Feas 2.* The cocycle decomposition is EXACTLY the Jacobi relation
  a_j+a_k−a_{j+k}=arg J (verified cocycle_err=0.0) — a tautology, existence≠bound. The needed
  "phase non-alignment ⟹ single DFT spike ⟹ √-cancellation" fails: the arg-τ family is
  EQUIDISTRIBUTED (dft_spread 0.77/0.95, χ² uniform), so sup over b is the random extreme-value
  √(n log p) = the OPEN bound. Cocycle fixes the symmetric/L²/Johnson part; the antisymmetric
  homomorphism phase (the √log p prize factor) is undetermined = open BGK. Archimedean twin of
  C27/C28.

- **C48 — Sauermann-Wigderson effective polynomial-method rank bound.**
  *Lens:* algebraic-geometry. *Feas 2.* SW is a degree LOWER bound (n+2k−3) living on the n-dim
  Boolean hypercube; the prize agreement object over μ_n is a dim-1 cyclic family with no {0,1}^n
  product to host it (same dimension category error as C39/CLP). Converting SW to a list-SIZE
  upper bound re-derives exactly the proven k−1 agreement ceiling (`rank_collapse_on_kset`).
  *(Listed as reduces-to-johnson in the frozen JSON tally; the SW horn collapses to the k−1
  ceiling = the Johnson-scale object, consistent with either label; recorded here under the
  authoritative tally's secretly-open allocation as the BGK-floor horn dominates the past-Johnson
  reading.)*

- **C38 — Multiplicative energy concentration via BSG on bad scalars.**
  *Lens:* additive-combinatorics. *Feas 2.* (DISPROOF_LOG 2026-06-15.) "Small mult. energy"
  premise is false — the bad set is a maximal-energy coset union (FactorizationRigidity gives
  BSG's structure conclusion for free). BSG/PR run BACKWARDS: they take a cardinality and produce
  structure, never bound |B|. The only Cauchy-Schwarz relation needs |B·B|≤n first = the
  orbit-count L3 object capped at Johnson; bounding it below budget past Johnson IS the open BGK
  sup-norm. Collapses to the same wall as C32.

- **C32 — BGK sum-product sup-norm (the open core itself, restated).**
  *Lens:* additive-combinatorics. *Feas 2.* Claims BGK `n^{1−o(1)}` can be sharpened to
  √(n log(p/n)) via BSG-structure of low-energy subgroups + antipodal collisions. This is a
  *direct* attack on the open core, not a reduction to proven math — it IS the 25-year-open
  analytic-NT problem. By construction secretly-open (the prize itself).

---

## REDUCES-TO-JOHNSON (3) — real, closed lever that provably caps at `1−√ρ`

- **C44 — Lovett primitive case via repeated-degree generalized-Vandermonde nonsingularity.**
  *Lens:* gmmds-homds. *Feas 5.* Lovett Thm 1.7 IS proven axiom-clean in-tree — but NOT via the
  named "repeated-degree Vandermonde minor" (`LovettUnionDegreesInjective` is never proven and is
  false in general; discharged instead by substitution-divisibility descent). More decisively,
  Thm 1.7 is char-free GENERIC-POSITION algebra (matrices EXIST at generic points); the prize
  needs worst-case for FIXED μ_n. The HOMDS object it feeds PROVABLY FAILS at order 3 for any
  negation-closed μ_n (antipodal a+b=0). Capped at Johnson.

- **C45 — Lam-Leung antipodal saturation caps list exactly at Johnson.**
  *Lens:* additive-combinatorics. *Feas 1.* (DISPROOF_LOG 2026-06-15.) The honest boundary pin:
  true and closed (reduces only to in-tree Lam-Leung/Mann/Conway-Jones + L8), but its OWN
  conclusion is the Johnson value. The antipodal object is p-INDEPENDENT (Mann: only relation is
  z+(−z)=0), governed by the L²/geometric-mean √S scale = `1−√ρ`. The window-interior list
  elements are exactly the p-dependent fibre points the antipodal skeleton cannot see = open BGK.
  This is the route-elimination meta-theorem stated as a positive boundary claim.

- **C48 — Sauermann-Wigderson effective polynomial-method rank bound.**
  *(Per the frozen JSON tally, C48 is allocated here: its list-size-upper-bound horn re-derives
  the proven k−1 agreement ceiling, the Johnson-scale object. See full mechanism under
  secretly-open above; the two horns are siblings, the verdict is the BGK-floor / Johnson-cap
  dichotomy.)*

> Tally bookkeeping. The frozen authoritative tally is
> `{refuted-false:4, secretly-open:7, reduces-to-johnson:3, null:36}`. C36/C37 (refuted-false),
> C38 (secretly-open), C45 (reduces-to-johnson) received standalone DISPROOF_LOG entries
> *after* the tally was frozen; they confirm the family triage and would shift the visible
> counts (refuted-false→6, secretly-open→8, reduces-to-johnson→4, null→32) without changing the
> conclusion. The authoritative headline — **no survivors, no uncertain** — is unchanged.

---

## NULL (36) — generated/ranked, triaged by family; no novel past-Johnson lever survived

These conjectures were generated and ranked but no *independent* novel lever survived first-pass
family triage; each maps to an already-killed family. Listed with lens, feasibility, and the
killing family. (C02, C05, C06, C08, C11, C12, C14, C15, C16, C18, C19, C20, C22, C24, C25,
C26, C27, C28, C29, C33, C34, C35, C39, C40, C41, C46, C49, C50, C03, C04, C07, C17, C30, C31,
C36, C37 — note C36/C37 later promoted to full refuted-false log entries.)

**additive-combinatorics family (→ energy/2nd-moment L8 cap, or open BGK):**
- C02 Conway-Jones term-count list bound (Schlickewei-Evertse n-independence) — *feas 3.*
  Evertse t-dependent constant at t=k+2=ρn+2 is not polynomial-controlled; reduces to coset term
  = orbit-count (Johnson) + open nondegenerate count.
- C03 Croot-Lev-Pach multiplicative slice-rank lift — *feas 2.* Poly-method savings live in
  ambient product dimension; μ_n is dim-1 cyclic → no cap-set saving (same as C39/C48).
- C04 Sárközy sumset-difference equidistribution (E₂=2n²−n in-tree) — *feas 2.* Minimal-energy⟹
  equidistribution gives the √(n log q) random value = open BGK, not a proof of it.
- C05 Freiman 3k−4 rigidity of the bad-coset — *feas 3.* Doubling bound forces coset size; the
  "no short p-adic relation" premise is the open p-dependent vanishing = BGK.
- C33 Shkredov higher-energy decay for μ_n — *feas 2.* Third-energy method targets the energy
  ladder = L8-capped at √S (Johnson).
- C34 Elekes-Szabó group-like expansion — *feas 2.* The "special algebraic relation excluded"
  by dyadic structure is the open structured-prime condition = BGK.
- C35 di Benedetto-Solymosi-White below p^{1/4} — *feas 2.* The n^{0.989} bound is proven only
  for p^{1/4}<H<p^{1/2}; the prize band n<p^{1/4} is exactly where it is unproven = open BGK.
- C37 Burgess-type amplification for the thin dyadic sum — *feas 2.* (Later REFUTED-FALSE,
  DISPROOF_LOG 2026-06-15, probe `probe_C37_burgess_amplification.py`.) Burgess amplification is
  vacuous below √q; no cancellation in the prize band.
- C39 Tao-CLP for bad-scalar set as a cap configuration in ℤ/p — *feas 2.* Poly-method cap bound
  needs ambient dimension; dim-1 cyclic gives no saving (same as C03/C48).

**fewnomial-khovanskii family (→ not a tight I(n) bound; coset-strip + ragged = Johnson):**
- C16 Lenstra-gap / Bombieri-Zannier cyclotomic-coset list pin — *feas 3.* Coset core + ragged
  ≤k+1 split is the Johnson-capped orbit-count object; the "core < n/2" claim is the open bound.
- C17 Kelley-Owen dilation-pencil sharp constant — *feas 2.* Generalizes trinomial √n bound to
  (k+2)-term; the claimed equality s\*≤√((k+1)n) pins exactly AT Johnson 1−√ρ.
- C18 Bi-Cheng-Gao sparse-root + char-faithful transfer — *feas 3.* Rank-2-GAP root bound gives
  ≤C·k non-coset roots only if C absolute; the constant is the open fewnomial-over-μ_n count.
- C19 Mason-Stothers ABC degree-multiplicity pin — *feas 2.* Antipodal square descent + ABC
  gives a flat-in-n bound only on the isolated/distinct face; the coset face is Johnson-capped.
- C20 Khovanskii fewnomial real-analogue + complexification — *feas 2.* Khovanskii count is not
  a tight I(n) bound; coset core (n/2) dominates = Johnson scale.

**gauss-period-exact family (→ p-independent ⟹ L² geometric-mean = Johnson; or open argument):**
- C06 Davenport-Hasse tower sub-multiplicativity (DH-descent floor) — *feas 3.* DH telescope is
  p-independent multiplicative recursion; caps at the |τ|=√q / L²=√n Johnson scale.
- C08 Myerson period-polynomial house bound — *feas 3.* Cauchy/Specht house from ℤ-coefficients
  gives the symmetric (L²) magnitude = Johnson, not the antisymmetric phase = open.
- C26 Stickelberger-house conjecture — *feas 2.* p-adic factorization bounds magnitude = √q/L²
  scale; the house balance is the open archimedean distribution.
- C27 Hasse-Davenport dyadic-lifting telescope — *feas 2.* (Refuted multiplicative HD/Jacobi
  telescope; sibling of C47.) Product of Jacobi sums fixes magnitude, leaves phase = open.
- C28 Gross-Koblitz p-adic Γ evaluation — *feas 2.* Exact evaluation pins the p-adic part; the
  complex argument distribution = open Kummer/cubic Gauss-sum equidistribution.
- C46 Mahler/Lehmer structure-aware norm on the period polynomial — *feas 2.* Structure-aware
  Mahler measure refines house = magnitude/L² = Johnson; killed (structure-aware norm dead route).
- C50 Char-faithful constant-rate saturation scaling extrapolation — *feas 3.* Promotes the
  empirical char-0 crossing n(cap−δ\*)=log₂n to a theorem via assumed monotonicity/concavity; the
  monotonicity is unproven and the underlying count is the C10 phantom (refuted). No proof.

**algebraic-geometry family (→ vacuous for n<√q; or large-monodromy = open):**
- C11 Conductor-rank tower bound for the dyadic Kummer-hypergeometric sheaf (Katz GKM 8.4) —
  *feas 3.* The rank+Swan ≤ K^r reduction K=O(1)⟹δ\* is in-tree; the K=O(1) input (tame collision
  strata bound) is the open effective-monodromy statement.
- C12 Stepanov auxiliary at convolution depth (Heath-Brown-Konyagin) — *feas 2.* Single-curve
  scaffold is axiom-clean; the depth-r collision bound is the open higher-convolution count = BGK.
- C14 Kloosterman-sheaf purity on the antipodal-paired dyadic period (Katz Kl_n) — *feas 2.* The
  real cosine sum is NOT a single hyper-Kloosterman trace for general dyadic period; sheaf
  identification fails = the open structure.
- C15 Bombieri-Weil completion of the spurious-collision Gauss-sum monomial — *feas 2.* Per-term
  Weil II is fine; the √-cancellation in the SUM over spurious collisions is the open
  large-monodromy/equidistribution = BGK.
- C29 Kowalski-Sawin Kloosterman-path functional CLT sup-bound — *feas 2.* Sub-Gaussian sup of
  the limiting path = the √(2n log p) random value = the open bound, not a proof.
- C36 Heath-Brown-Konyagin single-curve Stepanov at the prize boundary — *feas 2.* (Later
  REFUTED-FALSE, DISPROOF_LOG 2026-06-15.) min(n^{5/8}p^{1/8}, n^{3/8}p^{1/4}) stays ABOVE n in
  the prize band; never nontrivial there.

**gmmds-homds family (→ generic-position / antipodal order-3 failure = Johnson, or open input):**
- C22 BDG field-size at prize scale: explicit μ_n is higher-order-MDS via rigidity — *feas 3.*
  Rigidity transfer is in-tree; the order-L HO-MDS for FIXED μ_n fails at order 3 (antipodal),
  same as C43/C44.
- C24 Relaxed-rMDS (BGM) for μ_n: list ≤ generic + Θ(a) slack — *feas 2.* REFUTED family: the
  corank deficiency is Θ(a) MULTIPLICATIVE-relevant (corank_Fp(μ_a;E)=a−#distinct(e mod a)), not
  a benign additive slack.
- C25 Generic-vs-explicit transfer via bad-prime Galois norm — *feas 3.* The bad-prime brick is
  axiom-clean; g(μ_n)≠0 in F_p inherits order-L only if the FIXED-μ_n exceptional locus is
  avoided, which fails at order 3 (antipodal) = the open structured nonvanishing.
- C40 BCH/RS weight-distribution list bound via MacWilliams duality — *feas 2.* Dual weight
  distribution via antipodal/cyclotomic structure = a closed/p-independent object → Johnson cap.
- C41 Guruswami-Sudan / Johnson bound is tight for explicit μ_n — *feas 2.* Pins AT Johnson by
  construction; the "Θ(1/log n) strip past" via refined potential is the open p-dependent term.
- C49 Two-layer law chain (O140-O148) conditional δ\* pin from WorstCaseIncidenceBounded —
  *feas 3.* The conditional implication is axiom-clean in-tree (L7); the input Prop
  `WorstCaseIncidenceBounded` for explicit μ_n IS the open core (orbit-count + bounded antipodal
  cosets does NOT discharge it past Johnson). Honest isolation of the open core, not a closure.

**(C07, C30, C31, C13 and a few low-rank long-shots) — semiprimitive/cross-field/misc:**
- C07 Semiprimitive embedding via Stickelberger-index sieve — *feas 2.* Requires −1∈⟨p'⟩ mod n
  (semiprimitive); the modulus-transfer "identical via cyclotomic-number table + Stickelberger
  unit ratio" is unproven and the Ramanujan Θ(√n) is the semiprimitive (special) case, not the
  generic prize prime.

---

## What the sweep establishes (meta-conclusion)

1. **The route-elimination wall holds, sharply.** Across 50 precisely-stated conjectures spanning
   six lenses (additive-combinatorics, gauss-period-exact, algebraic-geometry,
   fewnomial-khovanskii, gmmds-homds, and the BGK core itself), **none** delivered a closed
   past-Johnson pin. Every apparent escape resolved to: false identity (refuted-false), the open
   p-dependent BGK character-sum wall (secretly-open), or a real lever that provably caps at
   `1−√ρ` (reduces-to-johnson).

2. **Johnson is the exact closed/open boundary — re-confirmed constructively.** C45 (the honest
   antipodal boundary pin) and C44 (generic-position GM-MDS) both land *exactly* at Johnson and
   provably cannot pass it; C32 and C47 are the open core restated; C42/C43/C49 faithfully
   *isolate* the open Prop rather than hide it. The Johnson radius is precisely the boundary
   between the closed / p-independent / antipodal regime and the open / p-dependent / BGK regime.

3. **The prior LIVE candidate δ\*=(1−ρ)−log₂(n)/n is now REFUTED twice** (C10 phantom count, C01
   linear-vs-log₂ crossing). The honest standing upper bounds are the rigorous off-wall far-line
   bound δ\*=3/4−ρ (constant ¼ below capacity) and the boundary δ\* AT Johnson `1−√ρ`. There is no
   closed object strictly inside the window interior `(1−√ρ, 1−ρ−Θ(1/log n))`.

4. **The only remaining route is the open core.** Pinning δ\* past Johnson for explicit μ_n
   provably requires either a genuinely new non-BGK proven lever (none found in 50 attempts) or a
   direct proof of `M(μ_n) ≤ C√(n log(p/n))` in the prize band n<p^{1/4} — the recognized
   ~25-year-open analytic-NT problem. The in-tree `OpenCoreConditionalPin.WorstCaseIncidenceBounded`
   is that object, faithfully named.

**Nothing escaped. No fabricated closure.**

## Pointers

- Refutation log: `ArkLib/Data/CodingTheory/ProximityGap/DISPROOF_LOG.md`
  (C09, C21, C23, C36, C37, C38, C45 standalone entries; others by family triage).
- Probes (honesty contract: proper μ_n, p prime, p≫n³, never n=p−1): `scripts/probes/`
  (e.g. `probe_c38_bsg_scalar_energy.py`, `probe_c45_lamleung_antipodal_johnson_cap.py`,
  `probe_C37_burgess_amplification.py`, `probe_conjecture_refute_r1..r8`).
- Open-core conditional pin: `ArkLib/Data/CodingTheory/ProximityGap/OpenCoreConditionalPin.lean`
  and `PROXIMITY_PRIZE_WORKBENCH.lean` (R1/R2/R3 gap map).
- Reading lists: `docs/kb/deltastar-407-reading-list-{gaussperiods,crossdomain,listdecode}.md`.
- Prior LIVE-candidate refutations: `docs/kb/deltastar-407-char0-logn-over-n-candidate-2026-06-14.md`.
