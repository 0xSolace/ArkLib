# The BCIKS20 Faithful Surface (#304)

The issue #304 corpus around the BCIKS20 §5 keystone ("every good decoded family lies on a
polynomial curve") lives in `ArkLib/ToMathlib/`. Every declaration cited below is in-tree,
sorry-free, and axiom-clean (`[propext, Classical.choice, Quot.sound]`; each file carries a
`#print axioms` footer). This page records (1) the statement-bug pattern that forced the
surface rewrite, (2) the architecture map, and (3) the working conventions that proved
load-bearing. Companion conventions page:
[`coding-theory-conventions.md`](coding-theory-conventions.md).

## 1. The statement-bug pattern and the audit checklist

The recurring failure mode: an interface bundle that *looks* like the paper statement but is
unsatisfiable, vacuous, or a transposition of it — so "progress" against it is fiction. Before
proving anything against a bundled hypothesis, run this checklist. Each item has a concrete,
machine-checked #304 instance.

| Check | #304 instance | Where machine-checked |
|---|---|---|
| **Residual ≡ goal** — a "residual" that restates the conclusion proves nothing. | Guarded throughout: every named residual ships with a *proven consumer* strictly stronger than the residual itself. | e.g. `RootSupplyOn` + `exists_root_with_readings_of_rootSupply` in `ArkLib/ToMathlib/ConditionDiscProduct.lean` |
| **Unsatisfiable fields** — a field provable only in a degenerate regime, or never. | `hβ : ∀ t, β R t = betaRec …` is permanently undischargeable: the legacy `β` is `Exists.choose` of a weight-only existence (trivial witness `0`), so nothing beyond the weight bound is provable about it (the "opaque-β" finding). `hsubst` is satisfiable only at `x₀ = 0`. | `ArkLib/ToMathlib/BetaIdentify.lean` (routes (a)/(b) blocked); `SubstFieldCaveat.hasSubst_shiftSeries_iff_eq_zero`, cited in `ArkLib/ToMathlib/OffcentreKeystoneAssembly.lean` |
| **Transposed variables** — the statement swaps the roles of two variables of the paper. | The legacy `hPz` "linear representative" shape is degree ≤ 1 in the *codeword* variable; BCIKS20 Prop. 5.5 is low-degree in the *curve parameter*. Any decoded family with one member of degree ≥ 2 on a good point refutes the old bundle. Same disease in the Claim 5.9 rendering: in-tree `Z`-image was the adjoined root `T`, not the ground variable. | `no_linRep_of_nonaffine`, `natDegree_linRep_eval_le_one` in `ArkLib/ToMathlib/FaithfulCurveExtraction.lean`; `ZLinearClosureAudit.lean` FINDING 1/2 (`natDegree_eq_one_of_gammaGenuine_paperZ_linear`) |
| **∀-quantifier order** — quantifying inside the bundle what the paper quantifies outside. | `BetaCurveInputOffcentre*` quantified `hPz` over *all* `P : F → F[X]`; once the good set is nonempty and a representative exists, every `P` must equal it — unsatisfiable exactly in the served regime. Fix: per-`P` bundle with `P` a structure parameter (`∀ u … ∀ P, hP → bundle`). | Documented + repaired in `ArkLib/ToMathlib/OffcentreKeystoneAssembly.lean` (`Section5StrictDataOffcentreFin u P`) |
| **Uninhabited total functions** — demanding a total per-place witness from a genericity argument. | No discriminant `disc` with `disc.eval z ≠ 0 → Nonempty (rationalRoot (H̃′ H) z)` can exist: for `H̃′ = Y² − X` over odd `𝔽_q` the rooted places are exactly the squares, whose complement (≈ q/2 points) defeats any fixed-degree polynomial. The root must be *supplied* by the decoded geometry. | `RootSupplyOn` note in `ArkLib/ToMathlib/ConditionDiscProduct.lean` (documented counterexample); geometric supply in `ArkLib/ToMathlib/RationalRootSupply.lean` (`rationalRoot_of_matching_branch`) |
| **Codomain too small** — readings forced into `F[X]` when the paper's live in `RatFunc F`. | The `F[X]`-coefficient Claim 5.9 target forces `IsUnit H.leadingCoeff` at *every* degree (`d_H = 1` by denominator arithmetic, `d_H ≥ 2` by injectivity below the modulus); the `RatFunc`-codomain target holds unconditionally at `d_H ≤ 2`; `T²` escapes the RatFunc line at `d_H ≥ 3` (the sharp boundary). | `ArkLib/ToMathlib/ZLinearRatFuncDegreeOne.lean`: `isUnit_leadingCoeff_of_gammaGenuine_Z_linear_target_all`, `gammaGenuine_Z_linear_target_ratfunc_of_natDegree_le_two`, `functionFieldT_sq_no_ratfunc_T_repr`; `ZLinearClosureAudit.lean` |
| **Vacuous regimes** — hypotheses satisfiable only where the consumer never runs. | The small-field keystone route needs `\|F\| ≤ κ·2^(n−N)` — vacuous at deployment sizes. The faithful interface ships anti-vacuity witnesses; the strict-radius boundary branch is discharged outright (unreachable at `δ < 1 − √ρ`). | `curveFamilyData_self` / `curveFamilyData_const` / `curveFamilyData_self_nonaffine_exists` in `ArkLib/ToMathlib/CurveFamilyLines.lean`; `boundaryProbabilityResidual_of_strict` in `ArkLib/ToMathlib/CurveFamilyRoundConsumers.lean` |

## 2. Architecture map

**Spine** (all in `ArkLib/ToMathlib/FaithfulCurveExtraction.lean`): per-`(u, P)`
`CurveFamilyData` (centre `x₀`, ≤ `k + 1` coefficients `c_t ∈ F[X]`, per-`z` identity
`P z = ∑_{t<n} (z − x₀)^t • c_t` on the good set) → `curveCoeffPolys_of_curveFamily` →
`strictCoeffPolysResidual_of_curveFamilyData` → the keystone goal
`δ_ε_correlatedAgreementCurves` (defined in
`ArkLib/Data/CodingTheory/ProximityGap/Basic.lean`) via
`correlatedAgreement_affine_curves_johnson_of_curveFamilyData_strict`.

**Producer lanes** (feed `CurveFamilyData`):

- *Per-`z` Hensel*: `CurveFamilyHensel.lean` (`CurveHenselDatum`,
  `curveFamilyData_of_curveHenselDatum`); `CurveHenselDatumProducers.lean` (GS-interpolant and
  analytic producers, `curveHenselDatum_of_truncatedLocalRoot[_genuine]`);
  `HenselMatchingPolySupply.lean` (`InterpolantInput` → `henselDatum_of_interpolantInput`);
  `HenselApproxSupply.lean` (congruence fields are mechanical from order-0 agreement);
  `LocalHenselSeries.lean` / `TruncatedLocalRoot.lean` (the `π̂_z` local series and its
  truncation transport).
- *Per-`z` reading, closed*: `LocalSeriesBaseRationalReading.lean` derives `htrunc` from §5
  base-rationality (`htrunc_of_base_rational`, `curveFamilyData_of_baseRational`) — the per-`z`
  reading front is closed given base-rationality. `CurveSeriesTruncReading.lean`: the truncated
  descent is *canonical* (`eq_curvePoly_of_map_lift_eq_trunc`), and `trunc_reading_iff` shows
  the series route does not shrink the per-`z` residual — the remaining content is exactly
  identifying the decoded `P z` with the reading; two-series witnesses are unique at
  `d_H ≥ 2` (`zLinear_repr_unique`).
- *Weight/cardinality (graded collapse)*: `GSGradedBundle.lean` (grading conditions (iii)–(v)
  discharged for every bundle by re-grading `D`; residuals = (i) monic, (ii) `deg_Y R ≥ 2`);
  `GenuineMonicCapstone.lean` (signed collapse `hcardFin_of_graded_signed`);
  `NonmonicWeightCollapse.lean` — **monic is eliminated from this lane**: the honest budget
  `bW = (H.leadingCoeff).natDegree` is absorbed into the slope
  (`hcardFin_of_graded_signed_nonmonic`, `gradedCardBudgetW`), with the monic budgets recovered
  verbatim at `L = 0`. The only remaining monic-only front is the identity
  `gammaLocal = gammaGenuine` (`BetaRecGenuineBridge.lean`).
- *Discriminant assembly*: `ConditionDiscProduct.lean` — one product discriminant fires all
  per-`z` conditions (`discMatchingSet`, `card_discMatchingSet_gt`, the `gradedCardBudget`
  shape); `RootSupplyOn` is the named non-disc residual.
- *Tail*: `BetaTailDegreeVanishing.lean` — naive window propagation `[k, T] → T+1` is FALSE
  (small-part partitions survive); true propagation needs the full initial segment; the
  frontier consumes `htailBeyond`, conditionally discharged by `htailBeyond_of_lift_window`
  (in `FaithfulFrontierComposition.lean`).
- *Genuine identification*: `BetaRecGenuineBridge.lean` (`betaRec_BcoeffSigned_eq_βHensel`;
  for monic `H`, `gammaLocal_BcoeffSigned_eq_gammaGenuine_of_monic`);
  `GammaCoeffRecursion.lean` (from the proven root identity, the explicit Newton recursion
  `ζ · αGenuine (t+1) = −coeff (t+1) (eval (gammaTruncGenuine …) Q)`, machine-checked at
  order 1); `CurveFamilyGenuine.lean` (`gammaGenuine_eq_curve_sum`,
  `αGenuine_eq_zero_on_range_of_matching_monic`).
- *Claim 5.9 status*: `CurveFamilyZLinear.lean` (two-series curve form; target ⟺
  per-coefficient `Z`-degree ≤ 1, so the residual hides nothing); `ZLinearClosureAudit.lean` +
  `ZLinearRatFuncDegreeOne.lean` (see checklist rows above: the `F[X]`-target forces a unit
  leading coefficient at all degrees; `RatFunc`-target free at `d_H ≤ 2`; sharp escape at
  `d_H ≥ 3`).

**Frontier statement**: `ArkLib/ToMathlib/FaithfulFrontierComposition.lean` —
`FaithfulFrontierData` is the per-`(u, P)` bundle whose fields are *only* the named honest
residuals (graded bundle, monic/high-`Y`, separability, `fB` discriminant inputs, the one §6
field-size inequality, root supply, per-point matching data, tail-beyond, good-disc, `htrunc`,
divisibility, order-0 congruence); `curveFamilyData_of_faithfulFrontier` and
`correlatedAgreement_affine_curves_of_faithful_frontier` compose every proven lane so nothing
provable remains in the hypothesis list.

**Consumers**: `CurveFamilyLines.lean` (anti-vacuity witnesses; the Theorem 1.4 affine-lines
front door `RS_correlatedAgreement_affineLines_johnson_of_curveFamilyData_strict`; numeric
`epsCA` wrappers); `CurveFamilyRoundConsumers.lean` (WHIR
`roundKeystoneData_of_curveFamilyData`, FRI
`friPerRound_epsCA_le_roundError_of_curveFamilyData`, STIR
`stir_perRound_foldBudget_of_curveFamilyData` — each replacing a vacuous small-field route).

**The section-factor closure (2026-06-10, `GSSurfaceKeystone.lean`)**: the per-`(u, P)`
producer of `CurveFamilyData` is now PROVEN from a GS-construction-level interface.  The
route works at the section divisor `H := T − v(Z)` (the fiber-linear factor every
curve-carrying branch collapses to, by `BranchCollapse.lean`):

- `SectionFactor.lean` — `section_dvd_of_factorization`: GS factorization + per-place curve
  membership + counting budget force `(T − v) ∣ Hᵢ` for some irreducible factor (the §6
  pigeonhole composed with the polynomial-root bound);
- `SectionBaseRational.lean` — at fiber-linear factors every `𝒪`-class is structurally
  base-rational (canonical representative is fiber-constant);
- `SectionXiUnit.lean` — `SectionXiOrder` is PROVEN there: the `ξ`-representative is a unit
  (separability evaluated at the section), so the A.4 `+1`-order bookkeeping is unnecessary
  exactly where the §5 argument routes the proof;
- `GSSurfaceKeystone.lean` — the assembly: explicit curve coefficients (exact division),
  explicit total root (`rootSection v z := v.eval z`), `π_z(ξ) ≠ 0` at every place (unit
  content — no discriminant avoidance), and the front door
  `correlatedAgreement_affine_curves_of_GS_surface`:
  `δ_ε_correlatedAgreementCurves` at every `δ < 1 − √ρ` from a per-`(u, P)` `GSSurfaceData`
  producer.  All axiom-clean.

**The open core (current)**: producing `GSSurfaceData` per `(u, P)` from the in-tree GS
existence chain (`modified_guruswami_has_a_solution`, `pg_Rset`, the graph route).  The named
supplies still open there: `SurfaceSeparabilitySupply` (trivariate `R.Separable`; only the
linear case is producible), the per-`z` GS cargo (`hdvdP`/`hcong` — the
`dvd_specialization_of_close` lane), the tail-window conditions feeding `htail`, and the
degree bounds `hdegc`.  The closed-radius boundary branch is settled negatively:
`BoundaryCardResidual` is machine-refuted as stated
(`BoundaryCardResidualRefutation.lean`), so the strict front door is the maximal honest
keystone.

## 3. Working conventions that proved load-bearing

- **Scratch-iterate in `/tmp`**, verify with `timeout 580 lake env lean <path>` from the repo
  root; only `cp` into the tree when green, then re-verify in place. Never leave a broken
  intermediate in the tree: the shared checkout autosyncs to `main` and will grab it.
- **Axiom-audit footers**: end every file with `#print axioms <decl>` for each public
  declaration; expected output is exactly `[propext, Classical.choice, Quot.sound]`.
- **Anti-vacuity witnesses ship with every new interface** (the `curveFamilyData_self`
  pattern). A bundle nobody can instantiate is a statement bug, not a contribution; an
  inhabitant that exercises the previously-refuted regime (here: non-affine codeword degree)
  is the regression test.
- **Honest residuals**: a residual must (a) not be the goal restated, (b) be a named `Prop`
  (never an axiom), (c) come with a proven consumer that strictly extends it. Refutations of
  the *old* statement stay in-tree next to the repair (`no_linRep_of_nonaffine`).
- **Check fleet files before assuming gaps**: multiple agents work this surface concurrently;
  `ls ArkLib/ToMathlib | grep -i <topic>` and `git log --oneline -20` first. After pushing,
  re-verify the landed content (`git show <remote>/main:<file>`) — autosync can interleave.

## 4. The Claim 5.9 statement-archaeology (2026-06-10/11)

Recorded after three independent sessions converged on the same verdicts; the full trail is
on issue #304 (comments of 2026-06-10, 20:08Z onward).

- **The per-order weight-1 invariant was a phantom.** `AlphaGenuineRegularWeightLe`
  (`Λ(α_t) ≤ 1` per order, issue #138) is a statement BCIKS20 never makes: Claim A.2's
  budget is *linear in t* (`Λ(β_t) ≤ 1 + (t+1)Λ(W) + e_t·Λ(ξ)`), and the paper's
  `Λ(α_t) = Λ(Y) = 1` sentence is motivation, not a load-bearing step.  The in-tree
  machine refutations (`P1MonicWeightRefutation`, `XDegreeBudgetProbe.graded_rescue_dead`)
  refuted the phantom, not the paper.  A consumer audit confirmed nothing downstream needs
  the sharp constant — every site survives any fixed or linear-in-t budget.
- **Weight-1 is an output, not an input.** It holds for the *final interpolated*
  coefficients (ground-line `v₀ + Z·v₁` sections, weight ≤ 1 by construction) under the §5
  counting hypotheses — and is *false* under bare `ClaimA2.Hypotheses` (the refutation
  witnesses carry no counting package).  When formalizing a paper remark, locate which
  hypotheses scope it before carving it into an interface.
- **Claim 5.9 is a curve collapse.** The §5 counting package forces `d_H = 1`
  (`Claim59GroundLine.claim59_curve_collapse`); the 2025 rewrite
  ("On Proximity Gaps for Reed–Solomon Codes", math.toronto.edu/swastik) states the step-4
  conclusion outright as `R(X,Y,Z) = Y − P(X,Z)`.  Consequence: `d_H ≥ 2` producer lanes
  (`hrepT` ab initio at `d_H = 2`) are off the end-to-end path
  (`counting_package_empty_of_two_le_natDegree`); production targets the `d_H = 1` lane.
- **The paper-faithful route** (landed as `GroundLineInterpolation.lean`,
  `ClearedGammaDefect.lean`, `Claim59GroundLine.lean`, `Claim59GroundLineWiring.lean`):
  eq.-(5.16) defect element cleared into `𝒪` → linear budget bound → `Lemma_A_1` kill per
  coordinate (Claim 5.10) → `k+1`-point ground-line interpolation (Claim 5.9) → corollaries
  (T-form target, #138 invariant under counting, curve collapse).  The per-place reading
  comes from `localSeries_eq_aPTaylor` (+ `_sliced`) with witness `p := taylor x₀ P`; the
  budget from `betaRec_weight_le_graded_signed` through the `betaRec = βHensel` bridge; the
  coordinates from the `Claim511` double-counting core.
- **The 2025 rewrite's footnote-5 omission** (content `C(X,Z)` vanishing absorbing
  proximate roots in BCIKS20 step 3) is already handled in-tree:
  `GSFactorAssignment.exists_specialized_factor_assignment` excludes content-vanishing
  places via a cofinite bad set.  The formalization was sound where the 2020 prose was not.
