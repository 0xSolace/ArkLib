# Paper Audit: Open Problems in List Decoding and Correlated Agreement

Paper-to-ArkLib audit for *Open Problems in List Decoding and Correlated
Agreement* (Arnon, Boneh, Fenzi; April 8, 2026). Lists the paper's named
formal items and records whether each one is currently present in ArkLib,
missing, or present in a materially different form.

This audit is the **status snapshot** — the canonical paper-to-Lean map. The
forward-looking phased plan and review logs are kept as local working notes
(out of the PR by design); this document records only what is present in the
tree.

Every per-item PR is expected to update this audit row in the same
commit.

The **canonical reference** for this work is the upstream LaTeX source,
`ef-millenium/ef-millenium.tex` (the authors' repo, kept as a local clone and
refreshed with `git -C ef-millenium pull`), **not** the static `ABF26.pdf`
snapshot — the `.tex` tracks edits the PDF predates (e.g. the §4.5 MCA
conjecture and Appendix C). Cited works are tracked against the authoritative
`ef-millenium/references.bib`; the audit refers to the paper by its short name
`ABF26` (eprint 2026/680).

## Metadata

- **Paper**: ABF26 — *Open Problems in List Decoding and Correlated Agreement* (eprint 2026/680)
- **Canonical source**: `ef-millenium/ef-millenium.tex` (upstream author repo, local clone; `git -C ef-millenium pull` to refresh)
- **Bibliography of record**: `ef-millenium/references.bib`
- **Audit owner**: ABF26 formalization (PR #505)

## Status Legend

- `present`: close match in ArkLib, no `sorry` blocking it.
- `present-but-different`: underlying concept exists, but the interface,
  statement shape, or abstraction level differs materially from the paper.
- `present-but-incomplete`: the relevant theorem/symbol exists, but the
  current Lean surface still depends on an explicit residual hypothesis,
  external `Prop`, or theorem family. This status does not imply a raw
  `sorry` proof hole in the current tree; use `scripts/sorry_census.py` for
  the raw-hole census.
- `missing`: no close formalization was found.
- `deferred`: in scope of a later phase per the plan; not currently worked
  on.

## Notes

- Rows follow the theorem-like items extracted from the PDF, plus named
  facts and remarks when they materially affect the comparison.
- The **ABF26 ID** column matches the `ABF26-*` identifiers used by Lean
  docstrings, external `Prop` declarations, and residual comments (e.g.
  `D2.13`, `T4.13`, `L4.6`). Older references to raw proof-hole tags are
  historical.
- The **Lean target** column gives the canonical declaration name. For
  `present` rows this is the existing name; for other rows it is the proposed
  name.
- The **Lean refs** column lists existing declarations and the files
  containing them.
- "External" Lean target rows reference results the paper itself states
  without proof or whose source-paper proof is not yet formalized in ArkLib.
  Current rows use `Prop` declarations, proved reductions with explicit
  residual hypotheses, or ordinary theorems; they are not raw `sorry` holes
  unless the census says otherwise.
- 2026-06-06 residualization check: on clean `fork/main`,
  `python3 scripts/sorry_census.py` reports `holes = 0`,
  `files_with_holes = 0`, and `decls_with_holes = 0`. Historical raw-line
  references below are kept only as breadcrumbs when explicitly marked.

## Drift since last audit

Three rows the previous audit flagged as `present-but-incomplete` are now
fully sorry-free, thanks to PR #385 (AHIV22, 2026-04-24), PR #463 (BCIKS20
`ReedSolomonGap`, 2026-04-30), and commit `6389c0e` (BCIKS20
`AffineSpaces`, 2026-05-05; pushed directly with no associated PR
number). Those rows are re-tagged `present` below. The older
AffineLines raw-line and proximity-gap proof-hole inventories are now
superseded by the zero-hole census and by named residual interfaces such as
`StrictCoeffPolysResidual`, `BoundaryCardResidual`,
`BoundaryCardLatticeResidual`, and the issue-indexed ABF26 theorem-family
`Prop`s. Two supporting files relevant to the Phase 1 ε-error migration and
the still-open non-unique-decoding/residualized branch:
[`ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean`](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean)
(smooth-domain FFT infrastructure, added 2026-04-17 in PR #448) and
[`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/JointAgreement.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/JointAgreement.lean)
(bivariate-existence lemmas, added 2026-03-11 by `b333f6ba`).

**This-PR additions** (`feat/abf26-plan` branch): three in-tree sorries
discharged in proof-discharge passes after the statement layer landed:
`dim_irsCode` (D2.13 dim formula, commit `3b0cfc99`),
`hammingBallVolume_eq_ncard_hammingBall` and its sub-sorries
`card_filter_hammingDist_eq` (`c01232f3`) and the Set/Finset card conversion
(`13f02444`) for D2.4, and `minDist_div_card_eq_minRelHammingDistCode`
(`3f344a00`, via a `Set.Finite.toFinset` refactor of `minRelHammingDistCode`
to dodge a `Fintype.ofFinite` instance diamond). Several new bridge lemmas
land in `Basic/LinearCode.lean` (`IsMDS_iff_singleton_bound_tight`),
`Basic/RelativeDistance.lean` (the `minDist_div_card` bridge above plus
characterisation lemmas for `minRelHammingDistCode`), and
`Whir/MutualCorrAgreement.lean` (`proximityCondition_imp_mcaEvent_affineLine`
and the probability-level `Pr_proximityCondition_le_epsMCA`, one-way bridges
documenting the WHIR↔ABF26 MCA asymmetry recorded in commit `d01117c8`).

## Section 1 — Grand Challenges (introduction)

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `GC1` | Grand MCA Challenge (page 5): "determine the largest `δ*_C ∈ [0, 1]` such that `ε_mca(C, δ*_C) ≤ ε*`" | present (as predicate) | `ProximityGap.grandMCAChallenge` in [GrandChallenges.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean) | existing | Stated as a generic `Prop`-valued predicate over a `LinearCode ι F` and a threshold `ε* : ℝ≥0`. **Phase-1 instantiation framework (2026-06-03):** RS targets `grandMCAChallengeRS` / `grandMCAChallengeRSrate`, prize regime `prizeRates` (= {1/2,1/4,1/8,1/16}) + `epsStar` (= 2^-128) + `mcaPrize`, witness-carrying `GrandMCAResolution` with one-sided `MCALowerWitness`/`MCAUpperWitness` (bound any resolution's `δ*` via `epsMCA_mono`), and bridges from `CapacityBounds` (`MCALowerWitness.ofLe`/`ofJohnsonBCHKS25`, `MCAUpperWitness.ofGt`/`ofEpsCAGt`). Resolution is open. |
| `GC2` | Grand List Decoding Challenge (page 5): "determine the largest `δ*_C ∈ [0, 1]` such that `\|Λ(C^≡m, δ*_C)\| ≤ ε* · \|F\|`" | present (as predicate) | `ProximityGap.grandListDecodingChallenge` in [GrandChallenges.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean) | existing | Stated as a generic `Prop`-valued predicate. Uses `ListDecodable.Lambda` for `\|Λ(C^≡m, ·)\|` (ABF26 D2.8). **Phase-1 mirror (2026-06-03):** `grandListDecodingChallengeRS` + `listDecodingPrize`, witness-carrying `GrandListResolution` with `ListLowerWitness`/`ListUpperWitness` (bound `δ*` via `lambda_coe_mono` from `Lambda_mono`). Resolution is open. |

## Section 2 — Preliminaries

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `L2.1` | Polynomial identity lemma | present | `prob_polynomial_identity_le`, `prob_schwartz_zippel_mv_polynomial_of_totalDegree_le`, `MvPolynomial.totalDegree_le_of_degreeOf_lt` in [Instances.lean](../../../ArkLib/Data/Probability/Instances.lean); `schwartz_zippel_of_fintype` in [Interpolation.lean](../../../ArkLib/Data/MvPolynomial/Interpolation.lean) | `prob_polynomial_identity_le` | Paper bound `m·(d-1)/|F|` for individual-degree-`<d` polynomials, realised as `prob_polynomial_identity_le`. Derived from the generalised Schwartz-Zippel wrapper `prob_schwartz_zippel_mv_polynomial_of_totalDegree_le` (which takes any `d ≥ totalDegree P`) via the `MvPolynomial.totalDegree_le_of_degreeOf_lt` helper. The legacy specialisation `prob_schwartz_zippel_mv_polynomial` (bound `≤ n / \|F\|` when `totalDegree ≤ n`) is preserved as a one-line wrapper. |
| `D2.2` | q-entropy function `H_q` | present | `CodingTheory.qEntropy` in [Entropy.lean](../../../ArkLib/Data/CodingTheory/Basic/Entropy.lean) | existing | `noncomputable def`; uses Mathlib's `Real.logb`. Boundary case `qEntropy q 0 = 0` is a `@[simp]` lemma. |
| `D2.3` | Restricted Hamming distance `Δ_T` | present | `CodingTheory.restrictedRelHammingDist` in [RelativeDistance.lean](../../../ArkLib/Data/CodingTheory/Basic/RelativeDistance.lean); existing full-domain `Δ₀`/`δᵣ` in [Distance.lean](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean) and [RelativeDistance.lean](../../../ArkLib/Data/CodingTheory/Basic/RelativeDistance.lean) | existing | `ℝ≥0`-valued; `T = ∅` gives `0` via `NNReal`'s `0/0 = 0`. |
| `D2.4` | Hamming-ball volume `Vol_q(δ,n)` | present | `CodingTheory.hammingBallVolume` in [HammingBallVolume.lean](../../../ArkLib/Data/CodingTheory/HammingBallVolume.lean); supporting `hammingBall`/`relHammingBall` sets in [ListDecodability.lean](../../../ArkLib/Data/CodingTheory/ListDecodability.lean) | existing | `noncomputable def` (depends on `Nat.floor` over `ℝ`). Boundary case `Vol_q(0, n) = 1` is a `@[simp]` lemma. |
| `D2.5` | ECC, `δ_min`, rate | present-but-different | `Code.dist`, `Code.minDist` in [Distance.lean](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean); `LinearCode.rate` in [LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean); bridge `minDist_div_card_eq_minRelHammingDistCode` and supporting `minRelHammingDistCode` in [RelativeDistance.lean](../../../ArkLib/Data/CodingTheory/Basic/RelativeDistance.lean) linking the raw `Code.minDist C / n` form to `δᵣ C` (proved, via `Set.Finite.toFinset` refactor of `minRelHammingDistCode`) | existing | Paper uses `C ⊆ Σ^n`; ArkLib uses function spaces. Mathematically equivalent. Paper-style `δ_min` / `ρ` scoped-notation file was once planned but never materialised — call sites use `Code.minDist C / Fintype.card ι` and `LinearCode.rate` directly. |
| `L2.6` | Singleton bound | present | `singleton_bound`, `singleton_bound_linear`, `IsMDS` predicate (from PR #430), and `IsMDS_iff_rate_distance` bridge in [LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean) | existing | `IsMDS LC` encodes the additive Nat Singleton-tight condition `Code.dist LC.carrier = length LC - dim LC + 1`; the bridge `IsMDS_iff_rate_distance` connects it to the rate-distance form `δ_min(LC)/n = 1 - dim/n + 1/n` used by ABF26 §2-§3. |
| `D2.7` | F-additive code | present-but-different | `ModuleCode`, `LinearCode` in [LinearCode.lean](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean) | use `ModuleCode ι F (Fin s → F)` directly | `ModuleCode` / `LinearCode` *bake in* F-linear subspace structure — the paper's "F-additive" notion is realised by these existing types. Theorems quantifying over a paper-style "F-additive `Set`-coded code `C`" can write `∃ MC : Submodule F (ι → A), (MC : Set _) = C` inline rather than via a dedicated paper-shape predicate; ArkLib convention avoids alias-style wrappers for items already realised by existing types. |
| `D2.8` | `Λ(C,δ,f)` and `\|Λ(C,δ)\|` | present | `ListDecodable.closeCodewordsRel` (= point list `Λ(C,δ,f)`), `ListDecodable.Lambda`, `closeCodewordsRel_subset_of_le`, `Lambda_mono`, `Lambda_le_ncard` in [ListDecodability.lean](../../../ArkLib/Data/CodingTheory/ListDecodability.lean) | existing | The point list `Λ(C,δ,f)` is the pre-existing `closeCodewordsRel C f δ` (no paper-shape alias: the `Lambda_at` abbrev was removed 2026-05-31). `Lambda` is the new `ℕ∞`-valued maximised list size `\|Λ(C,δ)\|`. |
| `D2.9` | `m`-interleaved code `C^≡m` | present-but-different | `interleavedCodeSet`, `codewordStackSet` in [InterleavedCode.lean](../../../ArkLib/Data/CodingTheory/InterleavedCode.lean) | existing + `scoped notation "_^≡_"` | Matrix-based API; paper uses tuple notation. |
| `L2.10` | `\|Λ(C^≡m,δ)\| ≤ binom(b+r,r)·\|Λ\|^r` | stated (external Prop) | `InterleavedCode.lambda_le_ggr11` in [InterleavedCode.lean](../../../ArkLib/Data/CodingTheory/InterleavedCode.lean) | same | Prop-valued GGR11 recursion statement. In-tree carrier/list-size infrastructure and the leaf-counting reduction are proved; the remaining external wall is the named Erase-Decode tree structure `InterleavedCode.GGR11.GGR11TreeStructure` tracked by #73. |
| `D2.11` | Reed-Solomon code `RS[F,L,k]` | present-but-different | `ReedSolomon.code` in [ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean) | existing + `scoped notation "RS[" F ", " L ", " k "]"` | Parameterised by injection `ι ↪ F` rather than `L ⊆ F`. Strictly more general. |
| `D2.12` | Smooth domain | present | `ReedSolomon.Smooth` in [ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean) | existing | Verified: typeclass requires multiplicative coset of a subgroup with order a power of two. New companion file [FftDomain.lean](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean) provides FFT-domain machinery; not a paper-item match but noted here for completeness. |
| `D2.13` | s-interleaved RS `IRS[F,L,k,s]` | present | [ReedSolomon/Interleaved.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/Interleaved.lean) | `ReedSolomon.Interleaved.irsCode`, plus `dim_irsCode` (proved) | Defined as `interleavedCodeSet (RS[F, L, ⌊k/s⌋])`. Dimension formula `dim(IRS) = s · (k/s)` proved via injective F-linear `(Fin s → ↥RS) → (ι → Fin s → F)` + `finrank_pi_fintype`. |
| `D2.14` | `(L,s)`-admissible field element | present | [ReedSolomon/Folded.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean) | `ReedSolomon.Folded.Admissible` | Required by D2.15. |
| `D2.15` | Folded RS `FRS[F,L,k,s,ω]` | present | [ReedSolomon/Folded.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean) | `ReedSolomon.Folded.frsCode` | Used pervasively in §3, §4, §6.3.2. |
| `D2.16` | τ-subspace-design code | present | [SubspaceDesign.lean](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean) | `CodingTheory.IsSubspaceDesign` | GX13 definition; uses `LinearMap.proj` for `A_i`. |
| `L2.17` | `min τ(r) ≥ ρ − 1/n` | present | [SubspaceDesign.lean](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean) | `CodingTheory.subspaceDesign_tau_lower` | GG25 lower-bound lemma proved in-tree, with the repaired nontrivial-code and `r ∈ [s]` hypotheses documented in the theorem docstring. |
| `T2.18` | FRS and UM are subspace-design | present-but-incomplete | [SubspaceDesign.lean](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean) | `CodingTheory.frs_is_subspaceDesign_gk16` | FRS half is residualized: `frs_is_subspaceDesign_gk16` consumes the explicit `GK16DegreeBudget`; the discharged `_of_injective` and `_of_admissible` variants close common call surfaces. UM half remains deferred. |
| `D2.19` | Extension field presentation `(B,F,e,ψ,φ)` | present | [ExtensionCodes.lean](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean) | `CodingTheory.ExtensionFieldPresentation` (structure wrapping `[Algebra B F]` + `Basis (Fin e) B F`), plus `IsSystematic` for the systematic variant. | Refactored to wrap Mathlib's `Algebra B F` + `Basis (Fin e) B F` directly (no parallel implementation of the field embedding / coordinate iso). `ψ := algebraMap B F`, `φ := basis.equivFun`, `coord j := proj j ∘ φ`. Univariate-multiplicity code (paper's namesake `DA.7`) is a *different* item, despite sharing a number. |
| `D2.20` | Extension code `C_F` | present | [ExtensionCodes.lean](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean) | `CodingTheory.extensionCode` (Set form) + `CodingTheory.extensionCodeSubmodule` (Submodule form, mirroring `ReedSolomon.code`'s shape in [ReedSolomon.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean)) | Set-level definition; uses coordinate-projections `P.coord j` of D2.19. **All closure laws proven**: `extensionCode_add_mem` (addition), `extensionCode_psi_smul_mem` (B-side scalar via `ψ`), and `extensionCode_smul_mem` (F-scalar closure, paper's D2.20 F-linearity claim, closed via basis-expansion through `Basis.sum_equivFun` + `Finset.sum_induction`). The Submodule packaging `extensionCodeSubmodule` bundles all three into a `Submodule F (ι → F)` (consumed by downstream code that wants a linear-code type; `coe_extensionCodeSubmodule` is the carrier bridge). Distance equality `δ_min(C_F) = δ_min(C_B)` from DP25 not formalised — separate paper item. |
| `L2.21` | `\|Λ(C_F,δ)\| = \|Λ(C_B^e,δ)\|` | present | [ExtensionCodes.lean](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean) | `CodingTheory.lambda_extensionCode_eq_lambda_interleaved` | BCFW25 Lemma D.3 proved in-tree via the coordinate isometry `extensionCoordEquiv`. |

## Section 3 — List Decoding

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `D3.1` | Johnson functions `J_{q,ℓ}`, `J_q`, `J` | present | existing `J` in [JohnsonBound/Basic.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean) (which matches paper's `J_q`); new `JohnsonBound.Jqℓ` and `JohnsonBound.Jcap` in [JohnsonBound/Family.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Family.lean) | `JohnsonBound.Jqℓ`, `JohnsonBound.J` (= paper `J_q`), `JohnsonBound.Jcap` | All three functions present. Limit relationships documented in docstrings; not formalised (paper does not prove them either). |
| `T3.2` | Johnson bound (Joh62) | stated (external Prop; in-tree proof available) | absolute-distance form `johnson_bound`, `johnson_bound_alphabet_free` in [JohnsonBound/Basic.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean); paper-shaped `johnson_bound_lambda_le_ell` in [JohnsonBound/Family.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Family.lean) | `CodingTheory.johnson_bound_lambda_le_ell` | Paper-shaped statement is present as an explicit external surface; porting the existing absolute-distance proof to `Lambda`-form is tracked separately. |
| `C3.3` | MDS coarse Johnson | stated (external Prop) | [JohnsonBound/Family.lean](../../../ArkLib/Data/CodingTheory/JohnsonBound/Family.lean) | `CodingTheory.mds_johnson_lambda_le` | Derivable from L2.6 + T3.2 via `Jcap` form once the paper-shaped Johnson wrapper is closed. |
| `T3.4` | τ-subspace-design list decoding | stated (external Prop) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.subspaceDesign_list_decoding_cz25` | Prop-valued CZ25 Thm B.5 statement. The `_of_residual` theorem proves the packaging from the explicit dimension-count residual; the external content is the CZ25 design-to-`Λ` conversion. |
| `C3.5` | Folded RS up to capacity | stated (external Prop) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.frs_list_decoding_capacity_cz25` | Prop-valued CZ25 Cor 2.21 statement. The `_of_residuals`/`_of_residuals_prop` reductions derive it from T3.4 plus T2.18 residual inputs. |
| `T3.6` | Random RS near capacity | stated (external Prop) | [Probability/Combinatorial.lean](../../../ArkLib/Data/Probability/Combinatorial.lean), [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.random_rs_list_decoding` | AGL24 Thm 1.1. The random-domain probability space is now present as `Probability.SizeSubset` / `uniformSizeSubsetOfLe`, with support/cardinality/equiv helpers and `SizeSubset.toEmbedding` for `RS[F,L,k]`. The AGL24 probability bound and concrete parameter instantiation remain external. |
| `L3.7` | Elias volume bound | present | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.linear_lambda_ge_elias_volume_eli57` | Eli57 volume lower bound proved in-tree using `hammingBallVolume`. |
| `C3.8` | Volume-based lower bound | present | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.linear_lambda_ge_entropy_volume` | Proved in-tree in the repaired lattice-point form, using `qEntropy` and the Elias-volume theorem. |
| `T3.9` | Generalized Singleton bound | present | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.linear_C_le_generalized_singleton_st20` | ST20 Thm 1.2 proof restored in-tree. |
| `T3.10` | Large-alphabet lower bound | stated (external Prop) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.large_alphabet_barrier_bdg24_agl23` | Prop-valued BDG24/AGL23 statement; the counting/descent reductions are isolated, with the AGL23 extraction theorem family remaining external. |
| `T3.11` | Random linear code lower bound | stated (external Prop; split issue) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean), [ExternalDebt.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/ExternalDebt.lean) | `CodingTheory.random_linear_lambda_lower_glmrsw22` | Prop-valued GLMRSW22 statement. The random-generator-matrix probability space is now in-tree via `uniformRandomLinearGeneratorMatrix`, `uniformRandomLinearCode`, and `randomLinearLambdaLowerProbability`, with `random_linear_lambda_lower_glmrsw22_of_random_generator_matrix` reassembling positive-probability witnesses into the legacy existential front door. The remaining #79 theorem is the GLMRSW22 first-moment count over that probability space. |
| `T3.12` | RS superpoly over extensions | stated (external Prop) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.rs_lambda_superpoly_extension_bkr06` | Prop-valued BKR06 statement. The `_of_residuals` and narrowed injection/family forms prove all packaging around the named geometric/numeric residuals. |
| `T3.13` | RS large list over prime fields | stated (external Prop) | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.rs_lambda_large_prime_ghsz02` | Prop-valued GHSZ02 statement. The `_of_residuals` and injection forms isolate the asymptotic/geometric construction residual. |
| `T3.14` | Large-rate RS lower bound | present | [ListDecoding/Bounds.lean](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean) | `CodingTheory.rs_lambda_high_rate_jh01` | JH01 Thm 2 repaired to the actual list-size separation and proved in-tree. |
| `T3.15` | CW07 hardness barrier | out of scope | none | `CodingTheory.rs_dlog_barrier` (external; not stated) | Algorithmic hardness (discrete-log reduction); we formalise combinatorial statements only. |

## Section 4 — Correlated Agreement Conjectures

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `D4.1` | `ε_ca(C,δ_fld,δ_int)` | present | `ProximityGap.epsCA`, `epsCA'`, `epsCA_curves`, `epsCA_affineSpaces`, `epsCA_mono_δ_fld`, `epsCA_antitone_δ_int`, three bridges `δ_ε_correlatedAgreement{AffineLines,Curves,AffineSpaces}_iff_epsCA{_,_curves_,_affineSpaces_}le` in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean); coexisting predicate API in [Basic.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean) | existing | Definition, monotonicity in both arguments, and bridges to all three predicate-style API variants (`AffineLines`, `Curves`, `AffineSpaces`) closed. |
| `R4.2` | ε_ca discretization | present | `ProximityGap.epsCA_eq_of_floor_eq` in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean) | existing | General "level set" form proved (`⌊δ_int · n⌋ = ⌊δ_int' · n⌋ → ε_ca's agree`). The paper's `β`-shift idiom is a corollary when `δ_int` is a multiple of `1/n`. |
| `D4.3` | `ε_mca(C,δ)` | present | `ProximityGap.epsMCA`, helper preds `ProximityGap.pairJointAgreesOn`, `ProximityGap.mcaEvent` in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean); WHIR-specific `hasMutualCorrAgreement` still in [Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean) | existing | Code-theory MCA definition closed. The WHIR `hasMutualCorrAgreement` re-expression as a specialization of `epsMCA` is a follow-up commit. |
| `R4.4` | MCA with proximity loss intentionally undefined | present | file docstring in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean) | docstring | Documentation only; documented in the "Note on MCA with proximity loss" subsection of the file docstring. |
| `F4.5` | `ε_pg ≤ ε_ca ≤ ε_mca` | present | `ProximityGap.epsPG`, `ProximityGap.epsPG_le_epsCA`, `ProximityGap.epsCA_le_epsMCA`, `ProximityGap.epsPG_le_epsCA_le_epsMCA`, plus helper `ProximityGap.jointProximity_imp_line_close` in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean) | existing | Closed in stages; proved for `Submodule F (ι → A)`. |
| `L4.6` | `ε_mca = ε_ca` below `δ_min/2` | present; RS route reduced | `ProximityGap.epsMCA_eq_epsCA_below_udr` in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean), `epsMCA_eq_epsCA_below_udr_rs` in [ToMathlib/L46DiffStackRS.lean](../../../ArkLib/ToMathlib/L46DiffStackRS.lean) | existing | The abstract theorem still consumes the explicit residual `diffStackMCAResidualBelowUDR`; the Reed-Solomon route is reduced to the named GS-witness lower-bound input. The bare abstract-code dominance is documented as false off that structured route. |
| `L4.7` | `ε_mca(C^≡t,δ) ≤ t·ε_mca(C,δ)` | present | `ProximityGap.epsMCA_interleaved_le` plus local helper `ProximityGap.Pr_exists_Fin_le_sum` (union-bound for finitely-indexed existentials) in [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean) | existing | Proved via row-decomposition of the interleaved `mcaEvent` plus the `Pr_exists_Fin_le_sum` union bound. |
| `T4.8` | AHIV17 general-code unique-decoding | present (UDR regime proven; `d/q` tightening residual) | [`ProximityGap/AHIV22.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/AHIV22.lean) (sorry-free), [ProximityGap/Errors.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean), [`BCIKS20/AffineLines/UniqueDecoding.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/UniqueDecoding.lean) | `ProximityToRS.ahiv17_epsCA_bound_uniqueDecodingRegime` | For `δ ≤ relUDR`, `epsCA (RScodeSet α deg) δ δ ≤ errorBound δ deg α` is fully proven (no residual): the BCIKS20 affine-lines base case discharges `ahiv17_affineLine_correlatedAgreement_residual` and routes through the `epsCA` bridge. This lands the `n/q` UDR error bound; the tighter AHIV17 `d/q = ‖RS‖₀/q` bound from `prob_of_bad_pts` still needs the row-span → affine-line specialization, tracked by the named residual. |
| `T4.9.1` | RS unique-decoding Item 1 (BCIKS20 Thm 1.4) | present-but-incomplete | [`BCIKS20/AffineLines/UniqueDecoding.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/UniqueDecoding.lean), [`AffineLines/Main.lean`](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/Main.lean) | `ABF26.rs_epsMCA_uniqueDecoding` | The unique-decoding branch is proved. The list-decoding/Johnson branch is residualized through `StrictCoeffPolysResidual`, `BoundaryCardResidual`, and the narrower `BoundaryCardLatticeResidual` variants; the old raw line reference is superseded. |
| `T4.9.2` | RS unique-decoding Item 2 (BCHKS25 Thm 1.3) | stated (external Prop; split issue) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.rs_epsCA_bchks25_item2` | Prop-valued BCHKS25 Thm 1.3 statement, tighter than T4.8 in the `δ_min/3`-to-Johnson regime. The RS interpolation/counting proof is tracked by #87. |
| `R4.10` | Small proximity-loss simplification | stated (derived external Prop; split issue) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.rs_epsCA_small_loss_r4_10` | Derived Prop statement. The `rs_epsCA_small_loss_r4_10_of_residuals` reduction and floor side condition are proved; it closes once T4.9.2 is supplied, tracked with #87. |
| `T4.11` | 1.5-Johnson regime general linear | stated (external Prop, 2 items; split issue) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.linear_epsMCA_1_5_johnson_gkl24`, `CodingTheory.linear_epsCA_1_5_johnson_bgks20` | Prop-valued GKL24 Thm 3 and BGKS20 Lem 3.2 statements. The cube-root list count and eta-margin union-bound work are tracked by #84. |
| `T4.12` | Johnson-range RS MCA | stated (external Prop; split issue) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean), [Hab25Johnson.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Hab25Johnson.lean) | `CodingTheory.rs_epsMCA_johnson_range_bchks25` | Prop-valued BCHKS25 Thm 4.6 statement. Existing WHIR conjecture is a different shape; adjacent Hab25 algebra is #68, while the public CapacityBounds front door is tracked by #85. |
| `T4.13` | MCA from τ-subspace-design | stated (external Prop; split issue) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.subspaceDesign_epsMCA_gg25` | Prop-valued GG25 Cor 4.9 statement using `IsSubspaceDesign`; upstream list-decoding/line-stitching residuals are tracked by #86. |
| `T4.14` | Folded RS MCA up to capacity | stated (external Prop; split issue) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.frs_epsMCA_capacity_gg25` | Prop-valued GG25 Cor 4.10 statement. The `_of_residuals`/`_of_residuals_prop` reductions derive it from T4.13 plus T2.18; the instantiation is tracked with #86. |
| `BCGM25` (extends T4.13/T4.14) | Polynomial-generator MCA | present (#76 resolved 2026-06-06; generator-native API plus compatibility shadow) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean), [ProximityGenerators.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/ProximityGenerators.lean), [MCAGenerator.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGenerator.lean) | `CodingTheory.polynomialGenerator_isMCAGenerator_bcgm25`, `CodingTheory.subspaceDesign_epsCA_curves_polynomial_generators_bcgm25`, `CoreDefinitions.IsPolynomialGenerator`, `CoreDefinitions.IsMCAGenerator` | BCGM25/BSGM25 (footnote 2 of ABF26 intro). The canonical CapacityBounds front door now uses the in-tree generator framework (`Generator`/`IsPolynomialGenerator`/`IsMCAGenerator`). The old `epsCA_curves … k` statement is retained only as an ABF26 survey-ledger compatibility shadow because there is not yet a checked bridge from scalar-code `IsMCAGenerator` to vector-alphabet curve CA. |
| `T4.15` | Random RS MCA up to capacity | stated (external Prop) | [Probability/Combinatorial.lean](../../../ArkLib/Data/Probability/Combinatorial.lean), [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.random_rs_mca` | GG25 Thm 5.15. Uses `Pr_{L ← uniformSizeSubsetOfLe F n hn}` over size-`n` random RS domains and `SizeSubset.toEmbedding` for the evaluation-domain injection. The GG25 MCA probability bound and concrete `bound`/`failure` values remain external. |
| `T4.16` | CA lower bound near capacity | stated (external Prop; split issue; witness package named) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean), [GrandChallenges.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean) | `CodingTheory.rs_epsCA_lower_capacity_bchks25_kk25`, `CodingTheory.RSLowerCapacityWitness`, `CodingTheory.rs_epsCA_lower_capacity_bchks25_kk25_of_witness`, `ProximityGap.GrandChallenges.MCAUpperWitness.ofLowerCapacityBCHKS25KK25` | Prop-valued BCHKS25+KK25 statement. `Θ(1/log n)` slack is existentially packaged; the witness package and Grand-MCA upper-witness adapter are in-tree, while the near-capacity bad-code construction remains tracked by #81. |
| `T4.17` | Complete CA breakdown | stated (external Prop; split issue) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean) | `CodingTheory.rs_epsCA_breakdown_cs25`, `CodingTheory.rs_epsCA_breakdown_cs25_entropyBallLowerWitness` | Prop-valued CS25 Cor 1 statement using `qEntropy`; the `≤ 1` half is routine and the named `entropyBallLowerWitness` isolates the hard `≥ 1` target for the qEntropy/RS-ball-count proof tracked by #82. |
| `T4.18` | CA jump at Johnson bound | stated (external Prop; split issue; numeric front door named) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean), [GrandChallenges.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean) | `CodingTheory.rs_epsCA_johnson_jump_bchks25`, `CodingTheory.RSJohnsonJumpWitness`, `CodingTheory.johnsonJumpRadius_eq_three_fourths`, `CodingTheory.johnsonJumpInternalRadius_eq_seven_eighths_add_inv`, `ProximityGap.GrandChallenges.MCAUpperWitness.ofJohnsonJumpBCHKS25AutoRadius` | Prop-valued BCHKS25 Cor 1.7 statement. The witness package and Grand-MCA upper-witness adapter are in-tree; `J(15/16)=3/4` and the internal radius `7/8 + 1/n` are checked. The char-2 witness-family construction remains external and is tracked by #83. |
| `L4.19` | CA bounded below by sampling probability | stated (external Prop; split issue; named mass) | [CapacityBounds.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/CapacityBounds.lean), [GrandChallenges.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean), related DG25 residual work in [DG25/MainResults.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean) | `CodingTheory.linear_epsCA_sampling_dg25_mass`, `CodingTheory.linear_epsCA_ge_sampling_dg25`, `CodingTheory.linear_epsCA_ge_sampling_dg25_of_mass_bound`, `ProximityGap.GrandChallenges.MCAUpperWitness.ofSamplingDG25Mass`, `ProximityGap.GrandChallenges.MCAUpperWitness.ofSamplingDG25` | Prop-valued DG25 Thm 2.5 statement. The named mass isolates `((q-1)/q)·Pr_u[Δ(u,C)≤δ]` and feeds the external Prop plus Grand-MCA upper-witness adapters. The DG25 files prove a different proximity-gap branch, so the covering-radius sampling lower bound remains tracked by #77. |
| `D4.20` | Line-decoding | present | [ProximityGap/LineDecoding.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/LineDecoding.lean) | `CodingTheory.LineDecodable` | GG25 Def 3.1. |
| `T4.21` | Line-decoding implies MCA | repaired core present | [ProximityGap/LineDecoding.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/LineDecoding.lean), [ProximityGap/LineDecodingRefutation.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/LineDecodingRefutation.lean), [ProximityGap/LineDecodingCoverage.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/LineDecodingCoverage.lean) | `CodingTheory.lineDecodable_imp_epsMCA_le_target`, `ProximityGap.LineDecodingCoverage.epsMCA_eq_zero_of_forall_double_cover` | The original black-box `lineDecodable_imp_epsMCA_le` route is refuted; the source keeps the old shape only as `_target`. The structural replacement is the proved per-coordinate double-coverage core in `LineDecodingCoverage.lean`. The remaining quantitative path is to supply GS/list-size coverage data, tracked through the MCAGS mass/frontier issues rather than by reviving the false pure-counting route. |
| `C4.5` | §4.5 MCA conjecture (`conj:mca-conjecture`): `ε_mca(C,δ) ≤ (1/\|F\|)·\|L\|^{c₁}/(ρ^{c₂}·η^{c₃})`, `η := 1−ρ−δ`, `δ < 1−ρ` | present (draft-source `Prop`; caveated adapters) | `ProximityGap.GrandChallenges.mcaConjecture`, `ProximityGap.GrandChallenges.mcaConjectureBound`, `ProximityGap.GrandChallenges.nonempty_mcaLowerWitness_of_mcaConjecture`, `ProximityGap.GrandChallenges.nonempty_mcaLowerWitness_of_ignoredSource_mcaConjecture`, `ProximityGap.GrandChallenges.exists_mcaLowerWitness_of_ignoredSource_mcaConjecture` in [GrandChallenges.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenges.lean), lattice adapters including `ProximityGap.GrandChallengesLattice.mcaThresholdExists_of_ignoredSource_mcaConjecture` and `ProximityGap.GrandChallengesLattice.mcaThreshold_spec_of_ignoredSource_mcaConjecture` in [GrandChallengesLattice.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallengesLattice.lean) | new (Phase 1, 2026-06-03; #78 resolved 2026-06-06) | Stated as a `Prop` (∃ constants `c₁ c₂ c₃`, ∀ RS code & `δ<1−ρ`), term-by-term faithful to the source. Conjecture⇒`MCALowerWitness` and lattice-threshold links are proven and axiom-clean. **Source caveat (verified 2026-06-03): this conjecture sits inside an `\ignore{…}` block in the current `.tex` (≈line 2030) — a draft, not a statement rendered in the compiled paper.** #78 decision: keep the existing public `mcaConjecture` compatibility surface, prefer the `ignoredSource`-named exported aliases when the caveat should be visible in identifiers, and do not treat this draft-source surface as a rendered-paper theorem obligation. |

## Section 5 — Connections Between List Decoding and Correlated Agreement

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `T5.1` | List decoding implies MCA | stated (external Prop) | [Connections/ListDecodingAndCA.lean](../../../ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean); WHIR-specific bridge work in [Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean) | `CodingTheory.linear_listSize_to_epsMCA_gcxk25` | Prop-valued GCXK25 Thm 3 statement. The `_of_residuals`, first-moment, and in-tree-card reductions isolate the bad-γ/GKL24 residuals tracked by #67. |
| `T5.2` | Small ε_ca implies list size < `\|F\|` | stated (external Prop) | [Connections/ListDecodingAndCA.lean](../../../ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean) | `CodingTheory.rs_epsCA_small_implies_lambda_lt_F_bchks25` | Prop-valued BCHKS25 Thm 1.9 statement with proved `_of_residuals` packaging around the bad-line witness input. |
| `T5.3` | CA implies list decoding for related RS | stated (external Prop) | [Connections/ListDecodingAndCA.lean](../../../ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean) | `CodingTheory.rs_epsCA_implies_lambda_extended_cs25` | Prop-valued CS25 Thm 2 statement with a proved contradiction core modulo the deep-hole probability residual. |
| `T5.4` | Separation: list-decoding does not tightly imply CA | stated (external Prop) | [Connections/ListDecodingAndCA.lean](../../../ArkLib/Data/CodingTheory/Connections/ListDecodingAndCA.lean) | `CodingTheory.rs_epsCA_separation_bgks20` | Prop-valued BGKS20 Lem 3.3 statement; proved reductions consume the near-certain bad-line residuals for both no-loss and proximity-loss forms. |

## Section 6 — Toy Problem (deferred)

All §6 items are tracked as `deferred` pending the OracleReduction security
framework gaps being closed. Plan Phase 8 holds these.

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `D6.1` | Toy problem relation `R_C^ℓ` | present | `ToyProblem.relation` in [Definitions.lean](../../../ArkLib/ProofSystem/ToyProblem/Definitions.lean) | `ToyProblem.relation` | Existence-of-message-matrix form; works for any `Set`-shaped code. |
| `C6.2` | Construction 6.2 | present | `ToyProblem.Spec.pSpec`, `Statement`, `OracleStatement`, `Witness`, `accepts`, `inputRelationFor`, `outputRelationFor`, `prover`, `verifier`, `reduction`, `oracleProver`, `oracleVerifier`, `oracleReduction`, `queryG`, `queryF`, `accepts_of_inputRelation` in [Spec/General.lean](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean) | same | Three-round `ProtocolSpec` (γ / g / spot-checks) with `OracleInterface` / `SampleableType` instances. Full honest `Prover` / `Verifier` / `Reduction` triple (computable, non-oracle) **and** `OracleProver` / `OracleVerifier` / `OracleReduction` flavour with real query-based verify body (`queryG`, `queryF` mirroring FRI's `getConst`/`queryCodeword`; query complexity `2t+1`). Honest-completeness point form `accepts_of_inputRelation` **proven** (ring + linearity). The protocol-level `oracleReduction_perfectCompleteness` residual lives in the same file (depends on `accepts_of_inputRelation` plus `OracleReduction.toReduction` plumbing and is tracked under the roadmap query's Phase 2, not in the audit table since it is a Lean-side strengthening rather than a separate paper item). IRS instantiation in `Impl/IRS.lean`. (Note: the 1-arity relaxed relation lives in `SimplifiedIOR.outputRelationFor`.) **Faithfulness fix (2026-06-05):** the IOR relations are now **fixed-encoding** (`inputRelationFor`/`outputRelationFor` over the verifier's own `encode`, witness tied), replacing the earlier existential-encoding `ToyProblem.relation` form under which honest completeness is unprovable/false (an adversary reparameterises the encoding — the same defect as the L6.12 attack). `oracleReduction_perfectCompleteness` is now statement-faithful; its sole residual is the ~250-line `OptionT`/`StateT`/`simulateQ` support-peel (blocker lemmas `simulateQ_list_forIn`, `simulateQ_addLift_add_liftM_*` landed in `ArkLib/ToVCVio/`). |
| `D6.3` | Relaxed toy relation `R̃_C,δ^ℓ` | present | `ToyProblem.relaxedRelation` in [Definitions.lean](../../../ArkLib/ProofSystem/ToyProblem/Definitions.lean) | `ToyProblem.relaxedRelation` | Existence of a valid instance `W*` with at least `(1−δ)·\|ι\|` columns agreeing on every row. |
| `D6.4` | Erasure correction | present | `CodingTheory.SupportsErasureCorrection` in [Erasure.lean](../../../ArkLib/Data/CodingTheory/Erasure.lean); re-exported as `ToyProblem.SupportsErasureCorrection` from [Definitions.lean](../../../ArkLib/ProofSystem/ToyProblem/Definitions.lean) | `CodingTheory.SupportsErasureCorrection` | Predicate is generic (lives under `CodingTheory/`); a `@[reducible]` re-export keeps `ToyProblem.SupportsErasureCorrection` resolving. Both clauses of the paper's definition are encoded — (i) recovery when erasures `< δ_min·n` ∧ matching codeword, (ii) `E f = none` otherwise. Correction-time `ecor` is a `ℕ` parameter (not yet enforced operationally). |
| `L6.5` | Every additive code supports erasure correction | present-but-incomplete | `ToyProblem.additive_code_supports_erasure_correction_grs25` in [SoundnessBounds.lean](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean) | same | External GRS25 residual, genuinely imported. Existence form (some `ecor` works); the paper's `O((s·n)³)` correction-time bound is **deliberately dropped** (pinning the constant needs a concrete encoder model). Faithful weakening, flagged here. |
| `L6.6` | Knowledge soundness of Construction 6.2 | present-but-incomplete | `ToyProblem.Spec.protocol62_knowledgeSound` in [Spec/General.lean](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean) | same | Statement has the concrete paper error formula and load-bearing `δ < δ_min(C)`/`[Nonempty ι]` hypotheses. The live proof surface is the reducible residual alias `protocol62_knowledgeSound_residual`, now pointing at `Bridge.StraightlineOfRewinding` rather than a raw proof hole. Tracked by #18. |
| `R6.7` | CA insufficient for L6.6 proof | present | `ToyProblem.Spec.remark67` (narrative; sits in L6.6 docstring) in [Spec/General.lean](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean) | same | Encoded as a docstring + a `Unit`-valued marker definition. |
| `L6.8` | Round-by-round knowledge soundness of Construction 6.2 | present-but-incomplete | `ToyProblem.Spec.protocol62_rbrKnowledgeSound` in [Spec/General.lean](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean) | same | Concrete per-challenge error statement is present. The live proof surface is `protocol62_rbrKnowledgeSound_residual`, another reducible alias to `Bridge.StraightlineOfRewinding`. Tracked by #18. |
| `C6.9` | Construction 6.9 (attack target) | present | `ToyProblem.SimplifiedIOR.pSpec`, `OutputStatement`, `OutputOracleStatement`, `OutputWitness`, `outputRelationFor`, `prover`, `verifier`, `reduction` in [Spec/SimplifiedIOR.lean](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean) | same | One-round V→P γ reducing IOR, mapping `(v, μ₁, μ₂, f₁, f₂) ↦ (v, μ₁+γ·μ₂, f₁+γ·f₂)`. Sibling file to `Spec/General.lean` (C6.2). **Only the non-oracle flavour is shipped**: an `OracleReduction` version would require declaring the combined output oracle `f_new := f₁ + γ·f₂` as an arbitrary function of `(f₁, f₂, γ)`, but the current `OracleVerifier.embed` machinery in [`OracleReduction/Basic.lean`](../../../ArkLib/OracleReduction/Basic.lean) only allows the output oracle family to be a *verbatim subset* of input oracles + prover messages. A `simOStmt`-based refactor of the framework (sketched in `Basic.lean:278, 293`) is needed before the oracle flavour can be added. The bundled-input non-oracle `reduction` captures full semantics in the meantime. |
| `L6.10` | Soundness of Construction 6.9 | present-but-incomplete | `ToyProblem.SimplifiedIOR.simplifiedIOR_knowledgeSound` in [Spec/SimplifiedIOR.lean](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean) | same | Concrete one-round knowledge-error statement is present. The live proof surface is `simplifiedIOR_knowledgeSound_residual`, the third reducible alias to `Bridge.StraightlineOfRewinding`. Tracked by #18. |
| `D6.11` | Winning set `Ω` | present | `ToyProblem.winningSet` in [Definitions.lean](../../../ArkLib/ProofSystem/ToyProblem/Definitions.lean) | `ToyProblem.winningSet` | `Set F` of challenges; cardinality bounds drive L6.12 / L6.13. The Def-6.11 *soundness error* `sup_{violating}\|Ω\|/\|F\|` is realised as `ToyProblem.winningSetSoundness` / `soundnessError` in [Leaderboard.lean](../../../ArkLib/ProofSystem/ToyProblem/Leaderboard.lean) (Phase 2 bits-of-security leaderboard; not a separate paper item — a Lean-side framework over D6.11, so off the parsed table like the C6.2 completeness stub). |
| `L6.12` | List-decoding lower-bound attack | **present** | `ToyProblem.simplified_iop_soundness_listDecoding_lb` in [SoundnessBounds.lean](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean) | same | **PROVEN sorry-free + axiom-clean 2026-06-04** (`#print axioms` → only `propext`/`Classical.choice`/`Quot.sound`). **Statement corrected 2026-06-04 (finding S5):** conclusion `\|Ω\|.ncard ≥ N·\|F\|/(\|F\|+2N)` (canonical `.tex` final bound), against the fixed-encoding `relaxedRelationFor enc` / `winningSetFor enc`; carries `[Nonempty ι]`, linearity (`enc` injective, `range enc = C`), and certifies the violation (`¬ R̃²` conjunct). Proof completed via the message-pair reconciliation lemma `encStack_mem_closeCodewordsRel_iff` (close-codeword stack ↔ agreement set, both directions; reuses the coercion handling of `mem_winningSet_zero_of_relClose`): (i) Λ-enumeration as the `encStack`-bijection `Smsg ≃ Λ(C^{≡2},δ,fStar)`, (ii) the violation `(μ₁,μ₂) ∉ S_v`, (iii) membership `winImg ⊆ Ω` via `mem_winningSetFor_of_agree`. The two Claim-B.1 applications + denominator algebra were already proven (`exists_dotProduct_image_lb`, `exists_affine_image_lb`, `claimB1_bound_to_real`, `listDecoding_winning_lb`). |
| `L6.13` | CA lower-bound attack | **present** | `ToyProblem.simplified_iop_soundness_ca_lb` in [SoundnessBounds.lean](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean) | same | **PROVEN sorry-free + axiom-clean 2026-06-04** (`#print axioms` → only `propext`/`Classical.choice`/`Quot.sound`). Statement strengthened: `[Nonempty ι]`, linearity hyp (`∃ enc, range enc = C`), `0 < ε_ca` guard (paper's "if not, vacuous"), and certifies the violation (`¬ R̃²` conjunct, via `jointAgreement_iff_jointProximity`). Helper `mem_winningSet_zero_of_relClose` (the `S ⊆ Ω` inclusion). The bound is in terms of `ε_ca`, not `ε_mca` (cf. R6.14). The attack→soundness chain `epsCA_le_winningSetSoundness` (Leaderboard.lean) is likewise real + axiom-clean. |
| `R6.14` | Attack reaches `ε_ca` not `ε_mca` | deferred | docstring on `simplified_iop_soundness_ca_lb` | docstring | Already noted in L6.13's docstring. |

## Appendix A — Additional Preliminaries

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `A.1` | IOR completeness | present-but-different | `Reduction.completeness`, `Reduction.perfectCompleteness` in [Security/Basic.lean](../../../ArkLib/OracleReduction/Security/Basic.lean) | use `Reduction.perfectCompleteness` directly | Paper's A.1 is realised by the existing definition (which is more general — richer execution / log model). ArkLib convention: use the in-tree name; the paper↔Lean name map lives in this Notes column rather than in an `alias` wrapper. |
| `A.2` | IOP as IOR to trivial relation | present-but-different | same framework in [Security/Basic.lean](../../../ArkLib/OracleReduction/Security/Basic.lean) | docstring on `Reduction.completeness` | Conceptually supported. |
| `A.3` | IOR knowledge soundness | present-but-different | `Verifier.knowledgeSoundness` in [Security/Basic.lean](../../../ArkLib/OracleReduction/Security/Basic.lean) | use `Verifier.knowledgeSoundness` directly | ArkLib's richer execution/log model captures the paper's narrative `(E, et, κ)` extractor presentation. No paper-shape wrapper — use the in-tree name. |
| `A.4` | Knowledge state function | present | [Security/RoundByRound.lean](../../../ArkLib/OracleReduction/Security/RoundByRound.lean) | existing | Aligned with paper. |
| `A.5` | Round-by-round knowledge soundness | present-but-different | `Verifier.rbrKnowledgeSoundnessOneShot`, `Verifier.rbrKnowledgeSoundness` in [Security/RoundByRound.lean](../../../ArkLib/OracleReduction/Security/RoundByRound.lean) | use `Verifier.rbrKnowledgeSoundness` directly | The paper's `KnowledgeStateFunction` machinery and per-round error tuple `(ε_1, …, ε_k)` map directly to the in-tree definition. No paper-shape wrapper. |
| `A.6` | Formal derivative `f^(s)` | present-but-different | Mathlib `Polynomial.derivative` | use `Polynomial.derivative` directly | Iterated `f^(s)` form is `Polynomial.derivative^[s]` (used in `ReedSolomon/Multiplicity.lean`). No paper-shape wrapper — use Mathlib's name. |
| `A.7` | Univariate multiplicity code `UM[F,L,k,s]` | present | `ReedSolomon.Multiplicity.umEvalOnPoints`, `ReedSolomon.Multiplicity.umCode`, `ReedSolomon.Multiplicity.mem_umCode_one_iff_mem_rsCode` in [ReedSolomon/Multiplicity.lean](../../../ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean) | same | Submodule form `(Polynomial.degreeLT F k).map (umEvalOnPoints domain s)`, mirroring `ReedSolomon.code` and `ReedSolomon.Folded.frsCode`. Encoder packages `s` formal-derivative evaluations per domain point. `mem_umCode_one_iff_mem_rsCode` provides the `s = 1` collapse to plain RS (hoisted out of the `[CommRing F]` namespace to a `[Field F]` scope so the `Polynomial F` instance paths align with `ReedSolomon.code`'s). Paper requirement `char(F) ≥ k` is documented but not baked into the bare definition. |

## Appendix B

| ABF26 ID | Paper item | Status | Lean refs | Lean target | Notes |
| --- | --- | --- | --- | --- | --- |
| `B.1` | Collision bound for random functions | present | `Probability.exists_large_image_of_pairwise_collision_bound` in [Combinatorial.lean](../../../ArkLib/Data/Probability/Combinatorial.lean) | `Probability.exists_large_image_of_pairwise_collision_bound` | Closed 2026-05-20. Proof route: helper lemmas `sum_fiber_sq_eq` (fiber-partition + diagonal decomposition) and `cauchy_schwarz_fiber` (`sq_sum_le_card_mul_sum_sq` over `ℝ` via cast); main theorem by contradiction (avoids Jensen): `PMF.bind`-unfolded linearity gives `E[numColls] ≤ N(N-1)ε`, while per-`φ ∈ supp` Cauchy-Schwarz + ENNReal cross-multiplication gives `numColls φ > N(N-1)ε`; `ENNReal.tsum_lt_tsum` strict-averaging closes the loop. |

## Existing Inconsistencies

The largest mismatches between the paper and ArkLib are structural rather
than mathematical. These drive the grand-challenge instantiation phase.

1. **Correlated agreement is formalized as predicates, not error functions.**
   ArkLib currently exposes `δ_ε_correlatedAgreement...` predicates in
   [ProximityGap/Basic.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean),
   while the paper is organized around numeric error functions `ε_pg`,
   `ε_ca`, and `ε_mca`. Closing this is the linchpin of Phase 1.

2. **General MCA is not yet a first-class coding-theory notion.**
   The TODO at the top of
   [ProximityGap/Basic.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean)
   still lists mutual correlated agreement as missing. The
   [Whir/MutualCorrAgreement.lean](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean)
   file is WHIR/proximity-generator specific and is not a drop-in
   formalization of Section 4. Phase 1 re-expresses the WHIR notion as a
   specialization of the new general `epsMCA`.

3. **The non-unique-decoding branch of BCIKS20 AffineLines is residualized.**
   The old raw line reference for `RS_correlatedAgreement_affineLines` is
   superseded. Current blockers are the named `StrictCoeffPolysResidual`,
   `BoundaryCardResidual`, and `BoundaryCardLatticeResidual` interfaces, plus
   the supporting bivariate-existence machinery in
   [JointAgreement.lean](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/JointAgreement.lean).

4. **Historical proximity-gap raw-hole inventories are superseded.**
   The current clean-tree census reports zero raw holes. The old file-count
   inventory for `Curves.lean`, `BCIKS20/ListDecoding/*`,
   `WeightedAgreement.lean`, `DG25/MainResults.lean`,
   `Whir/MutualCorrAgreement.lean`, and `GuruswamiSudan.lean` should be read
   as historical. Current ownership is by named residual interfaces and the
   focused issue map, not by anonymous proof-hole counts.

5. ~~**Several code families used centrally by the paper are absent.**~~
   *(Resolved 2026-05.)* All four families are now present in-tree, each
   reachable from a `present` or `present-but-incomplete` row above:
   Folded Reed-Solomon (D2.14, D2.15) in
   [`ReedSolomon/Folded.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean);
   univariate multiplicity codes (A.7) in
   [`ReedSolomon/Multiplicity.lean`](../../../ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean);
   subspace-design codes (D2.16, L2.17, T2.18) in
   [`SubspaceDesign.lean`](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean);
   and extension-field codes (D2.19, D2.20, L2.21) in
   [`ExtensionCodes.lean`](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean).

## Forward roadmap

The phased completion plan (grand-challenge instantiation framework, the
toy-protocol bits-of-security leaderboard, the §6 proofs, the concrete
parametrization tables, and the integration cleanups) and the per-finding
review logs are maintained as local working notes, kept out of the PR by
design. This audit doc is the in-tree status snapshot and is updated
row-by-row as PRs land.
