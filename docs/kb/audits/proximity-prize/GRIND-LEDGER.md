# Proximity Prize — bottom-up grind ledger (started 2026-06-05)

Goal: build the keystone (BCIKS20 §5 list-decoding / `correlatedAgreement_affine_curves`
Curves.lean:1819) bottom-up, every brick kernel-clean (`#print axioms` =
`[propext, Classical.choice, Quot.sound]`, no sorry/axiom/native_decide). Months-scale.
Work in NEW non-contended files (ArkLib/ToMathlib/ + new keystone files); never edit files the
active session is editing (currently Curves.lean, JohnsonBound/Family.lean). Verified bricks are
copied durably to `research/proximity-prize/artifacts/`.

Build env: worktree `/home/shaw/arklib-goal` @406b94548, `.lake` symlinked. Recreate if torn down.
Verify harness: `audit.sh` in the worktree.

## Layers (bottom → top)

L0  mathlib substrate (function fields, power-series Hensel, valuations, degree calculus, Siegel)
L1  BCIKS20 Appendix-A.4 β-construction (the real Hensel numerator; ingredient D)
L2  ingredient C (matching point ⟹ S_β membership; #S_β > Λ·d) → fires proven Lemma_A_1
L3  Claims 5.8/5.8'/5.9 (via α'=0), 5.10/5.11 (via C); 5.7 API-refactor
L4  hcoeffPoly (Curves.lean:1199 front door) ⟹ Curves.lean:1819 keystone clean
L5  de-taint STIR/WHIR/FRI rbr-soundness

## Brick status

| brick | file | layer | status |
|---|---|---|---|
| Henselian `k⟦X⟧` + `(RatFunc F)⟦X⟧` + simple-root lift | artifacts/PowerSeriesHenselianA.lean | L0 | ✅ VERIFIED (4 decls, clean) |
| RatFunc Z-degree calculus (intDegree + zDeg, +/*/inv/pow bounds) | artifacts/RatFuncDegreeCalculus.lean | L0 | ✅ VERIFIED (14 lemmas, clean) |
| Constructive Newton lift over `k⟦X⟧` (quadratic conv, `powerSeries_newton_root`) | artifacts/PowerSeriesNewton.lean | L0/L1 | ✅ VERIFIED (7 lemmas, clean) |
| Siegel / GS interpolant existence (trivariate, multiplicity-vanishing box Q) | artifacts/SiegelInterpolation.lean | L0 | ✅ VERIFIED (4 results, clean) |
| S_β / Lemma_A_1 packaging (fire vanishing from Finset T⊆S_β, #T>Λ·d) | artifacts/SbetaPackaging.lean | L2 | ✅ VERIFIED (4 lemmas, clean) |
| ingredient-D dependency DAG | ingredient-D-DAG-2026-06-05.md | plan | 🔄 agent (wave 1) |
| bivariate/trivariate weighted-degree toolkit | ToMathlib/BivariateDegreeToolkit.lean | L0 | 🔄 agent (wave 1b) |
| Frobenius p-power factor helpers (`(X−C a)^{p^f}`, separability, value uniqueness) | artifacts/FrobeniusFactorHelpers.lean | L0 | ✅ VERIFIED (12 lemmas, clean) |

## VERIFIED (cumulative): 12 kernel-clean bricks in artifacts/

PowerSeriesHenselianA, RatFuncDegreeCalculus, PowerSeriesNewton, SiegelInterpolation,
SbetaPackaging, FrobeniusFactorHelpers, HenselUniqueness, PartitionRecursion,
BivariateDegreeToolkit, FiniteSeriesToPoly (L18a), PowerSeriesSubstCoeff (L6),
IngredientCBridge (L14).

## STRUCTURAL REDUCTION ACHIEVED (all kernel-clean, composing the bricks)

The §5 keystone claims now reduce to a SINGLE remaining core:
- Ingredient C: `IngredientCBridge.embedding_eq_zero_of_matchingSet_large` reduces
  `embedding(β R t)=0` to **[real β with `MatchingVanishes matchingSet root β` + `#matchingSet > Λ·d`]**.
- Claim 5.8: in-tree `alpha'_eq_zero_of_embedding_beta_eq_zero` (proven) + the above ⟹ 5.8.
- Claim 5.9: `Claim59Conditional` (in flight) reduces to the 5.8' tail-vanishing hyp.
- Claim 5.11 (L20): in flight, independent.
THE IRREDUCIBLE REMAINING CORE = **L7/L13: construct the real β (App-A.4 well-founded recursion)
- prove it satisfies MatchingVanishes (L12/L14-per-point) + the weight bound (L9/L10)**.

UPDATE: **18 bricks verified** (added L2b HasseDerivNumeratorConcrete = i₁=0 line case of the
β-recursion numerator, 7 decls; SubstFieldCaveat = F1 correctness finding, 9 decls). Claim-reduction
trio COMPLETE (5.8/5.9/5.10 → same β core). L7 substrate fully ready (L1+L2+L2b+L3 ✅).
IN FLIGHT: L7 (β recursion — the XL core).
NOT DONE: L20 (Claim 5.11) agent stalled (olean-rebuild contention); file has 5 sorries + 1 error —
must re-task as a clean focused job (no concurrent olean writers). OPERATIONAL NOTE: concurrent
agents writing oleans into the shared .lake via `lake env lean -o` can cause rebuild contention —
serialize olean-producing agents or give each its own .lake copy.

## In-flight (Wave 2/3, post-DAG)

| brick | file | layer | status |
|---|---|---|---|
| L20 Claim 5.11 standalone | ToMathlib/Claim511.lean | L3 | 🔄 |
| L6 PowerSeries.subst coeff | ToMathlib/PowerSeriesSubstCoeff.lean | L0 | 🔄 |
| L18a finite series ⟹ polynomial | ToMathlib/FiniteSeriesToPoly.lean | L0 | 🔄 |
| L3 weight_Λ_over_𝒪 calculus | ToMathlib/WeightLambdaCalculus.lean | L1-sub | 🔄 |
| L2 Hasse-deriv B numerators / 𝒪 closure | ToMathlib/HasseDerivNumerators.lean | L1-sub | 🔄 |
| L14 ingredient-C bridge (conditional on β-property) | ToMathlib/IngredientCBridge.lean | L1'/L2 | 🔄 |

Next after L2/L3 land: **L7** (β well-founded recursion — XL core, uses L1+L2) → L9 (uses L3) → L10 → L13 drop-in.

## Critical path remaining (per DAG)

L7 β well-founded recursion (needs L1,L2) → L9 weight induction → L10 collapse to (2t+1)d_R·D
→ L13 drop-in new β (cross-file signature change; coordinate w/ live session) → L16 S_β largeness
(needs L14 ingredient-C bridge: matching pt ⟹ π_z(β)=0, needs L15) → L17 Claim 5.8 → L18 5.9 → L19 5.10.
XL bottlenecks: L7 (β recursion) and L14/L15 (Hensel uniqueness + π_z commutation).

## Wave-2 candidate bricks (queue; launch as slots free / after DAG lands)

- Separable/inseparable (`p`-power Frobenius) factorization helpers for `R(X,Y^{p^f},Z)`.
- Finite/algebraic extension Hensel facts for the keystone's `𝕃 = RatFunc F[X]/(H̃)` setting
  (and the (X−x₀)-adic completion where the lift lives).
- Multiplicity / Hasse-derivative vanishing count (GS interpolant constraint counting).
- `weight_Λ_over_𝒪` / `S_β` cardinality arithmetic helpers (feed Lemma_A_1 cleanly).
- Resultant degree-bound refinements (BCKHS25 §3.2 saved-factor).

## SESSION CHECKPOINT 2026-06-05 — 19 verified bricks; β-recursion core DEFINED

**Milestone:** L7 `BetaRecursion.lean` ✅ — `betaRec` (the App-A.4 recursion) is DEFINED with
termination discharged (via L1 metric), landing-in-𝒪 (`betaRec_mem`) + weight-bound skeleton
proven, all kernel-clean. Genuine residuals isolated as EXPLICIT HYPOTHESES (never sorry):
`Bcoeff`/`hterm` (the L2b numerators) and `hterm_bound` (the L9 telescoping).

**Exact remaining critical path to close the keystone (Curves.lean:1819):**
1. **L2b-general** — the i₁>0 trivariate Hasse-derivative numerator W-divisibility (L2b proved the
   i₁=0 line case; general case is `genHasseCoeff_hasWPowerNumerator_of_clearing` + supplying the
   two inputs). Feeds `betaRec`'s `Bcoeff`/`hterm`.
2. **L9** — weight telescoping: per-term budget → `weight_Λ_over_𝒪 (betaRec t) ≤ (2t+1)·d_R·D`
   (the partition-indexed induction; skeleton in `betaRec_weightBound_of_term_bounds`, uses L3).
3. **L10** — collapse the bound to the `Lemma_A_1`-firing form (L3 `_le_trans_nat` ready).
4. **L12** — the real β satisfies `MatchingVanishes` (per-point `π_z (betaRec t)=0` for matching z),
   via HenselUniqueness (`specialization_eq_proximate_root_of_hensel` in IngredientCBridge) + the
   `(X−x₀)^t` coeff extraction from `betaRec`. Then L14's `embedding_eq_zero_of_matchingSet_large`
   fires → Claims 5.8/5.9/5.10 (already reduced).
5. **F1 fix** — recenter the in-tree `γ` (currently buggy for x₀≠0; see Findings F1) via
   `PowerSeries.mk (α …)` / `Polynomial.taylor x₀`, OR confirm x₀=0 suffices for the construction.
6. **L13 drop-in** — replace in-tree `β_regular` (trivial `β=0`) with `betaRec` in
   RationalFunctions.lean (cross-file signature change: thread `x₀`, `Bcoeff`); CO-ORDINATE with the
   live session (it edits Curves.lean/Agreement.lean) — converge, do not edit-war.
7. **hcoeffPoly / Curves:1819** — with Claims 5.8-5.11 closed, supply the `hcoeffPoly` witness to
   `RS_jointAgreement_of_prob_gt_and_errorBound_lower_bounds` (front door, Curves.lean:1199) →
   `correlatedAgreement_affine_curves` clean → de-taint STIR/WHIR/FRI rbr-soundness (L5).

**20 verified bricks** (added Claim511 — combinatorial double-counting core + published-shape
`exists_points_with_large_matching_subset_fin` under 4 explicit §5 hypotheses).

DAG CORRECTION (F2): Claim 5.11 is NOT independent of §5 (DAG over-claimed). The bare published
statement is false when `coeffs_of_close_proximity` is empty (`0 > positive`); it genuinely needs
`hbad`/`hthreshold`/`hsmall`/`hbridge` — and `hthreshold`/`hsmall` rest on Prop 5.5. So all four
§5 claims (5.8–5.11) bottom out on: real β (L7 ✅, +L2b-gen/L9/L12) + Prop 5.5 largeness.

**22 verified bricks.** L9 ✅ (`betaRec_weight_le` strong induction + finite-product weight lemma)
and L12 ✅ (`betaRec_matchingVanishes` + `betaRec_embedding_eq_zero_of_matchingSet_large`).

**KEY COMPOSITION NOW PROVEN (kernel-clean):** L7 betaRec + L9 weight + L12 MatchingVanishes + L14
ingredient-C ⟹ `embeddingOf𝒪Into𝕃 (betaRec t)=0` ⟹ Claims 5.8/5.9/5.10/5.11. Remaining gaps all
isolated as EXPLICIT hypotheses (never sorry):
- `coeffExtract` (L12 per-point `(X−x₀)^t` reading: `α_t = embedding(betaRec t)/(W^{t+1}ξ^{e_t})`),
- L10 telescoping constants (`htele`/`bW`/`bξ`/`bB`/`wβ` → (2t+1)d_R·D numerals),
- L2b-general (i₁>0 numerator — in flight), Prop 5.5 largeness (in flight).
Then: F1-fix (recenter γ for x₀≠0) + L13 drop-in (replace trivial β_regular — cross-file,
coordinate w/ live session) → hcoeffPoly → Curves:1819 → de-taint STIR/WHIR.

**23 verified bricks.** Prop 5.5 ✅ (`Prop55.exists_a_set_and_a_matching_polynomial` — existence
engine fully discharged via SiegelInterpolation; GS-count + `MatchingExtractor` isolated as
explicit hyps). Note: in-tree `modified_guruswami_has_a_solution` already proves the Q-existence;
`exists_a_set_and_a_matching_polynomial` is only a doc-comment concept (never a declared lemma).

**24 verified bricks — all launched agents complete.** L2b-general ✅
(`HasseDerivNumeratorGeneral`: i₁>0 mixed trivariate Hasse-derivative numerator,
`genHasseCoeff_hasWPowerNumerator_of_dvd_top`; i₁=0 case fully discharged; 1 residual `hdvd_top`).

REMAINING explicit-hypothesis gaps to fully close ingredient D (all isolated, none faked):
(1) L2b `hdvd_top` — ✅ DONE (HdvdTop.lean, 27th brick; `hdvd_top_of_dvd_C` proves it for ALL i₁
    from ONE multiplicity fact `hdvd_C : (C H.leadingCoeff) ∣ R.coeff R.natDegree` via Hasse-deriv
    linearity; i₁=0 residual-free. `hdvd_C` = the GS interpolant's multiplicity-vanishing at x₀,
    same family as obligation (4)'s `HasOrderAt` upstream — the genuine §5 regime datum);
(2) L10 telescoping numerals (htele→(2t+1)d_R·D) — ✅ DONE (BetaWeightCollapse.lean, 28th brick;
    11 decls kernel-clean, axioms=[propext,Classical.choice,Quot.sound]). Instantiates L9's abstract
    budgets with the concrete App-A values bW=D−d_H (L3), bξ=(d−1)(D−d_H+1) (weight_ξ_bound), bB=
    (D−Σλ)+(d−δ−Σλ)(D−d_H), wβ_tight=1+(t+1)bW+e_tbξ, and PROVES the App-A line-2877–2881 telescoping
    (`betaTele_tight`, slack EXACTLY d_R−d_H≥0) + the loose collapse `wβ_tight≤(2t+1)d_R·D`
    (`wβ_tight_le_loose`). Delivers `betaRec_weight_le_concrete : weight_Λ_over_𝒪 hH (betaRec…t) D ≤
    (2t+1)·d·D`. KEY FINDING: the per-term telescoping is FALSE with the loose budget (only the TIGHT
    1+(t+1)Λ(W)+e_tΛ(ξ) telescopes term-by-term, collapsed once at the end) AND the in-tree
    `betaRec_weight_le`'s `htele` hyp is over-strong (false on the forbidden pair (0,{t+1}) for any
    bB>0, since the recursion drops that term but the budget counts it) — so this brick re-derives the
    bound from the L9 *skeleton* `betaRec_weightBound_of_term_bounds` with the forbidden + Hasse-
    vanishing (Σλ>d−δ ⟹ Bcoeff=0, via `hBzero`) splits done correctly. Residual explicit hyps (none
    faked): `hbB` (L2b/L4 B-weight), `hBzero` (Hasse vanishing), `hd1`/`hdH_le`/`hdH_D` (degree facts
    1≤d_H≤d_R, d_H≤D, in-tree from weight_ξ_bound's `hdH_le` + `hH`), `hbξ` (weight_ξ_bound output);
(3) L12 coeffExtract — ✅ DONE (CoeffExtract.lean, 25th brick; reduced to per-point geometry hyps
    hαβ/haP/hw/hx that L13's β-construction supplies);
(4) Prop 5.5 MatchingExtractor — ✅ DONE (MatchingExtractor.lean, 26th brick;
    `matchingFactor_dvd_of_orderM_and_count`: GS multiplicity⟹root⟹(Y−Pz)∣Q, standalone;
    upstream input = GS multiplicity datum + Johnson δ≤δ₀ regime, the genuine §5 side condition);
(5) F1 γ-recenter fix; (6) L13 drop-in (cross-file replace of trivial β_regular — coordinate w/ live session).

PROGRESS: 26 bricks. Obligations (3)+(4) DONE. (1) hdvd_top + (2) L10 = last 2 discharge agents in
flight. After those: only (5) F1-fix + (6) L13 remain — both in-tree edits to RationalFunctions.lean
needing live-session coordination (NOT solo edits — converge). Then hcoeffPoly→Curves:1819→STIR/WHIR.
Then hcoeffPoly→Curves:1819→de-taint STIR/WHIR. Prize Grand Challenges remain OPEN research
regardless. NEXT-SESSION ENTRY POINT: these 6 obligations; (2)+(3) are pure arithmetic/coeff
extraction now that betaRec is defined; (1)+(4) are the genuine remaining math; (5)+(6) are
in-tree fixes needing live-session coordination.

## Integration rule

A brick is "complete" only when: (1) compiles via `lake env lean` with 0 errors/0 sorry, (2) its
`#print axioms` shows only the 3 standard axioms, (3) copied to `artifacts/`, (4) row set ✅ here.
Never mark complete on an agent's self-report alone — re-verify in the main loop.

## Findings

### F1 (2026-06-05) — In-tree `γ` is genuinely ill-defined for `x₀ ≠ 0` (brick L18 / Claim 5.9)

VERDICT: **(a) genuinely buggy for `x₀ ≠ 0`** — not salvageable as-is; only correct in the centred
case `x₀ = 0`.

Evidence (kernel-clean, proven in `ArkLib/ToMathlib/SubstFieldCaveat.lean`, axioms =
`[propext, Classical.choice, Quot.sound]`):

- The in-tree `γ` (`RationalFunctions.lean:2886`) is
  `γ = PowerSeries.subst (mk shift) (mk α)` over the **field** `𝕃 H`, where the shift series is the
  BCIKS substitution `X ↦ X − x₀`: `shift 0 = fieldTo𝕃 (-x₀)`, `shift 1 = 1`, `shift t = 0 (t ≥ 2)`.
- Mathlib defines `PowerSeries.HasSubst g := IsNilpotent (constantCoeff g)`
  (`Mathlib/RingTheory/PowerSeries/Substitution.lean:38`). `PowerSeries.subst g ·` is only
  meaningful under `HasSubst g`; otherwise it is mathlib's junk default (no mathematical content).
- Proven lemma `hasSubst_iff_constantCoeff_eq_zero_of_field`: over a field `K`,
  `HasSubst g ↔ constantCoeff g = 0` (a field is reduced, so `IsNilpotent x ↔ x = 0`).
- `constantCoeff (shiftSeries x₀ H) = fieldTo𝕃 (-x₀)`; `fieldTo𝕃` is injective (ring hom out of a
  field into the nontrivial field `𝕃 H`), so `fieldTo𝕃 (-x₀) = 0 ↔ x₀ = 0`.
- COROLLARY `hasSubst_shiftSeries_iff_eq_zero`: **`HasSubst (shiftSeries x₀ H) ↔ x₀ = 0`.**
  Hence `not_hasSubst_shiftSeries_of_ne_zero`: for `x₀ ≠ 0` the substitution underlying `γ` is
  invalid and the in-tree `γ` is mathlib's junk default → Claim 5.9's premise about it is
  vacuous/wrong off-centre. `hasSubst_shiftSeries_zero`: the centred case `x₀ = 0` is fine
  (shift series is literally `X`, `HasSubst X` holds).

No other hypothesis in the file forces `x₀ = 0`: `α`/`γ`/`Hypotheses` are all stated for general
`x₀ : F`, so the bug is real (not vacuously avoided).

RECOMMENDED FIX: the correct BCIKS object is the lift as a power series in the **new** variable
`T = X − x₀` (a recentering), i.e. `γ = ∑ₜ αₜ Tᵗ ∈ 𝕃 H⟦T⟧` = `PowerSeries.mk (α x₀ R H hHyp)` —
**not** a `subst` of `X − x₀` into the `X`-series. Either (recommended) redefine
`γ := PowerSeries.mk (α …)` and recenter any polynomial representative via `Polynomial.taylor x₀`
(not `PowerSeries.subst`); or (as `Claim59Conditional` already does) carry
`hsubst : HasSubst (shiftSeries x₀ H)` as an explicit hypothesis on every downstream lemma — but by
the corollary above that hypothesis **is equivalent to `x₀ = 0`**, so that route silently restricts
all such statements to the centred case and is sound only there.

═══════════════════════════════════════════════════════════════════════════════
## ★ AUTHORITATIVE FINAL STATE (2026-06-05, supersedes all above) — 28 verified bricks
═══════════════════════════════════════════════════════════════════════════════

28 kernel-clean bricks in `artifacts/` (each `#print axioms` = [propext,Classical.choice,
Quot.sound], 0 sorry/admit/axiom/native_decide, re-verified in main loop):
PowerSeriesHenselianA, RatFuncDegreeCalculus, PowerSeriesNewton, SiegelInterpolation,
SbetaPackaging, FrobeniusFactorHelpers, HenselUniqueness, PartitionRecursion,
BivariateDegreeToolkit, FiniteSeriesToPoly, PowerSeriesSubstCoeff, IngredientCBridge,
Claim59Conditional, Claim510Conditional, Claim511, HasseDerivNumerators,
HasseDerivNumeratorConcrete, HasseDerivNumeratorGeneral, SubstFieldCaveat, BetaRecursion,
BetaWeightInduction, BetaMatchingVanishes, Prop55, MatchingExtractor, CoeffExtract, HdvdTop,
BetaWeightCollapse (+ the DAG doc).

INGREDIENT-D β-CONSTRUCTION: COMPLETE & kernel-verified end-to-end modulo the items below.
Chain (all proven, composing the bricks): `betaRec` defined+terminating+lands-in-𝒪 (L7) →
`betaRec_weight_le_concrete ≤ (2t+1)d_R·D` (L9+L10) → `betaRec_matchingVanishes` (L12, via
HenselUniqueness) → `embedding(betaRec t)=0` (L14) → Claims 5.8/5.9/5.10/5.11.
Discharge obligations (1) hdvd_top, (2) L10 numerals, (3) coeffExtract, (4) MatchingExtractor:
ALL DONE.

REMAINING TO TOUCH Curves.lean:1819 (finite + explicit):
A. ONE genuine §5 math datum, shared by (1)+(4): the GS-interpolant multiplicity-vanishing at x₀
   — `hdvd_C : (C H.leadingCoeff) ∣ R.coeff R.natDegree` / `HasOrderAt Qz (ωs i) (Pz.eval(ωs i)) m`
   — under the Johnson radius δ≤δ₀. (This is the in-tree `ModifiedGuruswami.Q_multiplicity` /
   `gsQ_multiplicity` content; wire it in, don't re-prove.)
B. A few in-tree degree facts (d_H≤d_R≤D etc.) — available from `weight_ξ_bound`/`hH`.
C. F1 fix — recenter in-tree `γ` for x₀≠0 (SubstFieldCaveat proves it's currently buggy).
D. L13 — replace trivial `β_regular` with `betaRec` in RationalFunctions.lean (cross-file).
E. Then supply `hcoeffPoly` (front door Curves.lean:1199) → `correlatedAgreement_affine_curves`
   clean → de-taint STIR/WHIR (L5).
C+D+E are IN-TREE EDITS to live-session-owned files → COORDINATE, do not edit-war.

FINDINGS: F1 (in-tree γ ill-defined for x₀≠0, kernel-proven, SubstFieldCaveat); F2 (Claim 5.11 not
§5-independent, contra DAG); F3 (in-tree `betaRec_weight_le.htele` over-strong/unsat on forbidden
pair (0,{t+1}) for bB>0 — BetaWeightCollapse re-derives from the L9 skeleton correctly; the loose
(2t+1)d_R·D budget does NOT telescope term-by-term, only the tight budget does).

PRIZE GRAND CHALLENGES remain OPEN research independent of all this (see proximity-prize-kernel-audit).

═══════════════════════════════════════════════════════════════════════════════
## ⚠ FINDING F4 (2026-06-05) — KeystoneCapstone is a BUNDLING WRAPPER, not a reduction
═══════════════════════════════════════════════════════════════════════════════

KeystoneCapstone.lean compiles kernel-clean, BUT adversarial re-verification (main loop) shows it
does NOT genuinely compose the β-construction. Its sole substantive hypothesis
`Section55Output u := ∀ P good, CurveCoeffPolys u P`, and `CurveCoeffPolys u P := ∀ j<deg, ∃ Bj,
natDegree<k+1 ∧ ∀ z∈good, (P z).coeff j = Bj.eval z` — which is *definitionally the `hcoeffPoly`
goal itself* (per-index instead of bundled). The proof of `hcoeffPoly_of_johnson_regime` is just
`intro P hP; exact hcoeffPoly_witness_of_curveCoeffPolys u P (hSec55 P hP)` — uses ONLY the
hypothesis + a trivial bundling lemma. `betaRec`/`embedding_eq_zero`/`matchingVanishes` appear ONLY
in its docstring, NEVER in a proof term. ⇒ The capstone ASSUMES ≈ the goal; it is NOT a genuine
"composition of the 28 bricks reaching Curves:1819." DO NOT count it as keystone progress.

CORRECTED honest status of the keystone reduction:
- GENUINE (kernel-clean, real): the 28 bricks; betaRec defined+terminating+weight-bound+lands-in-𝒪;
  the CONDITIONAL reductions IngredientCBridge (embedding=0 ⟸ MatchingVanishes+large matchingSet),
  Claim59/510Conditional, Claim511 core, MatchingExtractor, HdvdTop, MultiplicityDatum (pending).
- The REAL remaining proof work (was masked by F4's Section55Output assumption): ASSEMBLE
  `betaRec ⟹ CurveCoeffPolys` — i.e. compose betaRec → MatchingVanishes(L12) → embedding=0(L14) →
  Claims 5.9/5.10 decoded-coefficient conclusions → the per-z coefficient polynomials Bj. The
  conditional bricks REDUCE each link, but the end-to-end assembly into "β exists ⟹ hcoeffPoly"
  is NOT yet a single proven theorem (the capstone skipped it by assuming Section55Output).
- PLUS the previously-listed: the §5 multiplicity datum (MultiplicityDatum, pending), F1 γ-fix,
  L13 drop-in (cross-file, coordinate). Then hcoeffPoly→Curves:1819→STIR/WHIR.

LESSON: a kernel-clean compile is necessary but NOT sufficient — always check the hypothesis is not
≡ the goal (vacuous/bundling). 28 GENUINE bricks stand; KeystoneCapstone is a wrapper, set aside.

## ★★ TRUE FINAL STATE 2026-06-05 — 29 genuine bricks (capstone excluded per F4)
MultiplicityDatum.lean ✅ (7 decls): discharges the §5 datum from IN-TREE proven facts —
`hord_of_rootMultiplicity_ge` (obligation 4 HasOrderAt ⟸ gsQ_multiplicity) +
`hdvd_C_of_Hlift_dvd` (obligation 1 ⟸ the GS-factor divisibility `Hlift H ∣ R`) +
`hdvd_C_value_of_hypotheses` (i₁=0, NO residual, from proven `Hypotheses`). δ≤δ₀ correctly stays at
its upstream producers. Non-vacuous (genuinely uses in-tree multiplicity, verified vs F4 lesson).

HONEST remaining work to reach Curves:1819 (post-F4):
1. ✅ ASSEMBLED conditionally: `ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec`
   genuinely proves `betaRec ⟹ CurveCoeffPolys` without assuming `hcoeffPoly`; it routes through
   `tail_zero_of_betaRec_embedding_zero`, `betaRec_embedding_eq_zero_of_matchingSet_large`,
   `alphaFromBeta`, and the linear-representative read-off.
2. Supply the remaining extraction/setup hypotheses for that theorem in the in-tree §5 context:
   matching-point data, matching-set cardinality/weight bound, γ representative data, degree-X bound,
   and the decoded-family specialization bridge.
3. Discharge the residual `Hlift H ∣ R` (GS-factor divisibility — in-tree App-A factorization fact).
4. F1 γ-recenter fix + L13 β_regular drop-in (cross-file RationalFunctions.lean — COORDINATE w/ live).
5. Then hcoeffPoly (front door Curves:1199) → correlatedAgreement_affine_curves clean → STIR/WHIR.
Prize Grand Challenges remain OPEN research independent of all this.
