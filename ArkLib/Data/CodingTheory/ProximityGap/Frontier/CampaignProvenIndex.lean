/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B2_char0_logconcave
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B5_MomentProblemLogConvex
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B6_cumulant_signs
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B8_kstability_char0_closure
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf8B9_GaussianConvexOrderExtremal
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf6F1_gaussian_step_telescope
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf6P1_nonprincipal_energy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfL3_char0_prize_moment
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wfL4_char0_nonprincipal_energy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf9G2_ResonanceCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf9G3_periodpoly_coeff_nogo
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._wf9G4_roughness_not_the_driver
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._BridgeOneWall
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoFifthDoorTetrachotomy
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoTighterBoundCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteShawValueThinFloor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteTrivialCeiling
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteBGKCompletionCorridor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ConcreteShawCompletionCorridorFull
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ShawValueCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.ShawValueBracketCenter
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharPWraparoundLogConcaveQ
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CharPStepRatioMonotoneFails
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RhoAntitoneFailsThinPrime
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVValueShiftHistogramObstruction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._WraparoundMarkovVacuity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVIndexFactorOvershoot
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCoherenceOrderBlind
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBSidonNoEnergyExcess
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVHalfMassEquivalence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVPrizeBddAbove
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVPrizeShawTetrachotomySynthesis
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawValueLandauBridge
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleDispersion
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVObjectMomentCorridor
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVObjectMomentTrappedCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVPrizeObjectGrandCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSignedDeepSumAbsLeak
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GaussPeriodMomentCensus
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleTrivialOvershoot
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacobiCocycleAllDefectCSVacuous
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvGR_GaussSumEnergyStep
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvDil_MultEnergyStepDiagonal
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._CoreReductionNecessity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVDecompositionInvariantCoherence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVMultiPieceSignCoherence
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSixthCumulantVanishes
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVTripleCorrelationVanishes
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCorrelationHierarchyCapstone
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCumulantLadderVacuity
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCrossHalfPhaseUnstructured
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVHalfMassBalanceAtArgmax
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVHalfMassDilationForm
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVSignCocycleMassBalance
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVAlgebraicFloorCyclotomicWall
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVEighthCumulantSignUnstable
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVXGatedPrizeReduction
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVXGatePrizeBudget
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVXGatedBaseThresholdConcrete
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstCosetCountSingleton
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ShawGrandSynthesis
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._GKPhaseCoboundaryNonLinear
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AttackMarkoffCouplingNoGo
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvTannakianNonTorsionPump
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWorstBHalfMassCarriesAll
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVZDegreeEnvelope
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWeight2QuadformGcd
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVWindowConcentrationTrivial
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVArgmaxDecouplingNoControl
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCollisionExcessPigeonhole
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCoherenceSaturationInsufficient
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVFractionalMomentNoMaxGain
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVGeomMeanBelowMax
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVPhaseBlindRadialStats
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVOrderedWalkDoobMajorant
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._StepanovAtBstar
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVOrderedWalkMajorant
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvDIR9OrderedWalkMajorant
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvDIR9ReflectionSteinitz
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._JacAutocorrL2SupGap
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvERG_ErgodicMaximalReducesToWall
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvFloor_ResonatorRatioLowerBound
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._AvFloor_MomentRatioLadderGeneral
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._SumProductCensusStallBeta4
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._RudnevDilutionFixedSavingStall
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCoherenceDeficitThicknessInvariant
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._DoorIVCoherenceSlackVacuousAtArgmax
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._A1SOSLadderN16
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._A3SumProductDepthConfinement
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._A5TwistedMonodromyAbelianVerdict

/-!
# Campaign-Proven Index — permanent named exports of the prize close-out (#444)

The #389/#407/#444 BGK / δ* campaign produced a large body of **axiom-clean** results in
fast-iteration scratch files (`Frontier/_wf*`). Those files are explicitly *throwaway*
(`Frontier/README.md`: "files starting `_` are throwaway"), yet several of their headline
theorems are load-bearing and proven. This module makes that proven content **permanent and
discoverable**: each load-bearing result below is re-exported under a stable, descriptively
named theorem in a non-underscore permanent module, carrying a docstring that states its
**scope** (`char-0` / `obstruction` / `prize-bridge`) and its axiom audit.

This is a **consolidation only** — no mathematics is changed. Every export here is a direct
alias of a proven theorem; the axiom audit at the bottom confirms the inherited profile is
`[propext, Classical.choice, Quot.sound]` (no `sorryAx`).

## Scope tags

* **char-0** — proven unconditionally in characteristic 0 (the regime where the Lam–Leung /
  Wick energy law `E_r ≤ (2r-1)‼·n^r` is a theorem). These are the substrate the prize bridges
  consume; they do NOT by themselves resolve the prize (which needs the char-`p` transfer at
  `r ≈ ln q`).
* **obstruction** — an axiom-clean proof that a *named candidate lever* cannot reach the prize
  floor (a countermodel / no-go). These are permanent negative results.
* **prize-bridge** — an axiom-clean named-conditional reduction: `<named input> ⟹ prize bound`,
  with the named input the only remaining obligation.

The remaining open core (`BGKBound(1/2)`, the thin dyadic Gauss-period exponent-1/2
cancellation) is documented in `PROXIMITY_PRIZE_WORKBENCH.lean` and is NOT discharged by
anything here; this index does not claim otherwise.

## Index of permanent exports (by scope)

| export | scope | source brick |
|---|---|---|
| `char0_stepRatio_antitone_iff_sharpNewton` | char-0 | B2 |
| `char0_W3anti_of_sharpNewton_export` | char-0 | B2 |
| `char0_kstability_cross_le_wick` | char-0 | B8 |
| `char0_prize_moment_bound_unconditional` | char-0 | L3 |
| `char0_prize_moment_bound_sq_unconditional` | char-0 | L3 |
| `char0_nonprincipalEnergyBound_discharged` | char-0 | L4 |
| `char0_eta_pow_le_unconditional` | char-0 | L4 |
| `gaussian_moment_telescope` | prize-bridge | F1 |
| `convexOrder_gaussian_iff_wick_export` | prize-bridge | B9 |
| `prize_of_matchedGaussian_stepLaw_export` | prize-bridge | B9 |
| `eta_pow_le_of_nonprincipalEnergyBound_export` | prize-bridge | P1 |
| `moment_problem_does_not_give_wick_bracket` | obstruction | B5 |
| `cumulant_sign_route_refuted` | obstruction | B6 |
| `resonance_ceiling_below_prize_floor` | obstruction | G2 |
| `coeff_route_loose_export` | obstruction | G3 |
| `roughness_does_not_add_bad_primes_export` | obstruction | G4 |
| `prizeBound_iff_shawValue_le_export` | capstone | ShawValue |
| `strictPrizeBound_iff_shawValue_lt_export` | capstone | ShawValue |
| `strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound_export` | capstone | ShawValue |
| `exists_strictRawPrizeFamilyBound_iff_exists_strictShawValueFamilyBound_export` | capstone | ShawValue |
| `not_exists_strictRawPrizeFamilyBound_iff_not_exists_strictShawValueFamilyBound_export` | capstone | ShawValue |
| `exists_nonneg_strictRawPrizeFamilyBound_iff_exists_nonneg_strictShawValueFamilyBound_export` | capstone | ShawValue |
| `not_exists_nonneg_strictRawPrizeFamilyBound_iff_not_exists_nonneg_strictShawValueFamilyBound_export` | capstone | ShawValue |
| `shawValue_worstPeriod_clean_corridor_export` | capstone | ShawValue |
| `shawValue_clean_corridor_width_eq_export` | capstone | ShawValue |
| `shawValue_bracket_width_eq_sqrt_export` | capstone | ShawValue |
| `worstPeriod_sharp_bracket_export` | capstone | ConcreteTrivialCeiling |
| `completion_vacuous_below_trivial_ceiling_export` | obstruction | ConcreteBGKCompletionCorridor |
| `shawValue_worstPeriod_torsion_full_corridor_export` | capstone | ConcreteShawCompletionCorridorFull |
| `worstPeriod_torsion_sharp_floor_export` | capstone | ConcreteShawCompletionCorridorFull |
| `charP_wrap_gap_ge_two_mul_sq_export` | obstruction | CharPWraparoundLogConcaveQ |
| `charP_wrap_gap_nonneg_of_logConcave_export` | obstruction | CharPWraparoundLogConcaveQ |
| `charP_transfer_of_dominance_logConcave_export` | obstruction | CharPWraparoundLogConcaveQ |
| `charP_stepRatioMonotoneAt_iff_gap_nonneg_export` | obstruction | CharPStepRatioFails |
| `charP_stepRatioMonotone_false_n32_export` | obstruction | CharPStepRatioFails |
| `charP_no_universal_positive_stepRatioMonotone_export` | obstruction | CharPStepRatioFails |
| `rho_normalized_antitone_and_ceiling_incompatible_export` | obstruction | RhoAntitoneFails |
| `rho_antitone_route_not_universal_export` | obstruction | RhoAntitoneFails |
| `valueShift_nontrivial_forces_flat_histogram_export` | obstruction | DoorIVValueShiftHistogramObstruction |
| `valueShift_step_zero_of_one_histogram_witness_export` | obstruction | DoorIVValueShiftHistogramObstruction |
| `valueShift_route_vacuous_of_one_histogram_witness_export` | obstruction | DoorIVValueShiftHistogramObstruction |
| `wraparound_markov_count_le_export` | obstruction | WraparoundMarkovVacuity |
| `wraparound_markov_bound_vacuous_below_mean_export` | obstruction | WraparoundMarkovVacuity |
| `wraparound_average_control_does_not_bound_sup_export` | obstruction | WraparoundMarkovVacuity |
| `doorIV_naiveIncidenceScale_eq_sqrt_mul_prizeScale_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_naiveIncidenceBound_iff_shawValue_le_scaled_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_index_le_sq_of_scaledConstant_le_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_scaledConstant_le_iff_index_le_sq_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_not_scaledConstantFamily_le_uniform_of_exists_index_gt_sq_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_prizeScale_lt_naiveIncidenceScale_of_one_lt_m_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_constant_lt_scaledConstant_of_one_lt_m_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_not_scaledConstant_le_constant_of_one_lt_m_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_constant_lt_scaledConstant_iff_one_lt_m_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_prizeScale_lt_naiveIncidenceScale_iff_one_lt_m_export` | obstruction | DoorIVIndexFactorOvershoot |
| `doorIV_cosetInvariant_blind_to_order_export` | obstruction | DoorIVCoherenceOrderBlind |
| `doorIV_cosetHitting_selector_bound_iff_global_export` | obstruction | DoorIVCoherenceOrderBlind |
| `doorIV_strict_selector_bound_misses_coset_export` | obstruction | DoorIVCoherenceOrderBlind |
| `doorIV_additiveEnergyExcess_eq_zero_iff_sidon_export` | obstruction | DoorIVWorstBSidonNoEnergyExcess |
| `doorIV_no_positive_additiveEnergyExcess_of_subset_sidon_export` | obstruction | DoorIVWorstBSidonNoEnergyExcess |
| `doorIV_positive_additiveEnergyExcess_iff_not_sidon_export` | obstruction | DoorIVWorstBSidonNoEnergyExcess |
| `doorIV_prizeFamilyBound_iff_halfMassFamilyBound_export` | capstone | DoorIVHalfMassEquivalence |
| `doorIV_prizeFamilyBound_iff_normalizedHalfMassFamilyBound_export` | capstone | DoorIVHalfMassEquivalence |
| `doorIV_prizeFamilyBound_iff_all_halfMassShaw_forms_export` | capstone | DoorIVHalfMassEquivalence |
| `doorIV_bddAbove_nonneg_normalizedPrize_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_bddAbove_nonneg_normalizedHalfMass_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_bddAbove_nonneg_rawPrize_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_bddAbove_nonneg_rawHalfMass_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_bddAbove_prize_iff_nonneg_rawHalfMass_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_bddAbove_halfMass_iff_nonneg_rawPrize_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_not_nonneg_rawPrize_iff_prizeDrift_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_not_nonneg_rawHalfMass_iff_halfMassDrift_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_not_bddAbove_prize_iff_not_bddAbove_halfMass_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_not_bddAbove_prize_iff_halfMassDrift_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_not_bddAbove_halfMass_iff_prizeDrift_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_bddAbove_prize_iff_not_halfMassDrift_export` | capstone | DoorIVPrizeBddAbove |
| `doorIV_bddAbove_halfMass_iff_not_prizeDrift_export` | capstone | DoorIVPrizeBddAbove |
| `shawOOne_bddAbove_range_shawValue_export` | capstone | ShawValueCapstone |
| `corePrize_bddAbove_range_shawValue_export` | capstone | ShawValueCapstone |
| `corePrize_bddAbove_range_shawValue_of_pos_lt_export` | capstone | ShawValueCapstone |
| `shawOOne_unbounded_shawValue_drift_export` | capstone | ShawValueCapstone |
| `corePrize_unbounded_shawValue_drift_export` | capstone | ShawValueCapstone |
| `corePrize_unbounded_shawValue_drift_of_pos_lt_export` | capstone | ShawValueCapstone |
| `doorIV_prize_iff_shawBounded_nonneg_and_doorIV_only_export` | capstone | DoorIVPrizeShawTetrachotomySynthesis |
| `doorIV_remaining_gap_is_sqrtL_factor_doorIV_only_export` | capstone | DoorIVPrizeShawTetrachotomySynthesis |
| `doorIV_prize_iff_shawBounded_nonneg_and_floorPrizeRatio_export` | capstone | DoorIVPrizeShawTetrachotomySynthesis |
| `doorIV_corePrize_of_dominated_majorant_export` | capstone | ShawValueCapstone |
| `doorIV_shawOOne_of_coreMajorant_export` | capstone | ShawValueCapstone |
| `doorIV_landau_shaw_of_dominated_majorant_export` | capstone | ShawValueLandauBridge |
| `doorIV_shawOOne_of_dominated_majorant_export` | capstone | ShawValueLandauBridge |
| `trivial_cocycle_full_concentration_export` | obstruction | JacobiCocycleDispersion |
| `trivial_cocycle_offSupport_zero_export` | obstruction | JacobiCocycleDispersion |
| `jacobiCocycleDispersion_iff_shawValue_le_export` | capstone | JacobiCocycleDispersion |
| `exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound_pos_export` | capstone | JacobiCocycleDispersion |
| `not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_pos_export` | capstone | JacobiCocycleDispersion |
| `exists_jacobiCocycleDispersionFamilyBound_iff_rawSandwich_export` | capstone | JacobiCocycleDispersion |
| `doorIV_arithMean_le_max_export` | obstruction | DoorIVGeomMeanBelowMax |
| `doorIV_weightedMean_le_max_export` | obstruction | DoorIVGeomMeanBelowMax |
| `doorIV_weightedSubmean_le_max_export` | obstruction | DoorIVGeomMeanBelowMax |
| `doorIV_radialSum_invariant_under_unit_twist_export` | obstruction | DoorIVPhaseBlindRadialStats |
| `doorIV_stepanov_bstar_bound_export` | obstruction | StepanovAtBstar |
| `doorIV_bstar_saving_iff_degenerate_export` | obstruction | StepanovAtBstar |
| `doorIV_orderedWalk_endpoint_le_maximalExcursion_export` | obstruction | DoorIVOrderedWalkMajorant |
| `doorIV_orderedWalk_endpoint_bound_of_maximal_bound_export` | obstruction | DoorIVOrderedWalkMajorant |
| `doorIV_avDIR9Reflection_endpoint_le_R_export` | obstruction | AvDIR9Reflection |
| `doorIV_avDIR9Reflection_endpoint_id_export` | obstruction | AvDIR9Reflection |
| `doorIV_avDIR9Reflection_endpoint_norm_le_two_R1_export` | obstruction | AvDIR9Reflection |
| `doorIV_avDIR9Reflection_half_norm_ge_endpoint_half_export` | obstruction | AvDIR9Reflection |
| `doorIV_avDIR9Reflection_bound_two_R1_export` | obstruction | AvDIR9Reflection |
| `doorIV_avDIR9Reflection_reduces_export` | obstruction | AvDIR9Reflection |
| `doorIV_abs_signed_le_abs_moment_export` | obstruction | DoorIVSignedDeepSumAbsLeak |
| `doorIV_leak_nonneg_export` | obstruction | DoorIVSignedDeepSumAbsLeak |
| `doorIV_abs_moment_bound_transfers_export` | obstruction | DoorIVSignedDeepSumAbsLeak |
| `trivial_cocycle_overshoots_thin_export` | obstruction | JacobiCocycleTrivialOvershoot |
| `trivial_overshoot_gap_pos_export` | obstruction | JacobiCocycleTrivialOvershoot |
| `allDefect_cs_floor_vacuous_export` | obstruction | JacobiCocycleAllDefectCSVacuous |
| `gaussEnergyStep_incrementOne_lt_two_n_export` | capstone | AvGR_GaussSumEnergyStep |
| `gaussEnergyStep_step_of_increments_le_export` | capstone | AvGR_GaussSumEnergyStep |
| `dilationEnergy_step_iff_offdiagonal_export` | capstone | AvDil_MultEnergyStepDiagonal |
| `dilationEnergy_deep_step_of_depth2K_energy_export` | obstruction | AvDil_MultEnergyStepDiagonal |
| `dilationEnergy_not_deep_step_of_offdiagonal_gt_export` | obstruction | AvDil_MultEnergyStepDiagonal |
| `dilationEnergy_not_depth2K_energy_of_cs_and_offdiagonal_gt_export` | obstruction | AvDil_MultEnergyStepDiagonal |
| `coreReduction_mStar_gt_of_BCHKS_fails_export` | capstone | CoreReductionNecessity |
| `coreReduction_mStar_le_iff_BCHKS_export` | capstone | CoreReductionNecessity |
| `coreReduction_clears_johnson_iff_BCHKS_at_prev_fold_export` | capstone | CoreReductionNecessity |
| `doorIV_decomposition_block_sum_common_ray_export` | obstruction | DoorIVDecompositionInvariantCoherence |
| `doorIV_decomposition_partition_invariant_coherence_export` | obstruction | DoorIVDecompositionInvariantCoherence |
| `doorIV_decomposition_no_partition_beats_one_export` | obstruction | DoorIVDecompositionInvariantCoherence |
| `doorIV_multiPiece_coherence_mem_Icc_export` | obstruction | DoorIVMultiPieceSignCoherence |
| `doorIV_multiPiece_exact_saving_export` | obstruction | DoorIVMultiPieceSignCoherence |
| `doorIV_multiPiece_eps_budget_eq_export` | obstruction | DoorIVMultiPieceSignCoherence |
| `doorIV_multiPiece_eps_budget_iff_export` | obstruction | DoorIVMultiPieceSignCoherence |
| `doorIV_multiPiece_no_eps_slack_one_side_zero_export` | obstruction | DoorIVMultiPieceSignCoherence |
| `doorIV_multiWindow_budget_forces_card_le_export` | obstruction | DoorIVWindowConcentrationTrivial |
| `doorIV_no_multiWindow_split_rhs_le_strict_budget_export` | obstruction | DoorIVWindowConcentrationTrivial |
| `doorIV_argmaxDecoupled_const_ge_ratio_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_no_control_below_ratio_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_uniformControl_iff_ratio_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_exists_ratio_gt_no_control_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_uniformControlOn_iff_ratio_on_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_exists_ratio_gt_no_controlOn_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_candidate_pos_on_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_positive_support_on_subset_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_no_nonpos_candidate_controlOn_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_no_zero_candidate_controlOn_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_control_constant_pos_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_no_nonpos_candidate_control_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_no_zero_candidate_control_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_candidate_pos_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_positive_support_subset_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_argmaxDecoupled_no_absolute_const_export` | obstruction | DoorIVArgmaxDecouplingNoControl |
| `doorIV_collision_defect_eq_zero_iff_injOn_export` | obstruction | DoorIVCollisionExcessPigeonhole |
| `doorIV_collision_defect_pos_iff_not_injOn_export` | obstruction | DoorIVCollisionExcessPigeonhole |
| `doorIV_tripleCorrelation_sixPoint_zero_export` | obstruction | DoorIVTripleCorrelationVanishes |
| `doorIV_tripleCorrelation_sixPoint_vacuous_export` | obstruction | DoorIVTripleCorrelationVanishes |
| `doorIV_tripleCorrelation_m33_eq_wick_export` | obstruction | DoorIVTripleCorrelationVanishes |
| `doorIV_crossHalf_norm_add_eq_halfMass_export` | obstruction | DoorIVCrossHalfPhaseUnstructured |
| `doorIV_crossHalf_fixed_multiplier_forces_ratio_le_export` | obstruction | DoorIVCrossHalfPhaseUnstructured |
| `doorIV_crossHalf_fixed_multiplier_fails_of_ratio_gt_export` | obstruction | DoorIVCrossHalfPhaseUnstructured |
| `doorIV_halfMassBalance_single_half_pays_floor_export` | obstruction | DoorIVHalfMassBalanceAtArgmax |
| `doorIV_halfMassBalance_descent_loss_eq_two_export` | obstruction | DoorIVHalfMassBalanceAtArgmax |
| `doorIV_halfMassBalance_descent_loss_le_two_export` | obstruction | DoorIVHalfMassBalanceAtArgmax |
| `doorIV_halfMass_eta_image_smul_eq_eta_dilate_export` | capstone | DoorIVHalfMassDilationForm |
| `doorIV_halfMass_eta_index_two_split_dilate_export` | capstone | DoorIVHalfMassDilationForm |
| `doorIV_halfMass_norm_eta_le_two_dilate_export` | capstone | DoorIVHalfMassDilationForm |
| `doorIV_sign_positiveMass_eq_negativeMass_export` | obstruction | DoorIVSignCocycleMassBalance |
| `doorIV_sign_not_all_nonneg_of_positiveMass_pos_export` | obstruction | DoorIVSignCocycleMassBalance |
| `doorIV_sign_exists_negative_cross_of_positiveMass_pos_export` | obstruction | DoorIVSignCocycleMassBalance |
| `doorIV_sign_exists_positive_cross_of_negativeMass_pos_export` | obstruction | DoorIVSignCocycleMassBalance |
| `doorIV_sign_positiveMass_le_half_card_export` | obstruction | DoorIVSignCocycleMassBalance |
| `doorIV_sign_negativeMass_le_half_card_export` | obstruction | DoorIVSignCocycleMassBalance |
| `doorIV_sign_positiveMass_eq_half_total_doublingMass_export` | obstruction | DoorIVSignCocycleMassBalance |
| `doorIV_sign_negativeMass_eq_half_total_doublingMass_export` | obstruction | DoorIVSignCocycleMassBalance |
| `doorIV_gappedMinor125_159_eq_zero_export` | obstruction | DoorIVAlgebraicFloorCyclotomicWall |
| `doorIV_not_gappedMinor125_159_ne_zero_export` | obstruction | DoorIVAlgebraicFloorCyclotomicWall |
| `doorIV_eighthCumulant_mixed_sign_forbids_fixed_sign_export` | obstruction | DoorIVEighthCumulantSignUnstable |
| `doorIV_eighthCumulant_no_fixedSignCertificate_export` | obstruction | DoorIVEighthCumulantSignUnstable |
| `doorIV_levelWorst_le_sqrt_two_pow_mul_of_xGatedRatio_export` | capstone | DoorIVXGatedPrizeReduction |
| `doorIV_levelWorst_le_prize_budget_of_xgate_export` | capstone | DoorIVXGatePrizeBudget |
| `doorIV_gateThreshold_split_telescope_sqrt2_export` | obstruction | DoorIVXGatedBaseThreshold |
| `doorIV_gateThreshold_strictly_above_clean_export` | obstruction | DoorIVXGatedBaseThreshold |
| `doorIV_levelWorst_base_step_two_export` | obstruction | DoorIVXGatedBaseThresholdConcrete |
| `doorIV_levelWorst_base_corrected_of_gate_export` | obstruction | DoorIVXGatedBaseThresholdConcrete |

## Lane-2 capstone (the `prize ⟺ Sh(n)=O(1)` normalization)

The **capstone** scope tag marks the Lane-2 deliverable of the door-(iv) phase (#444,
Shaw-value essay 2026-06-18): the axiom-clean reduction of the prize inequality to a bounded
normalized *Shaw value* `Sh(M) = M / √(n·L)`, together with the proven two-sided corridor
`1/√(2L) ≤ Sh(M(μ_n)) ≤ √(n/L)` on the REAL Gauss-period worst frequency `M(μ_n)`. The floor is
unconditional (thin-regime Parseval, `q ≥ 2n`); the ceiling is unconditional (triangle
inequality); the open prize is *exactly* the demand to collapse this `√n`-wide corridor to an
absolute constant. These are normalization/consolidation only — no anti-concentration, completion,
moment, or capacity claim is hidden, and CORE stays OPEN.
-/

open scoped Nat

namespace ArkLib.ProximityGap.Frontier.CampaignProvenIndex

open ProximityGap.PrizeWorkbench
open ArkLib.ProximityGap.Frontier
open Asymptotics Filter
-- `eta` (the subgroup Gauss-sum period) lives here; needed for the L4/P1 exports below.
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ArkLib.ProximityGap.SubgroupGaussSumMomentLadder
open ArkLib.ProximityGap.NegationClosedWalk
open ArkLib.ProximityGap.Frontier.ShawValueCapstone
open ProximityGap.Frontier.ConcreteShawValueThinFloor
open ProximityGap.Frontier.WorstPeriodSqrtNFloor

/-! ## B2 — char-0 Wick step-ratio antitonicity (log-concavity), reduced to the classical
`SharpNewtonBessel` (Laguerre–Pólya type-I) input. Scope: **char-0**. -/

/-- **[char-0, B2]** The char-0 Wick-normalised moment step ratio `R d r = m_{r+1}/m_r` is
antitone in `r` **iff** the sharp Newton inequality holds for the Bessel power coefficients —
an exact, axiom-clean algebraic equivalence (no analytic input). -/
theorem char0_stepRatio_antitone_iff_sharpNewton (d : ℕ) (hd : 1 ≤ d) (r : ℕ) :
    Rstep d (r + 1) ≤ Rstep d r ↔
      ((r + 2 : ℕ) : ℚ) * besselCoeff d (r + 2) * besselCoeff d r
        ≤ ((r + 1 : ℕ) : ℚ) * (besselCoeff d (r + 1)) ^ 2 :=
  R_antitone_iff_sharpNewton hd r

/-- **[char-0, B2]** Headline: the classical `SharpNewtonBessel` (LP-I) hypothesis yields the
full telescope input `R d r ≤ 1` for all `r`, i.e. char-0 Wick monotonicity (`W3-anti`). -/
theorem char0_W3anti_of_sharpNewton_export (d : ℕ) (hd : 1 ≤ d)
    (hSN : SharpNewtonBessel d) : ∀ r, Rstep d r ≤ 1 :=
  char0_W3anti_of_sharpNewton hd hSN

/-! ## B8 — char-0 K=1 K-stability cross bound (the dyadic convolution closes). Scope: **char-0**. -/

/-- **[char-0, B8]** The char-0 `K = 1` K-stability cross bound. From the exact dyadic
convolution `E_r(μ_n) = ∑ C(2r,2j)·E_j(H)·E_{r-j}(H)` (`H = μ_{n/2}`, `-1 ∈ H`) and the per-set
char-0 Wick bound, the interior (cross) energy satisfies
`E_r(μ_n) - 2·E_r(H) ≤ (2r-1)‼·((2h)^r - 2 h^r) = Wick(n,r) - 2·Wick(n/2,r)`. -/
theorem char0_kstability_cross_le_wick {r : ℕ} (hr : 1 ≤ r) {h Eμn : ℝ} (hh : 0 ≤ h)
    (E : ℕ → ℝ) (hE0 : E 0 = 1) (hEnonneg : ∀ j, 0 ≤ E j)
    (hconv : Eμn = ∑ j ∈ Finset.range (r + 1),
        (Nat.choose (2 * r) (2 * j) : ℝ) * E j * E (r - j))
    (hwick : ∀ j, j ≤ r → E j ≤ ((2 * j - 1)‼ : ℝ) * h ^ j) :
    Eμn - 2 * E r ≤ ((2 * r - 1)‼ : ℝ) * ((2 * h) ^ r - 2 * h ^ r) :=
  W5KStabilityChar0.cross_le_wick_cross hr hh E hE0 hEnonneg hconv hwick

/-! ## L3 — the FULL char-0 prize moment bound as ONE *unconditional* theorem (no Sidon /
no antipodal-pairing hypothesis; the char-0 Lam–Leung energy bound is discharged internally via
`DyadicEnergyK1`). Scope: **char-0**. This is the strongest single proven statement of the
campaign: in characteristic 0 the per-frequency prize cancellation is a *theorem*, with the only
remaining gap being the char-`p` transfer at the prize scale `n = 2^30` (the BGK wall). -/

/-- **[char-0, L3]** THE char-0 prize moment bound (norm form), UNCONDITIONAL. For `G ⊆ μ_{2^k}`
(`k ≥ 1`) in a characteristic-zero field, a formal period sup `M` with `Q ≥ 1` frequencies and the
formal-period moment identity `M^{2r} ≤ Q·E_r(G)` obeys, at optimal depth `r ≥ max(1, log Q)`, the
prize square-root shape `M ≤ √(2e·|G|·r)`. The Lam–Leung energy bound `E_r ≤ (2r-1)‼·|G|^r` is
proven *inside* the theorem (char-0); there is no Sidon/`repThree`/pairing side hypothesis. -/
theorem char0_prize_moment_bound_unconditional {L : Type*} [Field L] [CharZero L] [DecidableEq L]
    {k r : ℕ} (hk : 1 ≤ k) (G : Finset L)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1)
    {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 < Q) (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : M ^ (2 * r) ≤ Q * (zeroSumCount G (2 * r) : ℝ)) :
    M ≤ Real.sqrt (2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ)) :=
  WFL3.char0_prize_moment_bound hk G hG hM hQ hr hrQ hmoment

/-- **[char-0, L3]** Squared form of `char0_prize_moment_bound_unconditional`: `M² ≤ 2e·|G|·r`. -/
theorem char0_prize_moment_bound_sq_unconditional {L : Type*} [Field L] [CharZero L]
    [DecidableEq L] {k r : ℕ} (hk : 1 ≤ k) (G : Finset L)
    (hG : ∀ z ∈ G, z ^ (2 ^ k) = 1)
    {M Q : ℝ} (hM : 0 ≤ M) (hQ : 0 < Q) (hr : 1 ≤ r) (hrQ : Real.log Q ≤ r)
    (hmoment : M ^ (2 * r) ≤ Q * (zeroSumCount G (2 * r) : ℝ)) :
    M ^ 2 ≤ 2 * Real.exp 1 * (G.card : ℝ) * (r : ℝ) :=
  WFL3.char0_prize_moment_bound_sq hk G hG hM hQ hr hrQ hmoment

/-! ## L4 — char-0 discharge of the nonprincipal-energy named hypothesis `(S-M1')` and the
per-frequency sup bound wired through the P1 bridge. Scope: **char-0** (the char-0 energy bound is
the proven `DyadicEnergyK1` value). -/

/-- **[char-0, L4]** Under the char-0 additive-energy bound `E_r(G) ≤ (2r-1)‼·|G|^r`, the named
nonprincipal-energy hypothesis `NonprincipalEnergyBound` holds with `doubleFact = (2r-1)‼` (`K=1`):
`q·E_r − n^{2r} ≤ q·(2r-1)‼·n^r`. Discharges `(S-M1')` from the char-0 substrate. -/
theorem char0_nonprincipalEnergyBound_discharged {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (G : Finset F) (r : ℕ)
    (henergy : (energyR G r : ℝ) ≤ ((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r) :
    WF6P1.NonprincipalEnergyBound (F := F) G r ((2 * r - 1)‼ : ℝ) :=
  WFL4.nonprincipalEnergyBound_of_energyR_le G r henergy

/-- **[char-0, L4]** Composing the char-0 discharge with the P1 bridge: under the char-0 energy
bound, every nontrivial frequency obeys the Gaussian/Wick sup bound
`‖η_b‖^{2r} ≤ q·(2r-1)‼·|G|^r`. In characteristic 0 the hypothesis is the proven `DyadicEnergyK1`
value, so this is an unconditional per-frequency bound there. -/
theorem char0_eta_pow_le_unconditional {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (henergy : (energyR G r : ℝ) ≤ ((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r)
    (b : F) (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (((2 * r - 1)‼ : ℝ) * (G.card : ℝ) ^ r) :=
  WFL4.char0_eta_pow_le_of_energyR_le hψ G r henergy b hb

/-! ## F1 — the sub-Gaussian moment telescope (the consumer that turns a per-step Gaussian
step-law into the full Wick even-moment bound). Scope: **prize-bridge**. -/

/-- **[prize-bridge, F1]** THE TELESCOPE. A nonnegative moment sequence obeying the Gaussian
step-law `M(r+1) ≤ (2r+1)·s·M(r)` from base `M 0 ≤ 1` satisfies the full sub-Gaussian even-moment
bound `M r ≤ (2r-1)‼·s^r` for every `r`. Pure induction; the load-bearing consumer of every
step-law lever. -/
theorem gaussian_moment_telescope {M : ℕ → ℝ} {s : ℝ}
    (hs : 0 ≤ s) (hM : ∀ r, 0 ≤ M r) (hbase : M 0 ≤ 1)
    (hstep : WF6F1.GaussianStepLaw M s) :
    ∀ r : ℕ, M r ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * s ^ r :=
  WF6F1.gaussian_moment_bound_of_stepLaw hs hM hbase hstep

/-! ## B9 — the matched Gaussian is the unique extremal target; its step-law telescopes to the
prize. Scope: **char-0 / prize-bridge** (the step-law is the named input). -/

/-- **[prize-bridge, B9]** Convex-order domination by the matched Gaussian ⟺ the Wick bound. -/
theorem convexOrder_gaussian_iff_wick_export {n : ℕ} (hn : 1 ≤ n) (M : ℕ → ℝ) :
    (∀ r, M r ≤ WF8B9.gaussianMoment n r) ↔ (∀ r, WF8B9.wickMoment M n r ≤ 1) :=
  WF8B9.convexOrder_gaussian_iff_wick hn M

/-- **[prize-bridge, B9]** Headline: if the period moment sequence obeys the matched-Gaussian
sub-step-law `M(r+1) ≤ (2r+1)·n·M(r)` from base `M 0 ≤ 1`, then `wickMoment M n r ≤ 1` for all
`r` — i.e. the period law is convex-order-dominated by `N(0,n)` (= the prize). The matched
Gaussian is pinned as the unique minimal target. -/
theorem prize_of_matchedGaussian_stepLaw_export {n : ℕ} (hn : 1 ≤ n) {M : ℕ → ℝ}
    (hM : ∀ r, 0 ≤ M r) (hbase : M 0 ≤ 1) (hstep : WF6F1.GaussianStepLaw M (n : ℝ)) :
    ∀ r, WF8B9.wickMoment M n r ≤ 1 :=
  WF8B9.prize_of_matchedGaussian_stepLaw hn hM hbase hstep

/-! ## P1 — the nonprincipal-energy bridge (the live moment-route lever). Scope: **prize-bridge**. -/

/-- **[prize-bridge, P1]** The named sufficient hypothesis `(S-M1')` — the nonprincipal additive
energy bound — implies the per-frequency sup bound `‖η_b‖^{2r} ≤ q·(doubleFact·|G|^r)` for every
nonprincipal `b`. With `doubleFact = (2r-1)‼` and depth `r ≈ ln q`, this is the prize
cancellation `max_{b≠0}‖η_b‖ ≤ C√(n log q)`. The correct, non-vacuous moment-route lever. -/
theorem eta_pow_le_of_nonprincipalEnergyBound_export {F : Type*} [Field F] [Fintype F]
    [DecidableEq F] {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (doubleFact : ℝ) (hbnd : WF6P1.NonprincipalEnergyBound (F := F) G r doubleFact)
    (b : F) (hb : b ≠ 0) :
    ‖eta ψ G b‖ ^ (2 * r) ≤ (Fintype.card F : ℝ) * (doubleFact * (G.card : ℝ) ^ r) :=
  WF6P1.eta_pow_le_of_nonprincipalEnergyBound hψ G r doubleFact hbnd b hb

/-! ## B5 / B6 — the moment-problem obstructions. Scope: **obstruction**. -/

/-- **[obstruction, B5]** Hankel-positivity (the free moment-problem half `M₁² ≤ M₀·M₂`) does
NOT imply the ultra-sub-Gaussian Wick bracket: there is an explicit positive raw-moment sequence
that satisfies the free half yet violates `UltraSubGaussianStep` at `r = 1`. Any unconditional
moment-sequence theorem (which sees only positivity) cannot establish `W3-anti`. -/
theorem moment_problem_does_not_give_wick_bracket :
    ∃ (M W : ℕ → ℝ) (n : ℕ),
      (∀ k, 0 < M k) ∧ (∀ k, W k = ((2 * k - 1)‼ : ℝ) * (n : ℝ) ^ k) ∧
      (M 1) ^ 2 ≤ (M 0) * (M 2) ∧
      ¬ _root_.ProximityGap.Frontier.MomentProblemB5.UltraSubGaussianStep M W 1 :=
  _root_.ProximityGap.Frontier.MomentProblemB5.ultraSubGaussian_not_free

/-- **[obstruction, B6]** The cumulant-sign sufficiency criterion is refuted at the actual
period law: no cumulant sequence with `κ₄ < 0` can have `κ₈ > 0` and still meet the
nonpositive-higher-cumulant envelope. The period law's cumulants are sign-indefinite, so the
cumulant route cannot drive the prize bound. -/
theorem cumulant_sign_route_refuted {κ : ℕ → ℝ} (h4 : κ 2 < 0) (h8 : 0 < κ 4) :
    ¬ (∀ r, 2 ≤ r → κ r ≤ 0) :=
  CumulantSigns.subWick_positivity_refuted h4 h8

/-! ## G2 / G3 / G4 — the late-campaign lever obstructions (resonance / coefficient / roughness).
Scope: **obstruction**. Each is an axiom-clean proof that a named candidate lever cannot reach the
prize floor `√(n·log(p/n))`. -/

/-- **[obstruction, G2]** The Parseval/RMS resonance certificate is strictly below the prize floor
in the thin prize regime: `c·√n < √(n·L)` whenever `0 < n`, `0 ≤ c`, `c² < L`. With the measured
resonance constant `c ≤ 2` and the prize index `L = log(p/n) = log m ≫ c²`, the resonance route
gives NO Ω-disproof of `C = O(1)`. -/
theorem resonance_ceiling_below_prize_floor (c n L : ℝ) (hn : 0 < n) (hc : 0 ≤ c) (hL : c ^ 2 < L) :
    c * Real.sqrt n < Real.sqrt (n * L) :=
  WF9G2.resonance_below_floor c n L hn hc hL

/-- **[obstruction, G3]** The cyclotomy-coefficient (Fujiwara coefficient-root) route is loose by a
divergent factor: for every constant `C` there is an `m` with `fujiwaraAtTwo (n·m+1) n > C·prizeScale n m`
for all `n > 0`. No coefficient-magnitude root bound can meet the BGK target. -/
theorem coeff_route_loose_export (C : ℝ) (hC : 0 < C) :
    ∃ m : ℝ, 2 ≤ m ∧
      ∀ n : ℝ, 0 < n →
        WF9G3.fujiwaraAtTwo (n * m + 1) n > C * WF9G3.prizeScale n m :=
  WF9G3.coeff_route_loose C hC

/-- **[obstruction, G4]** Roughness is not the driver: the per-config bad-prime set `{p : p ∣ N}`
is determined by the FIXED integer `N` alone, so adjoining a roughness side-condition `rough p` can
only restrict it — `{p : p ∣ N ∧ rough p} ⊆ {p : p ∣ N}`. The largest prime factor of `m = (p-1)/n`
is not a parameter of the bad set. -/
theorem roughness_does_not_add_bad_primes_export (N : ℕ) (rough : ℕ → Prop) :
    {p : ℕ | p ∣ N ∧ rough p} ⊆ {p : ℕ | p ∣ N} :=
  G4RoughnessNotTheDriver.roughness_does_not_add_bad_primes N rough

/-! ## prize-bridge — the two faces are ONE wall (Parseval-dual; answers the "campaign still
points miners at the refuted bare sup-norm" flag, #444). The additive-energy face and the
multiplicative sup-norm face are the SAME object, bracketed within the trivial averaging factor
`q−1`. The link is the exact moment identity `sum_nonzero_moment` — NO loss and NO gain — so the
open core is one wall in two Fourier-dual bases, not two independent walls to be bridged. -/

/-- **[prize-bridge, OneWall]** The backward bridge: a sup-norm bound forces an energy bound. If
every nonzero period satisfies `‖η_b‖ ≤ M`, then the additive energy is controlled by `M`:
`q·E_r − n^{2r} ≤ (q−1)·M^{2r}`. Together with the forward `M^{2r} ≤ q·E_r − n^{2r}`
(worst-term ≤ sum), the worst-case sup-norm `M^{2r}` and the additive energy `E_r` bracket each
other within `q−1`: the additive count and the Gauss-phase worst case carry IDENTICAL information.
This is the consolidating statement that the prize is one wall, not two independent obstructions. -/
theorem two_faces_are_one_wall_export {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hsup : ∀ b ∈ Finset.univ.erase (0 : F),
      ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ≤ M) :
    (Fintype.card F : ℝ)
        * (_root_.ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G r : ℝ)
        - (G.card : ℝ) ^ (2 * r)
      ≤ ((Fintype.card F : ℝ) - 1) * M ^ (2 * r) :=
  _root_.ArkLib.ProximityGap.Frontier.BridgeOneWall.pincer_is_one_wall hψ G r hM hsup

/-! ## NoFifthDoor — the Lane-2/3 tetrachotomy capstone (Shaw's "Shaw Value" essay, #444).
Scope: **capstone**. The headline citable statement of the campaign: there is NO fifth door, every
prize-scale certificate must pass through door (iv) (a genuinely new monomial-sum evaluation), and the
remaining obligation is exactly to shave the `√L = √log(p/n)` factor separating the BGK ceiling
`√(n·L)` that doors (i)-(iii) deliver from the prize floor `√n`. Pure scale algebra over the
abstract `Mechanism`/`DoorType` model; the classical-overshoot hypothesis is the formal content of the
proven Lever A-D refutations (indexed above as the obstruction-scope exports). -/

/-- **[capstone, NoFifthDoor]** No fifth door: if every classical door (moment/completion/extreme-value)
overshoots the BGK scale (the proven Lever A-D fate) in the regime `L > 1`, then any mechanism `m`
certifying a prize-scale bound `m.certScale ≤ √n` has door `newEvaluation` — door (iv) is the ONLY
door through which a prize-scale certificate can pass. -/
theorem noFifthDoor_forces_doorIV_export
    {m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism} {n L : ℝ}
    (hn : 0 < n) (hL : 1 < L)
    (hclassicalOvershoots :
      ∀ m' : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK n L)
    (hcert : m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n) :
    m.door = _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.forces_doorIV hn hL
    hclassicalOvershoots hcert

/-- **[capstone, NoFifthDoor]** Existential form: under the classical-overshoot hypothesis, the set of
prize-certifying mechanisms is contained in the door-(iv) mechanisms. Every prize-scale certificate is
a door-(iv) certificate. -/
theorem prizeCertifying_subset_doorIV_export {n L : ℝ} (hn : 0 < n) (hL : 1 < L)
    (hclassicalOvershoots :
      ∀ m' : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK n L) :
    ∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
      m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n →
      m.door = _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeCertifying_subset_doorIV hn hL
    hclassicalOvershoots

/-- **[capstone, NoFifthDoor]** The door-(iv) target corridor: the worst-frequency sup `M` lives in
`[√n, √(n·L)]` — the prize floor (Plancherel/RMS) below and the BGK ceiling (what doors (i)-(iii)
deliver) above. The entire remaining door-(iv) content is to descend from the ceiling to the floor. -/
theorem doorIV_corridor_export {M n L : ℝ}
    (hfloor : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n ≤ M)
    (hceil : M ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n L) :
    _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n ≤ M ∧
      M ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n L :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.mem_doorIV_corridor hfloor hceil

/-- **[capstone, NoFifthDoor]** The corridor has positive width in the prize regime `L > 1`: the
floor is strictly below the ceiling, so the door-(iv) shave is a real `√L`-factor gap, not a point. -/
theorem doorIV_corridor_width_pos_export {n L : ℝ} (hn : 0 < n) (hL : 1 < L) :
    _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n
      < _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n L :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.doorIV_corridor_width_pos hn hL

/-- **[capstone, NoFifthDoor]** The exact factor door (iv) must remove: the BGK ceiling equals the
prize floor scaled by `√L`, i.e. `√(n·L) = √L · √n`. Pins the door-(iv) obligation quantitatively. -/
theorem bgkScale_eq_sqrtL_mul_prizeScale_export {n L : ℝ} (hn : 0 ≤ n) (hL : 0 ≤ L) :
    _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n L
      = Real.sqrt L * _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale_eq_sqrtL_mul_prizeScale hn hL

/-- **[obstruction, NoFifthDoor]** Discharged classical overshoot quantifier for honest mechanisms:
past the SOTA threshold, every classical mechanism that respects its proven scale (`√q` for completion,
`C·n^{1−δ}` for moment/EVT) overshoots BGK. This is the theorem replacing the abstract
`hclassicalOvershoots` postulate on the physically meaningful subclass. -/
theorem noFifthDoor_ceilingRespecting_classical_overshoots_export
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, N₀ ≤ n → n * L ≤ q →
      ∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m.door.isClassical → m.RespectsProvenScale q C δ n →
          m.OvershootsBGK n L :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.ceilingRespecting_classical_overshoots
    hLnn hC hδ

/-- **[capstone, NoFifthDoor]** Discharged no-fifth-door capstone: past the SOTA threshold, if
classical mechanisms are real instances of their doors (they respect the proven completion/moment/EVT
scales), then any prize-scale certificate is forced through door (iv). The classical overshoot input is
proved from the concrete ceilings, not assumed. -/
theorem noFifthDoor_forces_doorIV_ceilingRespecting_export
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hL : 1 < L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, max N₀ 1 ≤ n → n * L ≤ q →
      (∀ m' : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.RespectsProvenScale q C δ n) →
      ∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n →
          m.door = _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.forces_doorIV_ceilingRespecting
    hLnn hL hC hδ

/-- **[capstone/obstruction, NoFifthDoor]** Local contrapositive of the discharged classical side:
past the SOTA threshold, a classical mechanism that certifies the prize scale must violate its own
proven door-scale (`√q` for completion, `C·n^{1−δ}` for moment/EVT). This blocks the degenerate
`certScale` loophole without assuming every mechanism globally respects its ceiling. -/
theorem noFifthDoor_classical_prize_certificate_violates_provenScale_export
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hL : 1 < L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, max N₀ 1 ≤ n → n * L ≤ q →
      ∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m.door.isClassical →
        m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n →
        ¬ m.RespectsProvenScale q C δ n :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.classical_prize_certificate_violates_provenScale
    hLnn hL hC hδ

/-- **[capstone, NoFifthDoor]** Local no-fifth-door alternative: past the SOTA threshold, any
prize-scale certificate is either a genuine door-(iv) mechanism, or it violates the proven scale of
its own classical door. This is the discharged, single-mechanism form of the no-fifth-door capstone. -/
theorem noFifthDoor_prize_certificate_doorIV_or_violates_provenScale_export
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hL : 1 < L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, max N₀ 1 ≤ n → n * L ≤ q →
      ∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n →
          m.door = _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation ∨
            ¬ m.RespectsProvenScale q C δ n :=
  _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prize_certificate_doorIV_or_violates_provenScale
    hLnn hL hC hδ

/-! ## ShawGrandSynthesis — the composed Lane-2/Lane-3 headline. Scope: **capstone**.
These exports make permanent the newly landed synthesis module: the prize is exactly Shaw boundedness,
and any proof at the prize floor must pass through door (iv). Pure composition, no CORE bound. -/

/-- **[capstone, ShawGrandSynthesis]** Conjoined headline: `ShawOOneOn ↔ CorePrizeBoundOn` and,
at a proven-scale mechanism instance, a prize-floor certificate forces door (iv). -/
theorem shawGrand_prize_reduces_to_doorIV_export
    {ι : Type*} {q n M : ι → ℝ}
    (hscale : ∀ i : ι,
      0 < _root_.ProximityGap.Frontier.ShawValueCapstone.shawScale (q i) (n i))
    {m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism}
    {n₀ L₀ q₀ C δ : ℝ}
    (hn₀ : 0 < n₀) (hL₀ : 1 < L₀) (hq₀ : n₀ * L₀ ≤ q₀)
    (hsota : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n₀ L₀ ≤
      C * n₀ ^ (1 - δ))
    (hatScale : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorDischarged.AtProvenScale
      m n₀ q₀ C δ) :
    (_root_.ProximityGap.Frontier.ShawValueCapstone.ShawOOneOn q n M ↔
      _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M) ∧
      (m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n₀ →
        m.door = _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation) :=
  _root_.ArkLib.ProximityGap.Frontier.ShawGrandSynthesis.prize_reduces_to_doorIV
    hscale hn₀ hL₀ hq₀ hsota hatScale

/-- **[capstone, ShawGrandSynthesis]** Same synthesis with Shaw-scale positivity discharged from
`0 < n_i < q_i` on the family. -/
theorem shawGrand_prize_reduces_to_doorIV_of_pos_lt_export
    {ι : Type*} {q n M : ι → ℝ}
    (hn : ∀ i : ι, 0 < n i) (hnq : ∀ i : ι, n i < q i)
    {m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism}
    {n₀ L₀ q₀ C δ : ℝ}
    (hn₀ : 0 < n₀) (hL₀ : 1 < L₀) (hq₀ : n₀ * L₀ ≤ q₀)
    (hsota : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.bgkScale n₀ L₀ ≤
      C * n₀ ^ (1 - δ))
    (hatScale : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorDischarged.AtProvenScale
      m n₀ q₀ C δ) :
    (_root_.ProximityGap.Frontier.ShawValueCapstone.ShawOOneOn q n M ↔
      _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M) ∧
      (m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n₀ →
        m.door = _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation) :=
  _root_.ArkLib.ProximityGap.Frontier.ShawGrandSynthesis.prize_reduces_to_doorIV_of_pos_lt
    hn hnq hn₀ hL₀ hq₀ hsota hatScale

/-- **[capstone, ShawGrandSynthesis]** Eventual family headline: Shaw boundedness is exactly the
CORE prize bound, and past the SOTA threshold every proven-scale prize-floor certificate is door (iv). -/
theorem shawGrand_prize_reduces_to_doorIV_eventually_export
    {ι : Type*} {q n M : ι → ℝ}
    (hscale : ∀ i : ι,
      0 < _root_.ProximityGap.Frontier.ShawValueCapstone.shawScale (q i) (n i))
    {L q₀ C δ : ℝ} (hC : 0 < C) (hL : 1 < L) (hLnn : 0 ≤ L) (hδ : δ < 1 / 2) :
    (_root_.ProximityGap.Frontier.ShawValueCapstone.ShawOOneOn q n M ↔
      _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M) ∧
      ∃ N₀ : ℝ, ∀ n' : ℝ, N₀ ≤ n' → 2 ≤ n' → n' * L ≤ q₀ →
        ∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
          _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorDischarged.AtProvenScale m n' q₀ C δ →
          m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale n' →
            m.door = _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation :=
  _root_.ArkLib.ProximityGap.Frontier.ShawGrandSynthesis.prize_reduces_to_doorIV_eventually
    hscale hC hL hLnn hδ

/-! ## NoTighterBound — the #407/#444 "no tighter bound from any direction" capstone (Lane-2).
Scope: **capstone**. The negative structural theorem: any functional bounding the per-frequency core
`M(n) = max_{b≠0}‖η_b‖` must be simultaneously b-sensitive, deterministic-archimedean, and genuinely
`L∞`. The two machine-checkable failure faces — a b-symmetric (moment-determined) statistic CANNOT
determine the sup, and an only-`L²`/depth-`r`-moment method is floored at the trivial `√S` — are
bundled into one citation point. (The third property, deterministic-archimedean, is named in prose; it
is the absence of an ensemble/freeness the fixed subgroup lacks.) -/

/-- **[capstone, NoTighterBound]** A `b`-symmetric statistic cannot determine the sup: two explicit
real families on `Fin 4` with IDENTICAL first and second moments but a strictly larger coordinate in
one. So any functional determined by the (permutation-invariant) moment data is blind to the worst
`b`. Failure mode (1) of the 3-property necessary condition. -/
theorem noTighterBound_secondMoment_blind_export :
    ∃ (η η' : Fin 4 → ℝ) (b₀ : Fin 4),
      (∑ i, η i = ∑ i, η' i) ∧ (∑ i, (η i) ^ 2 = ∑ i, (η' i) ^ 2) ∧
      (∀ j, |η' j| < |η b₀|) :=
  _root_.ProximityGap.Frontier.NoTighterBoundCapstone.secondMoment_does_not_determine_sup

/-- **[capstone, NoTighterBound]** The packaged no-tighter-bound capstone: BOTH machine-checkable
faces in one conjunction — (1) a moment-determined `b`-symmetric statistic cannot see the worst `b`,
and (3) any only-`L²`/depth-`r`-moment method `g` is floored at `√S` (cannot reach
`√(n·log m) ≪ √S`). Every classical and fresh tool fails at least one. The structural reason no
tighter bound on `M` is reachable from the symmetric / `L²` directions. -/
theorem noTighterBound_from_symmetric_or_L2_export :
    (∃ (η η' : Fin 4 → ℝ) (b₀ : Fin 4),
        (∑ i, η i = ∑ i, η' i) ∧ (∑ i, (η i) ^ 2 = ∑ i, (η' i) ^ 2) ∧
        (∀ j, |η' j| < |η b₀|)) ∧
    (∀ {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι] {r : ℕ}, 1 ≤ r → ∀ (g : ℝ → ℝ),
        (∀ (η : ι → ℝ) (b : ι), |η b| ≤ g (∑ i, (η i) ^ (2 * r))) →
        ∀ {S : ℝ}, 0 ≤ S → Real.sqrt S ≤ g (S ^ r)) :=
  _root_.ProximityGap.Frontier.NoTighterBoundCapstone.noTighterBound_from_symmetric_or_L2

/-! ## ShawValue — the Lane-2 `prize ⟺ Sh(n)=O(1)` capstone (the citable normalization).
Scope: **capstone**. The prize inequality `M ≤ C·√(n·L)` is exactly a bound on the normalized
Shaw value `Sh(M) = M/√(n·L)`; the proven two-sided corridor `1/√(2L) ≤ Sh(M(μ_n)) ≤ √(n/L)` on
the REAL Gauss-period worst frequency brackets the open prize at multiplicative width `√n`. -/

/-- **[capstone, ShawValue]** The prize normalization equivalence: under a positive prize scale,
the raw prize-shaped bound `M ≤ C·√(n·L)` is *exactly* the statement that the normalized Shaw
value is at most `C`. This removes the arithmetic wrapper, so the prize reads as “bound the
normalized object by an absolute constant” (`Sh(n)=O(1)`). Pure normalization — no cancellation
estimate is hidden. -/
theorem prizeBound_iff_shawValue_le_export {M C n L : ℝ} (hs : 0 < prizeScale n L) :
    M ≤ C * prizeScale n L ↔ shawValue M n L ≤ C :=
  prizeBound_iff_shawValue_le hs

/-- **[capstone, ShawValue]** Strict prize normalization equivalence: under a positive prize scale,
a strict raw prize-shaped bound `M < C·√(nL)` is exactly the statement that the normalized Shaw
value is strictly below `C`. This is the strict-slack companion to the citable Lane-2 equivalence,
not a cancellation estimate. -/
theorem strictPrizeBound_iff_shawValue_lt_export {M C n L : ℝ}
    (hs : 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L) :
    M < C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L ↔
      _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue M n L < C :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictPrizeBound_iff_shawValue_lt hs

/-- **[capstone, ShawValue]** Uniform strict-family form of the Lane-2 reduction: with positive
pointwise prize scale, a strict raw prize bound by the same constant throughout a family is exactly
a strict Shaw-value bound by that constant throughout the family. Pure normalization bookkeeping. -/
theorem strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound_export
    {ι : Type*} {M n L : ι → ℝ} {C : ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i)) :
    _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound M n L C ↔
      _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictShawValueFamilyBound M n L C :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound hs

/-- **[capstone, ShawValue]** Existential strict-family form of the Lane-2 reduction: with positive
pointwise prize scale, existence of one absolute strict raw-prize constant is exactly existence of
one absolute strict Shaw-value constant. Pure normalization bookkeeping. -/
theorem exists_strictRawPrizeFamilyBound_iff_exists_strictShawValueFamilyBound_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i)) :
    (∃ C, _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound M n L C) ↔
      (∃ C, _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictShawValueFamilyBound M n L C) := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C,
      (_root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound
        hs).1 hC⟩
  · rintro ⟨C, hC⟩
    exact ⟨C,
      (_root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound
        hs).2 hC⟩

/-- **[capstone, ShawValue]** Wall-facing strict existential form: failure of every absolute strict
raw-prize constant is exactly failure of every absolute strict Shaw-value constant. Pure
normalization bookkeeping for strict-margin obstructions. -/
theorem not_exists_strictRawPrizeFamilyBound_iff_not_exists_strictShawValueFamilyBound_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i)) :
    ¬ (∃ C, _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound M n L C) ↔
      ¬ (∃ C, _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictShawValueFamilyBound M n L C) :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.not_exists_strictRawPrizeFamilyBound_iff_not_exists_strictShawValueFamilyBound hs

/-- **[capstone, ShawValue]** Nonnegative strict-family form of the Lane-2 reduction: with positive
pointwise prize scale, existence of one nonnegative absolute strict raw-prize constant is exactly
existence of one nonnegative absolute strict Shaw-value constant. Pure normalization bookkeeping. -/
theorem exists_nonneg_strictRawPrizeFamilyBound_iff_exists_nonneg_strictShawValueFamilyBound_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i)) :
    (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound M n L C) ↔
      (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictShawValueFamilyBound M n L C) :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.exists_nonneg_strictRawPrizeFamilyBound_iff_exists_nonneg_strictShawValueFamilyBound hs

/-- **[capstone, ShawValue]** Wall-facing nonnegative strict-family form: failure of every
nonnegative absolute strict raw-prize constant is exactly failure of every nonnegative absolute strict
Shaw-value constant. Pure normalization bookkeeping for strict-margin obstructions. -/
theorem not_exists_nonneg_strictRawPrizeFamilyBound_iff_not_exists_nonneg_strictShawValueFamilyBound_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i)) :
    ¬ (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictRawPrizeFamilyBound M n L C) ↔
      ¬ (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.strictShawValueFamilyBound M n L C) :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.not_exists_nonneg_strictRawPrizeFamilyBound_iff_not_exists_nonneg_strictShawValueFamilyBound hs

/-- **[capstone, ShawValue]** THE Lane-2 corridor. For the actual primitive-character Gauss-period
worst frequency `M(μ_n) = worstPeriod ψ G` in the thin prize regime `q ≥ 2n` (automatic at
`q = n^β`, `β > 1`), the normalized Shaw value is sandwiched
`1/√(2L) ≤ Sh(M(μ_n)) ≤ √(n/L)`, both endpoints in closed form. The lower endpoint is the
`n`-independent thin-regime Parseval floor `1/√(2L)`; the upper is the trivial-ceiling scale
`√(n/L)`. The open prize `Sh(M(μ_n)) = O(1)` lives strictly inside this proven corridor.

(All identifiers in the statement are FULLY QUALIFIED: restating them unqualified in this
heavily-`open`ed index context resolves `worstPeriod`/`shawValue` to a different overload, so we pin
the exact source declarations to inherit the clean proof term verbatim.) -/
theorem shawValue_worstPeriod_clean_corridor_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs F).Nonempty)
    (hn1 : 1 ≤ (G.card : ℝ))
    (hq2n : 2 * (G.card : ℝ) ≤ (Fintype.card F : ℝ)) {L : ℝ} (hL : 0 < L)
    (hs : 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (G.card : ℝ) L) :
    1 / Real.sqrt (2 * L) ≤
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue
          (_root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ G hne) (G.card : ℝ) L
      ∧ _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue
          (_root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ G hne) (G.card : ℝ) L
          ≤ Real.sqrt ((G.card : ℝ) / L) :=
  _root_.ProximityGap.Frontier.ConcreteShawValueThinFloor.shawValue_worstPeriod_clean_corridor
    hψ G hne hn1 hq2n hL hs

/-- **[capstone, ShawValue]** The corridor width is exactly `√n`: the ratio of the trivial-ceiling
endpoint to the Plancherel-floor endpoint equals `√n`. So the open prize is precisely the demand to
collapse this `√n`-wide normalized bracket to an absolute constant. -/
theorem shawValue_bracket_width_eq_sqrt_export {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    (n / prizeScale n L) / (Real.sqrt n / prizeScale n L) = Real.sqrt n :=
  bracket_width_eq_sqrt hn hL

/-- **[capstone, ShawValue]** Exact width of the clean thin-regime normalized corridor.  The citable
Lane-2 bracket `1/√(2L) ≤ Sh(M(μ_n)) ≤ √(n/L)` has endpoint ratio `√(2n)`, so normalization leaves a
`√n`-scale unconditional gap (up to the harmless `√2`).  This is pure arithmetic over the proven
corridor, not a CORE/cancellation estimate. -/
theorem shawValue_clean_corridor_width_eq_export {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    Real.sqrt (n / L) / (1 / Real.sqrt (2 * L)) = Real.sqrt (2 * n) :=
  _root_.ProximityGap.Frontier.ConcreteShawValueThinFloor.clean_corridor_width_eq hn hL

/-- **[capstone, ConcreteTrivialCeiling]** The sharp unconditional corridor on the real worst
period in the quadratic thin regime: `√(|G|-1) ≤ M(G) ≤ |G|`. This is the concrete lower/upper
bracket the Shaw normalization rests on; it is pure Parseval plus the triangle ceiling and makes no
cancellation claim. -/
theorem worstPeriod_sharp_bracket_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (_root_.ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs F).Nonempty)
    (hq1 : (1 : ℝ) < (Fintype.card F : ℝ))
    (hG1 : (1 : ℝ) < (G.card : ℝ))
    (hsq : (G.card : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    Real.sqrt ((G.card : ℝ) - 1) ≤
        _root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ G hne
      ∧ _root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ G hne
          ≤ (G.card : ℝ) :=
  _root_.ProximityGap.Frontier.ConcreteTrivialCeiling.worstPeriod_sharp_bracket
    hψ G hne hq1 hG1 hsq

/-- **[obstruction, ConcreteBGKCompletionCorridor]** In the thin regime `d² ≤ q`, the classical
`√q` completion ceiling is no better than the free triangle ceiling `d`: `d ≤ √q`. Thus door (ii)
is not just above the BGK target, it can be vacuous relative to `M≤d` on the real period. -/
theorem completion_vacuous_below_trivial_ceiling_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℝ} (hd : 0 ≤ d)
    (hsq : d ^ 2 ≤ (Fintype.card F : ℝ)) :
    d ≤ Real.sqrt (Fintype.card F) :=
  _root_.ProximityGap.Frontier.ConcreteBGKCompletionCorridor.card_le_completionCeiling_of_sq_le
    (F := F) hd hsq

/-- **[capstone, ConcreteShawCompletionCorridorFull]** The complete normalized completion corridor
on the actual torsion-subgroup object `μ_d`: `1/√(2L) ≤ Sh(M(μ_d)) ≤ √(q/(d·L))`. The upper endpoint
is exactly the SOTA completion baseline; collapsing it to `O(1)` is the open prize. -/
theorem shawValue_worstPeriod_torsion_full_corridor_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}
    (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hne : (_root_.ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs F).Nonempty)
    (hd1 : 1 ≤ (d : ℝ))
    (hq2d : 2 * (d : ℝ) ≤ (Fintype.card F : ℝ)) {L : ℝ} (hL : 0 < L)
    (hs : 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumWorstCase.torsion F d).card : ℝ) L) :
    1 / Real.sqrt (2 * L)
        ≤ _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue
          (_root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ
            (_root_.ArkLib.ProximityGap.SubgroupGaussSumWorstCase.torsion F d) hne)
          ((_root_.ArkLib.ProximityGap.SubgroupGaussSumWorstCase.torsion F d).card : ℝ) L
      ∧ _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue
          (_root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ
            (_root_.ArkLib.ProximityGap.SubgroupGaussSumWorstCase.torsion F d) hne)
          ((_root_.ArkLib.ProximityGap.SubgroupGaussSumWorstCase.torsion F d).card : ℝ) L
          ≤ Real.sqrt ((Fintype.card F : ℝ) / ((d : ℝ) * L)) :=
  _root_.ProximityGap.Frontier.ConcreteShawCompletionCorridorFull.shawValue_worstPeriod_torsion_full_corridor
    hd hd0 hψ hne hd1 hq2d hL hs

/-- **[capstone, ConcreteShawCompletionCorridorFull]** The sharp Parseval floor specialized to the
canonical prize object `μ_d`: in the quadratic thin regime, `√(d−1) ≤ M(μ_d)`. This records the true
lower endpoint on the real object; the missing work remains entirely on the upper/cancellation side. -/
theorem worstPeriod_torsion_sharp_floor_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {d : ℕ}
    (hd : d ∣ Fintype.card F - 1) (hd0 : 0 < d)
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (hne : (_root_.ArkLib.ProximityGap.I031DilationOrbitReduction.nonzeroFreqs F).Nonempty)
    (hq1 : (1 : ℝ) < (Fintype.card F : ℝ)) (hd1 : (1 : ℝ) < (d : ℝ))
    (hsq : (d : ℝ) ^ 2 ≤ (Fintype.card F : ℝ)) :
    Real.sqrt ((d : ℝ) - 1) ≤
      _root_.ProximityGap.Frontier.ConcreteMomentAssembly.worstPeriod ψ
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumWorstCase.torsion F d) hne :=
  _root_.ProximityGap.Frontier.ConcreteShawCompletionCorridorFull.worstPeriod_torsion_sharp_floor
    hd hd0 hψ hne hq1 hd1 hsq

/-! ## CoreReductionNecessity — exact `m*` gate for the BCHKS/Shaw reduction.
Scope: **capstone**. These exports make the Lane-2 necessity direction permanent: under the
monotone cascade and the P2/E3 identification, the BCHKS budget at a fold is not merely sufficient
for the binding depth to clear that fold, it is exactly equivalent. Thus the Johnson-side strict
gate `m* < k` is equivalent to the single named BCHKS/Shaw budget at `k-1`. This is reduction
bookkeeping only; the BCHKS budget itself remains the explicit open input. -/

/-- **[capstone, CoreReductionNecessity]** Failure of the named BCHKS budget at fold `M` pushes
the binding depth strictly past `M`. This is the necessity half of the `m*` gate. -/
theorem coreReduction_mStar_gt_of_BCHKS_fails_export
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hmono : ∀ {a b : ℕ}, a ≤ b → D n b ≤ D n a)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (M : ℕ)
    (hfail : ¬ ArkLib.ProximityGap.CoreReductionComplete.BCHKSBudget Sigma (smap n) (rmap n M)
      (budget n)) :
    M < ArkLib.ProximityGap.CoreReductionComplete.mStar D budget n hex :=
  ArkLib.ProximityGap.CoreReductionComplete.mStar_gt_of_BCHKS_fails
    D budget Sigma smap rmap n hex hmono hident M hfail

/-- **[capstone, CoreReductionNecessity]** Exact two-sided gate: under cascade monotonicity and
the P2/E3 identification, `m* ≤ M` iff the BCHKS/Shaw budget holds at the corresponding fold. -/
theorem coreReduction_mStar_le_iff_BCHKS_export
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hmono : ∀ {a b : ℕ}, a ≤ b → D n b ≤ D n a)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (M : ℕ) :
    ArkLib.ProximityGap.CoreReductionComplete.mStar D budget n hex ≤ M ↔
      ArkLib.ProximityGap.CoreReductionComplete.BCHKSBudget Sigma (smap n) (rmap n M)
        (budget n) :=
  ArkLib.ProximityGap.CoreReductionComplete.mStar_le_iff_BCHKS
    D budget Sigma smap rmap n hex hmono hident M

/-- **[capstone, CoreReductionNecessity]** Consumer-facing Johnson-fold form: for positive
`kNat`, clearing `m* < kNat` is equivalent to the BCHKS/Shaw budget at the previous fold `kNat-1`.
This pins the exact open input of the reduction, without proving that input. -/
theorem coreReduction_clears_johnson_iff_BCHKS_at_prev_fold_export
    (D : ℕ → ℕ → ℕ) (budget : ℕ → ℕ) (Sigma : ℕ → ℕ → ℕ)
    (smap : ℕ → ℕ) (rmap : ℕ → ℕ → ℕ) (n : ℕ)
    (hex : ∃ m, D n m ≤ budget n)
    (hmono : ∀ {a b : ℕ}, a ≤ b → D n b ≤ D n a)
    (hident : ∀ m, D n m = Sigma (smap n) (rmap n m)) (kNat : ℕ) (hk_pos : 1 ≤ kNat) :
    ArkLib.ProximityGap.CoreReductionComplete.mStar D budget n hex < kNat ↔
      ArkLib.ProximityGap.CoreReductionComplete.BCHKSBudget Sigma (smap n) (rmap n (kNat - 1))
        (budget n) :=
  ArkLib.ProximityGap.CoreReductionComplete.clears_johnson_iff_BCHKS_at_prev_fold
    D budget Sigma smap rmap n hex hmono hident kNat hk_pos

/-! ## Door-IV wraparound `Q ≥ 0` discharge. Scope: **obstruction**.

These exports preserve the algebraic narrowing of the char-`p` transfer route: the blind
wraparound-gap assumption `Q ≥ 0` follows from the sharper log-concavity input `wa·wc ≤ wb²`,
with an explicit `2·wb²` margin. The companion dominance hypothesis is refuted by the next section,
so this is a route-local constraint/reduction, not a CORE proof. -/

/-- **[obstruction, CharPWraparoundLogConcaveQ]** Under wraparound log-concavity `wa·wc≤wb²`
and `0≤s`, the wraparound transfer gap is at least `2·wb²`. This replaces a blind `Q≥0` input
by a sharper single inequality plus an explicit margin. -/
theorem charP_wrap_gap_ge_two_mul_sq_export {s wa wb wc : ℝ}
    (hs : 0 ≤ s) (hlc : wa * wc ≤ wb ^ 2) :
    2 * wb ^ 2 ≤ ArkLib.ProximityGap.CharPTransferDecomposition.gap s wa wb wc :=
  ArkLib.ProximityGap.CharPTransferDecomposition.gap_wrap_ge_two_mul_sq hs hlc

/-- **[obstruction, CharPWraparoundLogConcaveQ]** The open wraparound-control hypothesis `Q≥0`
of the char-`p` transfer assembly follows from `0≤s` and wraparound log-concavity. The remaining
dominance input is separate and is not discharged here. -/
theorem charP_wrap_gap_nonneg_of_logConcave_export {s wa wb wc : ℝ}
    (hs : 0 ≤ s) (hlc : wa * wc ≤ wb ^ 2) :
    0 ≤ ArkLib.ProximityGap.CharPTransferDecomposition.gap s wa wb wc :=
  ArkLib.ProximityGap.CharPTransferDecomposition.gap_wrap_nonneg_of_logConcave hs hlc

/-- **[obstruction, CharPWraparoundLogConcaveQ]** The char-`p` transfer assembly with the
`Q≥0` hypothesis replaced by wraparound log-concavity. This records the exact remaining obligation:
`0≤G₀+L` dominance plus `wa·wc≤wb²`, with dominance refuted at concrete prize-regime witnesses in
`CharPStepRatioFails`. -/
theorem charP_transfer_of_dominance_logConcave_export {s a₀ b₀ c₀ wa wb wc : ℝ}
    (hs : 0 ≤ s)
    (hdom : 0 ≤ ArkLib.ProximityGap.CharPTransferDecomposition.gap s a₀ b₀ c₀ +
      (2 * (s + 2) * b₀ * wb - s * (a₀ * wc + c₀ * wa)))
    (hlc : wa * wc ≤ wb ^ 2) :
    0 ≤ ArkLib.ProximityGap.CharPTransferDecomposition.gap
      s (a₀ + wa) (b₀ + wb) (c₀ + wc) :=
  ArkLib.ProximityGap.CharPTransferDecomposition.charP_transfer_of_dominance_logConcave
    hs hdom hlc

/-! ## Door-IV char-p transfer / ρ-antitone refutations. Scope: **obstruction**.

These exports make the newest door-(iv) Lane-3 no-go results permanent: char-`p` step-ratio
monotonicity is exactly the sign of the transfer gap, and explicit prize-regime witnesses
refute both the universal step-ratio route and the normalized `ρ`-antitone-and-bounded route. These are route
refutations only; they do not disprove CORE. -/

/-- **[obstruction, CharPStepRatioFails]** The abstract char-`p` step-ratio monotonicity predicate
`s·E_r·E_{r+2} ≤ (s+2)·E_{r+1}²` is exactly nonnegativity of the transfer gap functional used in
`_CharPTransferDecomposition`. This pins the step-ratio route to one sign condition. -/
theorem charP_stepRatioMonotoneAt_iff_gap_nonneg_export (s Er Er1 Er2 : ℝ) :
    ArkLib.ProximityGap.CharPStepRatioFails.StepRatioMonotoneAt s Er Er1 Er2 ↔
      0 ≤ ArkLib.ProximityGap.CharPTransferDecomposition.gap s Er Er1 Er2 :=
  ArkLib.ProximityGap.CharPStepRatioFails.stepRatioMonotoneAt_iff_gap_nonneg s Er Er1 Er2

/-- **[obstruction, CharPStepRatioFails]** Exact prize-regime witness (`n=32`, `p=786433`, `r=3`)
refuting char-`p` step-ratio monotonicity: `7·E₃·E₅ ≤ 9·E₄²` is false for
the exact period energies. -/
theorem charP_stepRatioMonotone_false_n32_export :
    ¬ ArkLib.ProximityGap.CharPStepRatioFails.StepRatioMonotoneAt
        7 446720 92179360 24850732032 :=
  ArkLib.ProximityGap.CharPStepRatioFails.not_stepRatioMonotoneAt_n32

/-- **[obstruction, CharPStepRatioFails]** No theorem using only positivity of
`s,E_r,E_{r+1},E_{r+2}` can prove universal char-`p` step-ratio monotonicity; the exact positive
`n=32` witness violates it. -/
theorem charP_no_universal_positive_stepRatioMonotone_export :
    ¬ (∀ s Er Er1 Er2 : ℝ,
      0 < s → 0 < Er → 0 < Er1 → 0 < Er2 →
        ArkLib.ProximityGap.CharPStepRatioFails.StepRatioMonotoneAt s Er Er1 Er2) :=
  ArkLib.ProximityGap.CharPStepRatioFails.not_forall_positive_stepRatioMonotoneAt

/-- **[obstruction, RhoAntitoneFails]** In normalized `ρ = S/((p−1)E)` coordinates, the `n=32`,
`p=786433` witness cannot satisfy both the antitone step `ρ(4)≤ρ(3)` and the order-5 ceiling
`ρ(5)≤1`. This is the probe-facing no-go interface for the `ρ`-antitone-and-bounded route. -/
theorem rho_normalized_antitone_and_ceiling_incompatible_export :
    ¬ (ArkLib.ProximityGap.RhoAntitoneFails.S4 /
          (ArkLib.ProximityGap.RhoAntitoneFails.pm1 * ArkLib.ProximityGap.RhoAntitoneFails.E4)
        ≤ ArkLib.ProximityGap.RhoAntitoneFails.S3 /
          (ArkLib.ProximityGap.RhoAntitoneFails.pm1 * ArkLib.ProximityGap.RhoAntitoneFails.E3) ∧
      ArkLib.ProximityGap.RhoAntitoneFails.S5 /
          (ArkLib.ProximityGap.RhoAntitoneFails.pm1 * ArkLib.ProximityGap.RhoAntitoneFails.E5)
        ≤ (1 : ℝ)) :=
  ArkLib.ProximityGap.RhoAntitoneFails.not_normalized_antitone_and_ceiling

/-- **[obstruction, RhoAntitoneFails]** The `ρ`-antitone route is not universally satisfiable:
there are positive exact witness values with the `r=3` cross-inequality reversed and the `r=5`
normalized ceiling broken. Hence `open_core_of_rho_antitone` remains a conditional sufficient route,
not a universal proof strategy. -/
theorem rho_antitone_route_not_universal_export :
    ∃ S3 S4 S5 E3 E4 E5 pm1 : ℝ,
      (0 < pm1 ∧ 0 < E3 ∧ 0 < E4 ∧ 0 < E5) ∧
      S3 * E4 < S4 * E3 ∧
      pm1 * E5 < S5 :=
  ArkLib.ProximityGap.RhoAntitoneFails.antitone_route_not_universal

/-! ## Door-IV value-shift histogram obstruction. Scope: **obstruction**.

These exports make the finite anti-concentration no-go reusable from the permanent index. The
value-shift mechanism is the one door-(iv) `L^∞` spreading idea that genuinely avoids the moment route,
but its own necessary condition is stronger than value-set symmetry: a nontrivial shift must preserve
the full fiber-cardinality histogram. In a prime field the realizable steps are all-or-nothing, so one
nonzero histogram mismatch collapses the entire mechanism to step `0` and hence to the trivial
`fiberCard val 0 ≤ #T` ceiling. Route refutation only; no CORE claim. -/

/-- **[obstruction, DoorIVValueShiftHistogram]** In a prime field, a single nonzero realizable
value-shift step forces the fiber histogram to be completely flat: every two residues have equal
fiber cardinality. Thus a useful value-shift free part demands perfect residue equidistribution,
not merely value-set invariance. -/
theorem valueShift_nontrivial_forces_flat_histogram_export
    {T : Type*} [Fintype T] [DecidableEq T] {p : ℕ} [Fact (Nat.Prime p)]
    (val : T → ZMod p) {s : ZMod p} (hs : s ≠ 0)
    (hreal : ∃ vs : ArkLib.ProximityGap.Frontier.NovelAntiConcentration.ValueShift val,
      vs.s = s) :
    ∀ a b : ZMod p,
      ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val a =
        ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val b :=
  ArkLib.ProximityGap.Frontier.DoorIVValueShiftHistogramObstruction.nontrivial_valueShift_forces_flat_histogram val hs hreal

/-- **[obstruction, DoorIVValueShiftHistogram]** Single-witness collapse: in a prime field, one
fiber-cardinality mismatch at one step rules out the all-steps case and forces every value-shift to
have trivial step `0`. -/
theorem valueShift_step_zero_of_one_histogram_witness_export
    {T : Type*} [Fintype T] [DecidableEq T] {p : ℕ} [Fact (Nat.Prime p)]
    (val : T → ZMod p) {s a : ZMod p}
    (hne : ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val a ≠
      ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val (a + s))
    (vs : ArkLib.ProximityGap.Frontier.NovelAntiConcentration.ValueShift val) :
    vs.s = 0 :=
  ArkLib.ProximityGap.Frontier.DoorIVValueShiftHistogramObstruction.valueShift_step_zero_of_one_histogram_witness val hne vs

/-- **[obstruction, DoorIVValueShiftHistogram]** With one histogram mismatch, the value-shift
spreading route gives only the trivial ceiling `fiberCard val 0 ≤ #T`; it cannot supply a useful
wraparound anti-concentration bound for the prize value map without a flat periodic histogram. -/
theorem valueShift_route_vacuous_of_one_histogram_witness_export
    {T : Type*} [Fintype T] [DecidableEq T] {p : ℕ} [Fact (Nat.Prime p)]
    (val : T → ZMod p) {s a : ZMod p}
    (hne : ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val a ≠
      ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val (a + s))
    (vs : ArkLib.ProximityGap.Frontier.NovelAntiConcentration.ValueShift val) :
    vs.s = 0 ∧
      ArkLib.ProximityGap.Frontier.NovelAntiConcentration.fiberCard val 0 ≤ Fintype.card T :=
  ArkLib.ProximityGap.Frontier.DoorIVValueShiftHistogramObstruction.valueShift_route_vacuous_of_one_histogram_witness val hne vs

/-! ## Door-IV wraparound Markov vacuity. Scope: **obstruction**.

These exports lock the average-to-sup no-go interface for the wraparound bad-prime route. The finite
Markov/union bound is valid, but when the threshold is at or below the mean its right side is at least
the whole prime set, so it cannot exclude even one heavy prime. Average wraparound control therefore
does not supply a supremum bound through the union route. -/

/-- **[obstruction, WraparoundMarkovVacuity]** Finite Markov inequality in multiplicative form:
for nonnegative weights, `T * #{j ∈ S : T ≤ W j} ≤ ∑ W j`. This is the exact union-bound interface
for the summed wraparound incidence. -/
theorem wraparound_markov_count_le_export {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (W : ι → ℝ) (T : ℝ) (hW : ∀ j ∈ S, 0 ≤ W j) :
    T * ((S.filter (fun j => T ≤ W j)).card : ℝ) ≤ ∑ j ∈ S, W j :=
  ArkLib.ProximityGap.WraparoundMarkovVacuity.markov_count_le S W T hW

/-- **[obstruction, WraparoundMarkovVacuity]** If `0 < T ≤ mean S W`, the Markov right-hand side
`(∑ W)/T` is at least `|S|`, so the union bound is vacuous at that threshold. -/
theorem wraparound_markov_bound_vacuous_below_mean_export {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (W : ι → ℝ) (T : ℝ)
    (hne : S.Nonempty) (hT : 0 < T)
    (hTmean : T ≤ ArkLib.ProximityGap.WraparoundMarkovVacuity.mean S W) :
    (S.card : ℝ) ≤ (∑ j ∈ S, W j) / T :=
  ArkLib.ProximityGap.WraparoundMarkovVacuity.markov_bound_vacuous_below_mean S W T hne hT hTmean

/-- **[obstruction, WraparoundMarkovVacuity]** Combined interface: below the average, the Markov
count bound still holds but its exclusion bound is already at least the full index-set size, so
average-control does not bound the supremum through this route. -/
theorem wraparound_average_control_does_not_bound_sup_export {ι : Type*} [DecidableEq ι]
    (S : Finset ι) (W : ι → ℝ) (T : ℝ)
    (hne : S.Nonempty) (hT : 0 < T) (hW : ∀ j ∈ S, 0 ≤ W j)
    (hTmean : T ≤ ArkLib.ProximityGap.WraparoundMarkovVacuity.mean S W) :
    T * ((S.filter (fun j => T ≤ W j)).card : ℝ) ≤ ∑ j ∈ S, W j
      ∧ (S.card : ℝ) ≤ (∑ j ∈ S, W j) / T :=
  ArkLib.ProximityGap.WraparoundMarkovVacuity.average_control_does_not_bound_sup
    S W T hne hT hW hTmean

/-! ## Door-IV index-factor overshoot. Scope: **obstruction**.

These exports make the naive-incidence scale loss citable from the permanent index: replacing the prize
scale `sqrt(n L)` by the incidence bridge scale `sqrt(n m L)` multiplies the normalized Shaw constant
by exactly `sqrt m`. A bounded normalized naive constant therefore bounds the index itself; an unbounded
index family cannot pass through this bridge without a genuinely new argument removing the factor. -/

/-- **[obstruction, DoorIVIndexFactorOvershoot]** The naive incidence bridge scale
`sqrt(n*m*L)` is exactly `sqrt(m)` times the prize scale `sqrt(n*L)`. -/
theorem doorIV_naiveIncidenceScale_eq_sqrt_mul_prizeScale_export {n m L : ℝ}
    (hm : 0 ≤ m) :
    ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale n m L =
      Real.sqrt m * ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale_eq_sqrt_mul_prizeScale hm

/-- **[obstruction, DoorIVIndexFactorOvershoot]** A raw bound at the naive incidence scale is
exactly a Shaw-value bound with the constant multiplied by `sqrt(m)`. -/
theorem doorIV_naiveIncidenceBound_iff_shawValue_le_scaled_export {M C n m L : ℝ}
    (hn : 0 < n) (hm : 0 ≤ m) (hL : 0 < L) :
    M ≤ C * ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale n m L ↔
      ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue M n L ≤ C * Real.sqrt m :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceBound_iff_shawValue_le_scaled hn hm hL

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Contrapositive-facing form: with fixed positive
raw constant `C`, any uniform cap `D` on `C*sqrt(m)` forces `m ≤ (D/C)^2`; hence the naive bridge
cannot give a bounded Shaw constant on an unbounded-index family. -/
theorem doorIV_index_le_sq_of_scaledConstant_le_export {C m D : ℝ}
    (hC : 0 < C) (hm : 0 ≤ m) (hbound : C * Real.sqrt m ≤ D) :
    m ≤ (D / C) ^ 2 :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.index_le_sq_of_scaledConstant_le
    hC hm hbound

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Exact pointwise cap criterion: for a positive raw
constant and nonnegative advertised cap, a naive normalized cap `C*sqrt(m) ≤ D` is equivalent to the
finite index constraint `m ≤ (D/C)^2`. The `sqrt(m)` loss is exactly an index bound. -/
theorem doorIV_scaledConstant_le_iff_index_le_sq_export {C m D : ℝ}
    (hC : 0 < C) (hm : 0 ≤ m) (hD : 0 ≤ D) :
    C * Real.sqrt m ≤ D ↔ m ≤ (D / C) ^ 2 :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.scaledConstant_le_iff_index_le_sq
    hC hm hD

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Single-witness family refutation: if some index
exceeds `(D/C)^2`, then no uniform cap `C*sqrt(m i) ≤ D` can hold across the family. This is the
probe-facing audit hook for unbounded-index failures of the naive bridge. -/
theorem doorIV_not_scaledConstantFamily_le_uniform_of_exists_index_gt_sq_export
    {ι : Type*} {C D : ℝ} {m : ι → ℝ}
    (hC : 0 < C) (hm : ∀ i, 0 ≤ m i)
    (hlarge : ∃ i, (D / C) ^ 2 < m i) :
    ¬ ∀ i, C * Real.sqrt (m i) ≤ D :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.not_scaledConstantFamily_le_uniform_of_exists_index_gt_sq
    hC hm hlarge

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Strict nontrivial-index scale loss: if the
hidden index satisfies `1 < m`, the naive incidence bridge scale is strictly larger than the prize
scale. The no-loss endpoint is exactly degenerate index one. -/
theorem doorIV_prizeScale_lt_naiveIncidenceScale_of_one_lt_m_export {n m L : ℝ}
    (hn : 0 < n) (hm : 1 < m) (hL : 0 < L) :
    ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L <
      ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale n m L :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.prizeScale_lt_naiveIncidenceScale_of_one_lt_m
    hn hm hL

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Strict normalized-constant loss: with positive raw
constant and genuinely nontrivial index, the normalized naive Shaw constant is strictly larger than the
desired constant. -/
theorem doorIV_constant_lt_scaledConstant_of_one_lt_m_export {C m : ℝ}
    (hC : 0 < C) (hm : 1 < m) :
    C < C * Real.sqrt m :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.constant_lt_scaled_constant_of_one_lt_m
    hC hm

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Contrapositive strict form: at a nontrivial index,
the inflated naive Shaw constant cannot remain below the desired constant. A route through
`sqrt(n*m*L)` must remove the index factor before claiming a constant Shaw bound. -/
theorem doorIV_not_scaledConstant_le_constant_of_one_lt_m_export {C m : ℝ}
    (hC : 0 < C) (hm : 1 < m) :
    ¬ C * Real.sqrt m ≤ C :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.not_scaled_constant_le_constant_of_one_lt_m
    hC hm

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Exact strict normalized-constant criterion:
the naive Shaw constant is strictly larger than the desired constant iff the hidden index is
strictly larger than one. -/
theorem doorIV_constant_lt_scaledConstant_iff_one_lt_m_export {C m : ℝ}
    (hC : 0 < C) (hm0 : 0 ≤ m) :
    C < C * Real.sqrt m ↔ 1 < m :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.constant_lt_scaled_constant_iff_one_lt_m
    hC hm0

/-- **[obstruction, DoorIVIndexFactorOvershoot]** Exact strict scale criterion: the naive incidence
scale strictly exceeds the prize scale iff the hidden index is strictly larger than one. -/
theorem doorIV_prizeScale_lt_naiveIncidenceScale_iff_one_lt_m_export {n m L : ℝ}
    (hn : 0 < n) (hm0 : 0 ≤ m) (hL : 0 < L) :
    ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L <
      ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.naiveIncidenceScale n m L ↔
        1 < m :=
  ArkLib.ProximityGap.Frontier.DoorIVIndexFactorOvershoot.prizeScale_lt_naiveIncidenceScale_iff_one_lt_m
    hn hm0 hL

/-! ## Door-IV order-blindness / selector obstruction. Scope: **obstruction**.

These exports make the Lane-1 `rho(b)` order-selector no-go permanent: a coset-invariant
coherence statistic is a quotient-level function on `b·μₙ`, not a function of the raw
multiplicative order of `b`. Any restricted selector can improve the worst coherence only
by missing an entire coset; merely filtering element-level/order buckets that still hit
every coset preserves the global bound problem. Route refutation only; no CORE claim. -/

/-- **[obstruction, DoorIVCoherenceOrderBlind]** If a statistic is invariant on left `H`-cosets,
then even same-coset elements with different multiplicative orders have the same statistic value.
Thus a `rho(b)`-style coset-level coherence cannot be controlled by multiplicative order alone. -/
theorem doorIV_cosetInvariant_blind_to_order_export {G : Type*} [Group G]
    {H : Subgroup G} {β : Type*} {f : G → β}
    (hf : _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.CosetInvariant H f)
    {a b : G} (hab : a * b⁻¹ ∈ H)
    (hord : orderOf a ≠ orderOf b) :
    f a = f b :=
  _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.cosetInvariant_blind_to_order
    hf hab hord

/-- **[obstruction, DoorIVCoherenceOrderBlind]** If a restricted frequency class `T` meets every
left `H`-coset, then an upper bound for a coset-invariant statistic on `T` is exactly the global
upper bound. Order buckets or element-level filters do not create a new anti-concentration lever
unless they omit whole cosets. -/
theorem doorIV_cosetHitting_selector_bound_iff_global_export {G : Type*} [Group G]
    {H : Subgroup G} {β : Type*} [LE β] {f : G → β} {C : β}
    (hf : _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.CosetInvariant H f) {T : Set G}
    (hT : ∀ b : G, ∃ t ∈ T, t * b⁻¹ ∈ H) :
    (∀ t ∈ T, f t ≤ C) ↔ ∀ b : G, f b ≤ C :=
  _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.bound_on_cosetHitting_set_iff_global
    (H := H) (f := f) (C := C) hf hT

/-- **[obstruction, DoorIVCoherenceOrderBlind]** Positive selector no-go: if a restricted class
claims a strict improvement below some global coset-invariant value, then it must miss an entire
left `H`-coset. Any genuine improvement is quotient-level, not multiplicative-order-level. -/
theorem doorIV_strict_selector_bound_misses_coset_export {G : Type*} [Group G]
    {H : Subgroup G} {β : Type*} [Preorder β] {f : G → β} {T : Set G} {C : β}
    (hf : _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.CosetInvariant H f)
    (hbound : ∀ t ∈ T, f t ≤ C) (hstrict : ∃ b : G, C < f b) :
    ∃ x : G, ∀ t ∈ T, t * x⁻¹ ∉ H :=
  _root_.ProximityGap.Frontier.DoorIVCoherenceOrderBlind.exists_coset_missed_of_strict_selector_bound
    (H := H) (f := f) hf hbound hstrict

/-! ## Door-IV worst-b Sidon/no energy-excess obstruction. Scope: **obstruction**.

These exports make the exact Sidon-floor constraint reusable from the permanent index. On a Sidon
worst-frequency representative set, the additive-energy excess above `2|G|²-|G|` is exactly zero,
and this remains true on every subset. Thus an additive-energy/sum-product lever must first prove
non-Sidon structure; when the probe-facing object is Sidon, the route has no positive energy budget
to grip. Route refutation only; no CORE claim. -/

/-- **[obstruction, DoorIVWorstBSidonNoEnergyExcess]** The additive-energy excess above the Sidon
floor vanishes exactly for Sidon sets. This pins the probe report `E(W)=2|W|²-|W|` to a kernel
checked no-excess statement. -/
theorem doorIV_additiveEnergyExcess_eq_zero_iff_sidon_export {F : Type*}
    [Field F] [Fintype F] [DecidableEq F] (G : Finset F) :
    ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergyExcess G = 0 ↔
      ArkLib.ProximityGap.SubgroupGaussSumMoment.IsSidonSet G :=
  ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergyExcess_eq_zero_iff_sidon G

/-- **[obstruction, DoorIVWorstBSidonNoEnergyExcess]** Sidon-ness is hereditary for this no-go:
every subset of a Sidon worst-b representative set has zero positive additive-energy budget above
the Sidon floor. Restricting to a subcollection cannot resurrect an additive-energy lever. -/
theorem doorIV_no_positive_additiveEnergyExcess_of_subset_sidon_export {F : Type*}
    [Field F] [Fintype F] [DecidableEq F] {G H : Finset F}
    (hG : ArkLib.ProximityGap.SubgroupGaussSumMoment.IsSidonSet G) (hHG : H ⊆ G) :
    ∀ B : ℕ, 0 < B →
      ¬ (B ≤ ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergyExcess H) :=
  ArkLib.ProximityGap.SubgroupGaussSumMoment.no_positive_additiveEnergyExcess_of_subset_sidon
    hG hHG

/-- **[obstruction, DoorIVWorstBSidonNoEnergyExcess]** Positive additive-energy excess is exactly
non-Sidon structure. Any door-(iv) certificate demanding positive energy excess is therefore a
certificate that the worst-b object is not Sidon, contrary to the pinned Sidon-floor probe regime. -/
theorem doorIV_positive_additiveEnergyExcess_iff_not_sidon_export {F : Type*}
    [Field F] [Fintype F] [DecidableEq F] (G : Finset F) :
    0 < ArkLib.ProximityGap.SubgroupGaussSumMoment.additiveEnergyExcess G ↔
      ¬ ArkLib.ProximityGap.SubgroupGaussSumMoment.IsSidonSet G :=
  ArkLib.ProximityGap.SubgroupGaussSumMoment.positive_additiveEnergyExcess_iff_not_sidon G

/-! ## Door-IV half-mass equivalence capstone. Scope: **capstone**.

These exports make the half-mass reduction citable: under the pointwise comparison `M ≤ H ≤ K*M`
with one family-wide `K`, the original uniform prize bound is equivalent to a uniform half-mass
bound and to bounded normalized half-mass Shaw value. This is normalization/reduction only; the
analytic half-mass cancellation estimate remains the open door-(iv) problem. -/

/-- **[capstone, DoorIVHalfMassEquivalence]** Uniform-family reduction: with one comparison
constant `K`, the existence of an absolute prize constant is equivalent to the existence of an
absolute half-mass constant. -/
theorem doorIV_prizeFamilyBound_iff_halfMassFamilyBound_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound M scale C) ↔
      (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassFamilyBound H scale C) :=
  ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.exists_prizeFamilyBound_iff_exists_halfMassFamilyBound
    hK hMH hHM

/-- **[capstone, DoorIVHalfMassEquivalence]** Mixed Shaw-value form: with positive scales, the
raw uniform prize Big-O bound is equivalent to bounded normalized half-mass Shaw value `H/scale`. -/
theorem doorIV_prizeFamilyBound_iff_normalizedHalfMassFamilyBound_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound M scale C) ↔
      (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalizedHalfMassFamilyBound H scale C) :=
  ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.exists_prizeFamilyBound_iff_exists_normalizedHalfMassFamilyBound
    hK hscale hMH hHM

/-- **[capstone, DoorIVHalfMassEquivalence]** Four-way packaging: the raw prize bound is equivalent
to simultaneous raw half-mass, normalized prize, and normalized half-mass formulations. -/
theorem doorIV_prizeFamilyBound_iff_all_halfMassShaw_forms_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound M scale C) ↔
      (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassFamilyBound H scale C) ∧
        (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalizedPrizeFamilyBound M scale C) ∧
          (∃ C, ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalizedHalfMassFamilyBound H scale C) :=
  ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound_iff_all_halfMassShaw_forms
    hK hscale hMH hHM

/-- **[capstone, DoorIVPrizeBddAbove]** Standard-library `BddAbove` and the conventional
nonnegative `O(1)` constant are exactly equivalent for normalized prize/Shaw ratios. -/
theorem doorIV_bddAbove_nonneg_normalizedPrize_export {ι : Type*} (M scale : ι → ℝ) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ∃ C, 0 ≤ C ∧
        ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalizedPrizeFamilyBound M scale C :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_iff_exists_nonneg_normalizedPrizeFamilyBound
    M scale

/-- **[capstone, DoorIVPrizeBddAbove]** Same nonnegative-constant `BddAbove` bridge for the
normalized half-mass Shaw target. -/
theorem doorIV_bddAbove_nonneg_normalizedHalfMass_export {ι : Type*} (H scale : ι → ℝ) :
    BddAbove (Set.range fun i => H i / scale i) ↔
      ∃ C, 0 ≤ C ∧
        ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.normalizedHalfMassFamilyBound H scale C :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_iff_exists_nonneg_normalizedHalfMassFamilyBound
    H scale

/-- **[capstone, DoorIVPrizeBddAbove]** Positive-scale `BddAbove` of normalized prize/Shaw ratios
is exactly the raw prize-family Big-O statement with a conventional nonnegative constant. -/
theorem doorIV_bddAbove_nonneg_rawPrize_export {ι : Type*}
    {M scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ∃ C, 0 ≤ C ∧
        ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound M scale C :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedPrize_iff_exists_nonneg_prizeFamilyBound
    hscale

/-- **[capstone, DoorIVPrizeBddAbove]** Positive-scale `BddAbove` of normalized half-mass/Shaw
ratios is exactly the raw half-mass-family Big-O statement with a conventional nonnegative constant. -/
theorem doorIV_bddAbove_nonneg_rawHalfMass_export {ι : Type*}
    {H scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    BddAbove (Set.range fun i => H i / scale i) ↔
      ∃ C, 0 ≤ C ∧
        ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassFamilyBound H scale C :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedHalfMass_iff_exists_nonneg_halfMassFamilyBound
    hscale

/-- **[capstone, DoorIVPrizeBddAbove]** Mixed sign-normalized face: bounded normalized prize/Shaw
ratios are exactly the existence of a conventional nonnegative raw half-mass family constant. -/
theorem doorIV_bddAbove_prize_iff_nonneg_rawHalfMass_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ∃ C, 0 ≤ C ∧
        ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassFamilyBound H scale C :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedPrize_iff_exists_nonneg_halfMassFamilyBound
    hK hscale hMH hHM

/-- **[capstone, DoorIVPrizeBddAbove]** Symmetric mixed sign-normalized face: bounded normalized
half-mass Shaw ratios are exactly the existence of a conventional nonnegative raw prize constant. -/
theorem doorIV_bddAbove_halfMass_iff_nonneg_rawPrize_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    BddAbove (Set.range fun i => H i / scale i) ↔
      ∃ C, 0 ≤ C ∧
        ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound M scale C :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedHalfMass_iff_exists_nonneg_prizeFamilyBound
    hK hscale hMH hHM

/-- **[capstone, DoorIVPrizeBddAbove]** Failure of a conventional nonnegative raw prize constant is
exactly explicit normalized-prize drift past every candidate constant. -/
theorem doorIV_not_nonneg_rawPrize_iff_prizeDrift_export {ι : Type*}
    {M scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    (¬ ∃ C, 0 ≤ C ∧
        ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.prizeFamilyBound M scale C) ↔
      ∀ C, ∃ i, C < M i / scale i :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_exists_nonneg_prizeFamilyBound_iff_forall_exists_lt_normalizedPrize
    hscale

/-- **[capstone, DoorIVPrizeBddAbove]** Failure of a conventional nonnegative raw half-mass constant
is exactly explicit normalized half-mass Shaw drift past every candidate constant. -/
theorem doorIV_not_nonneg_rawHalfMass_iff_halfMassDrift_export {ι : Type*}
    {H scale : ι → ℝ} (hscale : ∀ i, 0 < scale i) :
    (¬ ∃ C, 0 ≤ C ∧
        ArkLib.ProximityGap.Frontier.DoorIVHalfMassEquivalence.halfMassFamilyBound H scale C) ↔
      ∀ C, ∃ i, C < H i / scale i :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_exists_nonneg_halfMassFamilyBound_iff_forall_exists_lt_normalizedHalfMass
    hscale

/-- **[capstone, DoorIVPrizeBddAbove]** The door-(iv) wall is invariant under the half-mass
reduction: failure of `BddAbove` for normalized prize ratios is exactly failure for normalized
half-mass Shaw ratios. -/
theorem doorIV_not_bddAbove_prize_iff_not_bddAbove_halfMass_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (¬ BddAbove (Set.range fun i => M i / scale i)) ↔
      ¬ BddAbove (Set.range fun i => H i / scale i) :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_bddAbove_range_normalizedPrize_iff_not_bddAbove_range_normalizedHalfMass
    hK hscale hMH hHM

/-- **[capstone, DoorIVPrizeBddAbove]** The unbounded prize-side wall can be stated as explicit
half-mass Shaw drift: every candidate constant is exceeded by some normalized half-mass ratio. -/
theorem doorIV_not_bddAbove_prize_iff_halfMassDrift_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (¬ BddAbove (Set.range fun i => M i / scale i)) ↔
      ∀ C, ∃ i, C < H i / scale i :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_bddAbove_range_normalizedPrize_iff_forall_exists_lt_normalizedHalfMass
    hK hscale hMH hHM

/-- **[capstone, DoorIVPrizeBddAbove]** The symmetric wall face: unbounded normalized half-mass
Shaw ratios can be stated as explicit normalized-prize drift past every candidate constant. -/
theorem doorIV_not_bddAbove_halfMass_iff_prizeDrift_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (¬ BddAbove (Set.range fun i => H i / scale i)) ↔
      ∀ C, ∃ i, C < M i / scale i :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.not_bddAbove_range_normalizedHalfMass_iff_forall_exists_lt_normalizedPrize
    hK hscale hMH hHM

/-- **[capstone, DoorIVPrizeBddAbove]** Positive door-(iv) boundedness is exactly the negation of
half-mass Shaw drift, packaging `prize ⇔ ¬ wall` in the same standard-library API. -/
theorem doorIV_bddAbove_prize_iff_not_halfMassDrift_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    BddAbove (Set.range fun i => M i / scale i) ↔
      ¬ ∀ C, ∃ i, C < H i / scale i :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedPrize_iff_not_forall_exists_lt_normalizedHalfMass
    hK hscale hMH hHM

/-- **[capstone, DoorIVPrizeBddAbove]** Symmetric positive/wall face: bounded normalized half-mass
Shaw ratios are exactly the negation of normalized-prize drift. -/
theorem doorIV_bddAbove_halfMass_iff_not_prizeDrift_export {ι : Type*}
    {M H scale : ι → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hscale : ∀ i, 0 < scale i)
    (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    BddAbove (Set.range fun i => H i / scale i) ↔
      ¬ ∀ C, ∃ i, C < M i / scale i :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeBddAbove.bddAbove_range_normalizedHalfMass_iff_not_forall_exists_lt_normalizedPrize
    hK hscale hMH hHM

/-- **[capstone, ShawValueCapstone]** Standard-library boundedness form of the Shaw slogan:
`Sh(n)=O(1)` is exactly `BddAbove` of the dimensionless Shaw-value range. The nonnegative constant in
`ShawOOneOn` is obtained by replacing any upper bound `C` with `max C 0`. -/
theorem shawOOne_bddAbove_range_shawValue_export {ι : Type*} {q n M : ι → ℝ} :
    _root_.ProximityGap.Frontier.ShawValueCapstone.ShawOOneOn q n M ↔
      BddAbove (Set.range fun i : ι =>
        _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i)) :=
  _root_.ProximityGap.Frontier.ShawValueCapstone.shawOOneOn_iff_bddAbove_range_shawValue

/-- **[capstone, ShawValueCapstone]** Positive-scale prize bound as a bounded Shaw-value range:
`CorePrizeBoundOn` is equivalent to `BddAbove (range Sh)`. This is the standard-library `BddAbove`
face of the literal `prize ⇔ Sh(n)=O(1)` reduction, with no new analytic estimate. -/
theorem corePrize_bddAbove_range_shawValue_export {ι : Type*} {q n M : ι → ℝ}
    (hscale : ∀ i : ι, 0 < _root_.ProximityGap.Frontier.ShawValueCapstone.shawScale (q i) (n i)) :
    _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M ↔
      BddAbove (Set.range fun i : ι =>
        _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i)) :=
  _root_.ProximityGap.Frontier.ShawValueCapstone.corePrizeBoundOn_iff_bddAbove_range_shawValue hscale

/-- **[capstone, ShawValueCapstone]** Prize-regime version of the `BddAbove (range Sh)` capstone,
discharging scale positivity from `0 < n_i < q_i`. -/
theorem corePrize_bddAbove_range_shawValue_of_pos_lt_export {ι : Type*} {q n M : ι → ℝ}
    (hn : ∀ i : ι, 0 < n i) (hnq : ∀ i : ι, n i < q i) :
    _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M ↔
      BddAbove (Set.range fun i : ι =>
        _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i)) :=
  _root_.ProximityGap.Frontier.ShawValueCapstone.corePrizeBoundOn_iff_bddAbove_range_shawValue_of_pos_lt
    hn hnq

/-- **[capstone, ShawValueCapstone]** Negative `BddAbove` face of the Shaw slogan: failure of
`Sh(n)=O(1)` is exactly explicit drift of the Shaw values past every proposed constant. -/
theorem shawOOne_unbounded_shawValue_drift_export {ι : Type*} {q n M : ι → ℝ} :
    ¬ _root_.ProximityGap.Frontier.ShawValueCapstone.ShawOOneOn q n M ↔
      ∀ C : ℝ, ∃ i : ι,
        C < _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i) :=
  _root_.ProximityGap.Frontier.ShawValueCapstone.not_shawOOneOn_iff_forall_exists_lt_shawValue

/-- **[capstone, ShawValueCapstone]** Negative prize-reduction face: under positive Shaw scale,
failure of `CorePrizeBoundOn` is exactly explicit unbounded drift of the dimensionless Shaw values. -/
theorem corePrize_unbounded_shawValue_drift_export {ι : Type*} {q n M : ι → ℝ}
    (hscale : ∀ i : ι, 0 < _root_.ProximityGap.Frontier.ShawValueCapstone.shawScale (q i) (n i)) :
    ¬ _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M ↔
      ∀ C : ℝ, ∃ i : ι,
        C < _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i) :=
  _root_.ProximityGap.Frontier.ShawValueCapstone.not_corePrizeBoundOn_iff_forall_exists_lt_shawValue
    hscale

/-- **[capstone, ShawValueCapstone]** Prize-regime negative face of the Shaw drift criterion,
discharging positive scale from `0 < n_i < q_i`. -/
theorem corePrize_unbounded_shawValue_drift_of_pos_lt_export {ι : Type*} {q n M : ι → ℝ}
    (hn : ∀ i : ι, 0 < n i) (hnq : ∀ i : ι, n i < q i) :
    ¬ _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M ↔
      ∀ C : ℝ, ∃ i : ι,
        C < _root_.ProximityGap.Frontier.ShawValueCapstone.shawValue (q i) (n i) (M i) :=
  _root_.ProximityGap.Frontier.ShawValueCapstone.not_corePrizeBoundOn_iff_forall_exists_lt_shawValue_of_pos_lt
    hn hnq


/-- **[capstone, DoorIVPrizeShawTetrachotomySynthesis]** Single citable Lane-2 synthesis: the
nonnegative-constant prize-family reduction is exactly the nonnegative Shaw-value `O(1)` reduction,
and, under the classical-overshoot refutations, every prize-certifying mechanism is door (iv). -/
theorem doorIV_prize_iff_shawBounded_nonneg_and_doorIV_only_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (L i))
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    ((∃ C, 0 ≤ C ∧ ShawValueCapstone.rawPrizeFamilyBound M n L C) ↔
        (∃ C, 0 ≤ C ∧ ShawValueCapstone.shawValueFamilyBound M n L C)) ∧
      (∀ m : NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
        m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.prize_iff_shawBounded_nonneg_and_doorIV_only
    hs hnref hLref hclassicalOvershoots

/-- **[capstone, DoorIVPrizeShawTetrachotomySynthesis]** The remaining quantitative gap is exactly
`√L` between the prize floor and BGK scale, and the no-fifth-door theorem routes any certificate for
that gap to door (iv). -/
theorem doorIV_remaining_gap_is_sqrtL_factor_doorIV_only_export
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref) :
    (NoFifthDoorTetrachotomy.prizeScale nref < NoFifthDoorTetrachotomy.bgkScale nref Lref) ∧
      (NoFifthDoorTetrachotomy.bgkScale nref Lref =
        Real.sqrt Lref * NoFifthDoorTetrachotomy.prizeScale nref) ∧
      (∀ m : NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
        m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation) :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.remaining_gap_is_sqrtL_factor_doorIV_only
    hnref hLref hclassicalOvershoots

/-- **[capstone, DoorIVPrizeShawTetrachotomySynthesis]** Fully discharged positive-side package:
`prize ⇔ Sh(n)=O(1)` with nonnegative constants, plus an eventual floor-ratio formulation of the
pointwise certificate problem after all honest classical doors are excluded. -/
theorem doorIV_prize_iff_shawBounded_nonneg_and_floorPrizeRatio_export
    {ι : Type*} {Mfam n Lfam : ι → ℝ}
    (hs : ∀ i, 0 < ShawValueCapstone.prizeScale (n i) (Lfam i))
    {L q C δ : ℝ} (hLnn : 0 ≤ L) (hL : 1 < L) (hC : 0 < C) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ,
      ((∃ K, 0 ≤ K ∧ ShawValueCapstone.rawPrizeFamilyBound Mfam n Lfam K) ↔
          (∃ K, 0 ≤ K ∧ ShawValueCapstone.shawValueFamilyBound Mfam n Lfam K)) ∧
        (∀ nref : ℝ, max N₀ 1 ≤ nref → nref * L ≤ q →
          (∀ m' : NoFifthDoorTetrachotomy.Mechanism,
            m'.door.isClassical → m'.RespectsProvenScale q C δ nref) →
          ∀ M K : ℝ, NoFifthDoorTetrachotomy.prizeScale nref ≤ M →
            (1 ≤ DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio M nref) ∧
              (M ≤ K * NoFifthDoorTetrachotomy.prizeScale nref ↔
                DoorIVPrizeShawTetrachotomySynthesis.floorPrizeRatio M nref ≤ K) ∧
              (∀ m : NoFifthDoorTetrachotomy.Mechanism,
                m.certScale ≤ NoFifthDoorTetrachotomy.prizeScale nref →
                m.door = NoFifthDoorTetrachotomy.DoorType.newEvaluation)) :=
  ArkLib.ProximityGap.Frontier.DoorIVPrizeShawTetrachotomySynthesis.prize_iff_shawBounded_nonneg_and_floorPrizeRatio
    hs hLnn hL hC hδ

/-- **[capstone, ShawValueCapstone]** Elementary dominated-majorant transfer: a campaign
`CorePrizeBoundOn` theorem for a pointwise majorant gives the same raw prize-scale bound for every
smaller target.  This is pure monotonicity of the sup norm, with no new analytic estimate. -/
theorem doorIV_corePrize_of_dominated_majorant_export {ι : Type*} {q n M M' : ι → ℝ}
    (hle : ∀ i : ι, M' i ≤ M i)
    (h : ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M) :
    ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M' :=
  ProximityGap.Frontier.ShawValueCapstone.corePrizeBoundOn_of_le hle h

/-- **[capstone, ShawValueCapstone]** Non-Landau citation form of the dominated-majorant Lane-2
reduction: under positive scale, a campaign raw prize bound for a majorant implies `Sh(n)=O(1)` for
any dominated target. -/
theorem doorIV_shawOOne_of_coreMajorant_export {ι : Type*} {q n M M' : ι → ℝ}
    (hscale : ∀ i : ι, 0 < ProximityGap.Frontier.ShawValueCapstone.shawScale (q i) (n i))
    (hle : ∀ i : ι, M' i ≤ M i)
    (h : ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n M) :
    ProximityGap.Frontier.ShawValueCapstone.ShawOOneOn q n M' :=
  ProximityGap.Frontier.ShawValueCapstone.shawOOneOn_of_le_corePrizeBoundOn hscale hle h

/-- **[capstone, ShawValueLandauBridge]** A literal Landau prize bound for any nonnegative
pointwise majorant transfers directly to the Shaw-value `O(1)` statement for the dominated target.
This is the consumer-facing majorant composition rung for the Lane-2 `prize ⇔ Sh(n)=O(1)` reduction;
it is pure order/normalization bookkeeping and proves no new Gauss-period estimate. -/
theorem doorIV_landau_shaw_of_dominated_majorant_export {q n M M' : ℕ → ℝ}
    (hM'nn : ∀ i, 0 ≤ M' i)
    (hscale : ∀ i, 0 < ProximityGap.Frontier.ShawValueCapstone.shawScale (q i) (n i))
    (hle : ∀ i, M' i ≤ M i)
    (h : (ProximityGap.Frontier.ShawValueCapstone.supSeq M) =O[atTop]
      (ProximityGap.Frontier.ShawValueCapstone.scaleSeq q n)) :
    (ProximityGap.Frontier.ShawValueCapstone.shawSeq q n M') =O[atTop]
      (fun _ => (1 : ℝ)) :=
  ProximityGap.Frontier.ShawValueCapstone.shawSeq_isBigO_one_of_le_prizeBigO
    hM'nn hscale hle h

/-- **[capstone, ShawValueLandauBridge]** The same dominated-majorant transfer in the campaign's
`ShawOOneOn` predicate: a Landau prize-scale bound for a pointwise majorant gives a global uniform
`Sh(n)=O(1)` bound for every nonnegative dominated target. -/
theorem doorIV_shawOOne_of_dominated_majorant_export {q n M M' : ℕ → ℝ}
    (hM'nn : ∀ i, 0 ≤ M' i)
    (hscale : ∀ i, 0 < ProximityGap.Frontier.ShawValueCapstone.shawScale (q i) (n i))
    (hle : ∀ i, M' i ≤ M i)
    (h : (ProximityGap.Frontier.ShawValueCapstone.supSeq M) =O[atTop]
      (ProximityGap.Frontier.ShawValueCapstone.scaleSeq q n)) :
    ProximityGap.Frontier.ShawValueCapstone.ShawOOneOn q n M' :=
  ProximityGap.Frontier.ShawValueCapstone.shawOOneOn_of_le_prizeBigO hM'nn hscale hle h


/-! ## JacobiCocycleDispersion — the named door-(iv) missing theorem, permanently indexed.
Scope: **capstone**. The point of this section is discoverability: the #444 reduction does not
leave an anonymous anti-concentration obligation, but the explicit predicate
`JacobiCocycleDispersion M C n m`, exactly equivalent to a bounded Shaw value with `L = log m`.
These exports are direct aliases of the proven Lane-2 wrappers; they do NOT prove the missing
Jacobi dispersion theorem, and make no CORE/cancellation/completion/moment/capacity claim. -/

/-- **[obstruction, JacobiCocycleDispersion]** The degenerate trivial cocycle has full
concentration at a support frequency: if the written phase ratio satisfies `ζ^k = 1`, the length-`n`
fiber is exactly `n`. This is the baseline the missing Jacobi dispersion theorem must destroy. -/
theorem trivial_cocycle_full_concentration_export {n : ℕ} (hn : 0 < n) (ζ : ℂ) {k : ℕ}
    (hζk : ζ ^ k = 1) :
    (∑ g ∈ Finset.range n, (ζ ^ k) ^ g) = (n : ℂ) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.trivial_cocycle_full_concentration
    hn ζ hζk

/-- **[obstruction, JacobiCocycleDispersion]** Off a support frequency, a trivial cocycle has exact
geometric cancellation. The on/off pattern shows that the named Door-IV theorem is not a normalization
artifact: it must rule out collapse to this degenerate support. -/
theorem trivial_cocycle_offSupport_zero_export {n : ℕ} (ζ : ℂ) {k : ℕ}
    (hpow : (ζ ^ k) ^ n = 1) (hoff : ζ ^ k ≠ 1) :
    (∑ g ∈ Finset.range n, (ζ ^ k) ^ g) = 0 :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.trivial_cocycle_offSupport_zero
    ζ hpow hoff

/-- **[capstone, JacobiCocycleDispersion]** Pointwise form of the named door-(iv) target: the
Jacobi-cocycle dispersion predicate is exactly a Shaw-value bound with logarithmic thinness
parameter `L = log m`. -/
theorem jacobiCocycleDispersion_iff_shawValue_le_export {M C n m : ℝ}
    (hs : 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n (Real.log m)) :
    _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.JacobiCocycleDispersion M C n m ↔
      _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValue M n (Real.log m) ≤ C :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersion_iff_shawValue_le hs

/-- **[capstone, JacobiCocycleDispersion]** Uniform nonnegative-constant form under the standard
thin-instance positivity hypotheses `0 < n_i` and `0 < log m_i`: bounded Jacobi-cocycle dispersion
is equivalent to `Sh=O(1)`. -/
theorem exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound_pos_export
    {ι : Type*} {M n m : ι → ℝ} (hn : ∀ i, 0 < n i) (hlog : ∀ i, 0 < Real.log (m i)) :
    (∃ C, 0 ≤ C ∧
      _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersionFamilyBound M n m C) ↔
      (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n
          (fun i => Real.log (m i)) C) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound_of_pos
    hn hlog

/-- **[capstone, JacobiCocycleDispersion]** Wall-facing uniform form: under the standard positivity
hypotheses, failing to find any nonnegative Jacobi-dispersion constant is exactly failing to find any
nonnegative Shaw-value constant. -/
theorem not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_pos_export
    {ι : Type*} {M n m : ι → ℝ} (hn : ∀ i, 0 < n i) (hlog : ∀ i, 0 < Real.log (m i)) :
    ¬ (∃ C, 0 ≤ C ∧
      _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersionFamilyBound M n m C) ↔
      ¬ (∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n
          (fun i => Real.log (m i)) C) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_of_pos
    hn hlog

/-- **[capstone, JacobiCocycleDispersion]** Raw-sandwich invariance for the named Jacobi target:
if a downstream door-(iv) quantity `H` is uniformly between `M` and `K*M`, then boundedness of
Jacobi-cocycle dispersion transfers exactly up to constants. -/
theorem exists_jacobiCocycleDispersionFamilyBound_iff_rawSandwich_export
    {ι : Type*} {M H n m : ι → ℝ} {K : ℝ}
    (hK : 0 ≤ K) (hMH : ∀ i, M i ≤ H i) (hHM : ∀ i, H i ≤ K * M i) :
    (∃ C, _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersionFamilyBound M n m C) ↔
      (∃ C, _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.jacobiCocycleDispersionFamilyBound H n m C) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.exists_jacobiCocycleDispersionFamilyBound_iff_of_rawSandwich
    hK hMH hHM

/-! ## DoorIVObject — the single live door-(iv) open object is moment-trapped (Lane-1 close-out).
Scope: **capstone**. The worst-frequency coset-half coherence sup of the monomial sum (the sole live
open object of the tetrachotomy) is, in every measurement (n=16..128, multiple structured primes),
moment-trapped: bounded below by the iid-unit-phase (extreme-value) surrogate floor `iidSup`, with the
gap above it bounded by the additive-energy (moment) excess `Δ`. Equivalently the object sup is pinned
to the corridor `[iidSup, iidSup + Δ]`. No non-moment, non-extreme-value slack survives. CORE stays
open; no cancellation/anti-concentration/capacity claim. (#444, probes
`probe_dooriv_jacobi_cocycle_dispersion_magnitude.py`, `probe_dooriv_cocycle_excess_structure.py`.) -/

/-- **[capstone, DoorIVObject]** The door-(iv) object sup is pinned to the moment-corridor: under the
no-edge floor (`iidSup ≤ realSup`) and the excess-is-moment bound (`realSup − iidSup ≤ Δ`), the real
sup satisfies `iidSup ≤ realSup ≤ iidSup + Δ`. -/
theorem doorIV_object_moment_corridor_export {iidSup realSup Δ : ℝ}
    (hEdge : _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.SurrogateLeReal
      iidSup realSup)
    (hExcess : _root_.ArkLib.ProximityGap.Frontier.DoorIVObjectMomentCorridor.gap iidSup realSup ≤ Δ) :
    iidSup ≤ realSup ∧ realSup ≤ iidSup + Δ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVObjectMomentCorridor.realSup_in_moment_corridor
    hEdge hExcess

/-- **[capstone, DoorIVObject]** The grand three-pillar statement of the #444 structural result: from
the standard thin-instance positivity, the proven classical-overshoot refutations, and the two measured
facts about the door-(iv) object, ALL THREE pillars hold simultaneously — (1) the prize ⇔ `Sh=O(1)`
reduction, (2) the door-(iv)-only mechanism exclusion, and (3) the object moment-corridor
`[iidSup, iidSup + Δ]`. The single citable statement: the prize is a bounded Shaw value, deliverable
only through door (iv), whose open object is moment-trapped. CORE stays open. -/
theorem prize_iff_shawBounded_doorIV_only_and_object_moment_trapped_export
    {ι : Type*} {M n L : ι → ℝ}
    (hs : ∀ i, 0 < _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale (n i) (L i))
    {nref Lref : ℝ} (hnref : 0 < nref) (hLref : 1 < Lref)
    (hclassicalOvershoots :
      ∀ m' : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m'.door.isClassical → m'.OvershootsBGK nref Lref)
    {iidSup realSup Δ : ℝ}
    (hEdge : _root_.ArkLib.ProximityGap.Frontier.DoorIVCocycleNoRandomEdge.SurrogateLeReal
      iidSup realSup)
    (hExcess :
      _root_.ArkLib.ProximityGap.Frontier.DoorIVObjectMomentCorridor.gap iidSup realSup ≤ Δ) :
    ((∃ C, 0 ≤ C ∧
        _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.rawPrizeFamilyBound M n L C) ↔
        (∃ C, 0 ≤ C ∧
          _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.shawValueFamilyBound M n L C)) ∧
      (∀ m : _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.Mechanism,
        m.certScale ≤ _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.prizeScale nref →
        m.door =
          _root_.ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy.DoorType.newEvaluation) ∧
      (iidSup ≤ realSup ∧ realSup ≤ iidSup + Δ) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVPrizeObjectGrandCapstone.prize_iff_shawBounded_doorIV_only_and_object_moment_trapped
    hs hnref hLref hclassicalOvershoots hEdge hExcess

/-! ## DoorIVSignedDeepSumAbsLeak — the absolute-value leak made permanent.
Scope: **obstruction / positive localization**. The signed deep period-power probe found the
thinness-essential signal in `Σ η_b^r`, while all moment / energy packages pass through
`Σ |η_b|^r` and discard cancellation. These permanent exports expose the kernel-checked
triangle-inequality leak and its monotone transfer direction. They do NOT prove the open
uniform signed deep-cancellation bound, and make no CORE/cancellation/completion/capacity claim. -/

/-- **[obstruction, DoorIVSignedDeepSumAbsLeak]** Absolute-value / moment packaging can
only upper-bound the signed deep sum through the triangle-inequality leak:
`|Σ η_b^r| ≤ Σ |η_b|^r`. The gap is exactly the signed cancellation thrown away by
moment methods. -/
theorem doorIV_abs_signed_le_abs_moment_export {ι : Type*}
    (s : Finset ι) (η : ι → ℝ) (r : ℕ) :
    |∑ b ∈ s, (η b) ^ r| ≤ ∑ b ∈ s, |η b| ^ r := by
  classical
  exact _root_.ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak.abs_signed_le_abs_moment
    s η r

/-- **[obstruction, DoorIVSignedDeepSumAbsLeak]** The leak gap is nonnegative:
absolute moments minus the signed deep sum magnitude are a real discarded-cancellation
budget, never a saving. -/
theorem doorIV_leak_nonneg_export {ι : Type*}
    (s : Finset ι) (η : ι → ℝ) (r : ℕ) :
    0 ≤ (∑ b ∈ s, |η b| ^ r) - |∑ b ∈ s, (η b) ^ r| := by
  classical
  exact _root_.ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak.leak_nonneg s η r

/-- **[obstruction, DoorIVSignedDeepSumAbsLeak]** Any absolute-moment bound transfers
only one way, to a bound on the signed sum. The converse is false (kernelized in the
source file), so a signed deep-cancellation certificate cannot be recovered from an
absolute-value certificate. -/
theorem doorIV_abs_moment_bound_transfers_export {ι : Type*}
    (s : Finset ι) (η : ι → ℝ) (r : ℕ) {B : ℝ}
    (hB : ∑ b ∈ s, |η b| ^ r ≤ B) :
    |∑ b ∈ s, (η b) ^ r| ≤ B := by
  classical
  exact _root_.ProximityGap.Frontier.DoorIVSignedDeepSumAbsLeak.abs_moment_bound_transfers
    s η r hB


/-! ## JacobiCocycleTrivialOvershoot — the trivial baseline fails the thin prize target.
Scope: **obstruction**. The trivial cocycle's full `n`-spike is not a dispersion witness in the
prize regime `n > C² log m`; it overshoots the target `C√(n log m)` by a positive amount.
These exports pin the gap the genuine Jacobi cocycle must close, without proving it closes it. -/

/-- **[obstruction, JacobiCocycleTrivialOvershoot]** In the thin prize regime
`C² log m < n`, the trivial-cocycle baseline `M = n` fails the named Jacobi dispersion predicate.
This is the kernel-checked version of "the genuine cocycle must break the full `n`-spike." -/
theorem trivial_cocycle_overshoots_thin_export {C n logm : ℝ}
    (hn : 0 ≤ n) (hC : 0 ≤ C) (hlogm : 0 ≤ logm) (hthin : C ^ 2 * logm < n) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleDispersion.JacobiCocycleDispersion
      n C n (Real.exp logm) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleTrivialOvershoot.trivial_cocycle_overshoots_thin
    hn hC hlogm hthin

/-- **[obstruction, JacobiCocycleTrivialOvershoot]** In the same thin regime, the additive
overshoot gap `n - C√(n log m)` of the trivial spike is strictly positive. The open Door-IV
work is exactly to make the genuine cocycle disperse enough to remove this gap. -/
theorem trivial_overshoot_gap_pos_export {C n logm : ℝ}
    (hn : 0 ≤ n) (hC : 0 ≤ C) (hlogm : 0 ≤ logm) (hthin : C ^ 2 * logm < n) :
    0 < n - C * Real.sqrt (n * logm) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleTrivialOvershoot.trivial_overshoot_gap_pos
    hn hC hlogm hthin


/-! ## JacobiCocycleAllDefectCSVacuous — Cauchy--Schwarz has zero floor at full defect.
Scope: **obstruction**. The k-defect deficit floor degenerates exactly in the adversarial
all-defect regime `k = M`: its lower bound is `0`, leaving only the trivial ceiling. This locks
Shaw's Lever-B / L²-budget refutation as a permanent indexed constraint lemma. -/

/-- **[obstruction, JacobiCocycleAllDefectCSVacuous]** In the all-defect regime, the
Cauchy--Schwarz k-defect floor is exactly zero and the only remaining consequence is the
trivial ceiling on the phase sum. Thus the metric L²-budget route cannot certify prize-scale
cancellation at `k = M`. -/
theorem allDefect_cs_floor_vacuous_export (M : ℕ) (hM : 1 ≤ M) (w : Fin M → ℂ)
    (hunit : ∀ i, ‖w i‖ = 1) :
    ((M : ℝ) - (Finset.univ : Finset (Fin M)).card)
        * (∑ i ∈ (Finset.univ : Finset (Fin M)), (1 - (w i).re)) / (M : ℝ) = 0
      ∧ ‖_root_.ProximityGap.Frontier.DyadicJacobiCocycleNonContraction.phaseSum
            (_root_.ArkLib.ProximityGap.Frontier.JacobiCocycleKDefectQuantDeficit.kDefectFamily
              (Finset.univ : Finset (Fin M)) w)‖ ≤ (M : ℝ) :=
  _root_.ArkLib.ProximityGap.Frontier.JacobiCocycleAllDefectCSVacuous.allDefect_cs_floor_vacuous
    M hM w hunit


/-! ## GaussSumEnergyStep / DilationMultEnergyStep — the exact deep-step assault.
Scope: **capstone / obstruction**. These exports permanently index the focused Door-IV
Paley-kernel assault at the exact increment/off-diagonal level. The K=1 increment closes
unconditionally; the all-K step is reduced to the named tilted-increment input; and the
dilation split isolates the remaining BGK wall as off-diagonal/depth-`2K` cancellation.
No CORE bound is claimed. -/

/-- **[capstone, GaussSumEnergyStep]** The `K = 1` tilted-energy increment is strictly below
`2n` for every rational parameter pair `4 ≤ n < p`. This is the one unconditional closed-form
multiplicative-subgroup rung of the Paley/BGK deep step. -/
theorem gaussEnergyStep_incrementOne_lt_two_n_export
    (n p : ℚ) (hn : 4 ≤ n) (hpn : n < p) :
    (3 * p * (n - 1) - n ^ 3) / (p - n) - n * (p - n) / (p - 1) < 2 * n :=
  _root_.Issue444.GaussSumEnergyStep.incrementOne_lt_two_n n p hn hpn

/-- **[capstone, GaussSumEnergyStep]** The exact telescope reduction: if every tilted increment
is at most `2n`, then every deep-step ratio satisfies `r K ≤ (2K+1)n`. The hypothesis for
`K ≥ 2` is exactly the open tilted-variance/BGK input; this export records the reduction only. -/
theorem gaussEnergyStep_step_of_increments_le_export
    (n : ℚ) (r : ℕ → ℚ) (hr0 : r 0 ≤ n)
    (hincr : ∀ K, r (K + 1) - r K ≤ 2 * n) :
    ∀ K, r K ≤ (2 * (K : ℚ) + 1) * n :=
  _root_.Issue444.GaussSumEnergyStep.step_of_increments_le n r hr0 hincr

/-- **[capstone, DilationMultEnergyStep]** The exact diagonal split turns the deep step
`A_{K+1} ≤ (2K+1)nA_K` into the off-diagonal inequality `OFF ≤ 2KnA_K`. This is the
load-bearing algebraic reduction supplied by multiplicative dilation invariance. -/
theorem dilationEnergy_step_iff_offdiagonal_export
    (Akp1 Ak off : ℚ) (n K : ℚ)
    (hsplit : Akp1 = n * Ak + off) :
    (Akp1 ≤ (2 * K + 1) * n * Ak) ↔ (off ≤ 2 * K * n * Ak) :=
  _root_.Issue444.DilationMultEnergyStep.step_iff_offdiagonal Akp1 Ak off n K hsplit

/-- **[obstruction, DilationMultEnergyStep]** The Cauchy--Schwarz route from the off-diagonal
piece proves the deep step only after assuming the depth-`2K` energy/Wick input
`Em·Ephi ≤ (2K n A_K)^2`. Thus the dilation lever reduces to, but does not discharge, the
BGK wall. -/
theorem dilationEnergy_deep_step_of_depth2K_energy_export
    (Akp1 Ak off Em Ephi : ℚ) (n K : ℚ)
    (hsplit : Akp1 = n * Ak + off)
    (hoff_nonneg : 0 ≤ off)
    (hCS : off ^ 2 ≤ Em * Ephi)
    (htarget_nonneg : 0 ≤ 2 * K * n * Ak)
    (hdepth : Em * Ephi ≤ (2 * K * n * Ak) ^ 2) :
    Akp1 ≤ (2 * K + 1) * n * Ak :=
  _root_.Issue444.DilationMultEnergyStep.deep_step_of_depth2K_energy
    Akp1 Ak off Em Ephi n K hsplit hoff_nonneg hCS htarget_nonneg hdepth


/-- **[obstruction, DilationMultEnergyStep]** Probe-facing contrapositive of the diagonal split:
if the off-diagonal piece exceeds `2K n A_K`, the deep step itself is false. -/
theorem dilationEnergy_not_deep_step_of_offdiagonal_gt_export
    (Akp1 Ak off : ℚ) (n K : ℚ)
    (hsplit : Akp1 = n * Ak + off)
    (hoff_gt : 2 * K * n * Ak < off) :
    ¬ Akp1 ≤ (2 * K + 1) * n * Ak :=
  _root_.Issue444.DilationMultEnergyStep.not_deep_step_of_offdiagonal_gt
    Akp1 Ak off n K hsplit hoff_gt

/-- **[obstruction, DilationMultEnergyStep]** If Cauchy--Schwarz certifies
`OFF² ≤ Em·Ephi` while the target is already below `OFF`, then the depth-`2K` energy budget
`Em·Ephi ≤ target²` is impossible. This names the exact BGK-wall failure mode. -/
theorem dilationEnergy_not_depth2K_energy_of_cs_and_offdiagonal_gt_export
    (off Em Ephi target : ℚ)
    (hoff_nonneg : 0 ≤ off)
    (htarget_nonneg : 0 ≤ target)
    (hoff_gt : target < off)
    (hCS : off ^ 2 ≤ Em * Ephi) :
    ¬ Em * Ephi ≤ target ^ 2 :=
  _root_.Issue444.DilationMultEnergyStep.not_depth2K_energy_of_cs_and_offdiagonal_gt
    off Em Ephi target hoff_nonneg htarget_nonneg hoff_gt hCS


/-! ## DoorIVDecompositionInvariantCoherence — partition-invariant coherence saturation.
Scope: **obstruction**. These exports make the newest Lane-1 partition no-go permanent: if the
underlying terms already lie on a common nonnegative ray at the adversarial frequency, then every
partition of those terms has multi-piece coherence exactly `1`. Non-negation-stable / asymmetric /
finer partitions cannot create a coherence saving; any useful theorem must break term-level co-ray
alignment, i.e. the original CORE sup-norm problem. -/

/-- **[obstruction, DoorIVDecompositionInvariant]** Common-ray terms group to common-ray
block-sums under any partition map. -/
theorem doorIV_decomposition_block_sum_common_ray_export
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι κ : Type*} [DecidableEq κ]
    (t : Finset ι) (f : ι → E) (u : E) (c : ι → ℝ)
    (hf : ∀ i ∈ t, f i = c i • u) (hc : ∀ i ∈ t, 0 ≤ c i)
    (g : ι → κ) (k : κ) :
    (∑ i ∈ t.filter (fun i => g i = k), f i)
      = (∑ i ∈ t.filter (fun i => g i = k), c i) • u
    ∧ 0 ≤ (∑ i ∈ t.filter (fun i => g i = k), c i) :=
  _root_.ProximityGap.Frontier.DoorIVDecompositionInvariantCoherence.block_sum_common_ray
    t f u c hf hc g k

/-- **[obstruction, DoorIVDecompositionInvariant]** Headline partition-invariance theorem:
common-ray term alignment forces grouped multi-piece coherence to equal `1` for every partition. -/
theorem doorIV_decomposition_partition_invariant_coherence_export
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι κ : Type*} [DecidableEq κ]
    (t : Finset ι) (s : Finset κ) (f : ι → E) (u : E) (c : ι → ℝ)
    (hf : ∀ i ∈ t, f i = c i • u) (hc : ∀ i ∈ t, 0 ≤ c i)
    (g : ι → κ) (hcover : ∀ i ∈ t, g i ∈ s)
    (hmass : 0 < ∑ i ∈ t, c i) (hu : u ≠ 0) :
    _root_.ProximityGap.Frontier.DoorIVComplexRayCoherence.multiPieceNormCoherence s
      (fun k => ∑ i ∈ t.filter (fun i => g i = k), f i) = 1 :=
  _root_.ProximityGap.Frontier.DoorIVDecompositionInvariantCoherence.multiPieceNormCoherence_block_eq_one_of_common_ray t s f u c hf hc g hcover hmass hu

/-- **[obstruction, DoorIVDecompositionInvariant]** Constraint form: while the terms are
common-ray aligned, no partition can certify a strict coherence bound `≤ θ < 1`. -/
theorem doorIV_decomposition_no_partition_beats_one_export
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {ι κ : Type*} [DecidableEq κ]
    (t : Finset ι) (s : Finset κ) (f : ι → E) {θ : ℝ}
    (hθ : θ < 1)
    (hray : ∃ (u : E) (c : ι → ℝ),
      (∀ i ∈ t, f i = c i • u) ∧ (∀ i ∈ t, 0 ≤ c i) ∧
      0 < (∑ i ∈ t, c i) ∧ u ≠ 0)
    (g : ι → κ) (hcover : ∀ i ∈ t, g i ∈ s) :
    ¬ _root_.ProximityGap.Frontier.DoorIVComplexRayCoherence.multiPieceNormCoherence s
        (fun k => ∑ i ∈ t.filter (fun i => g i = k), f i) ≤ θ :=
  _root_.ProximityGap.Frontier.DoorIVDecompositionInvariantCoherence.no_partition_beats_one_of_common_ray_terms t s f hθ hray g hcover

/-- **[obstruction, DoorIVMultiPieceSignCoherence]** Real refined-piece coherence has the
closed-unit-interval ceiling `0 ≤ coherence ≤ 1` whenever its `L¹` denominator is positive. Therefore
all nontrivial door-(iv) content starts only at a strict subunit bound `≤ 1 - ε`; the signed-mass
exports below identify the exact minority-mass payment for that slack. -/
theorem doorIV_multiPiece_coherence_mem_Icc_export {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) (hpos : 0 < ∑ i ∈ s, |A i|) :
    _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.multiPieceCoherence s A ∈
      Set.Icc (0 : ℝ) 1 :=
  _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.multiPieceCoherence_mem_Icc s A hpos

/-- **[obstruction, DoorIVMultiPieceSignCoherence]** Exact saving identity for real refined
piece coherence. After compression to aggregate positive/negative masses, the slack below saturation
is precisely `2·minority/total`; refinement alone creates no hidden cancellation term. -/
theorem doorIV_multiPiece_exact_saving_export {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (htotal : 0 < posMass + negMass) :
    1 - _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.multiPieceCoherence s A =
      (2 * min posMass negMass) / (posMass + negMass) :=
  _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.one_sub_multiPieceCoherence_eq_two_mul_min_ratio
    s A hsum hden htotal

/-- **[obstruction, DoorIVMultiPieceSignCoherence]** Exact epsilon-budget equality interface for real
refined piece coherence. A certificate `coherence = 1 - ε` is equivalent to the exact
minority-sign payment `ε·total = 2·minority`. -/
theorem doorIV_multiPiece_eps_budget_eq_export {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass ε : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (htotal : 0 < posMass + negMass) :
    _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.multiPieceCoherence s A = 1 - ε ↔
      ε * (posMass + negMass) = 2 * min posMass negMass :=
  _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.multiPieceCoherence_eq_one_sub_iff_eps_mass_budget_eq
    s A hsum hden htotal

/-- **[obstruction, DoorIVMultiPieceSignCoherence]** Exact epsilon-budget interface for real refined
piece coherence. A certificate `coherence ≤ 1 - ε` is equivalent to the denominator-cleared minority
sign-mass obligation `ε·total ≤ 2·minority`; subdivision alone cannot create door-(iv) slack. -/
theorem doorIV_multiPiece_eps_budget_iff_export {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass ε : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (htotal : 0 < posMass + negMass) :
    _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.multiPieceCoherence s A ≤ 1 - ε ↔
      ε * (posMass + negMass) ≤ 2 * min posMass negMass :=
  _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.multiPieceCoherence_le_one_sub_iff_eps_mass_budget
    s A hsum hden htotal

/-- **[obstruction, DoorIVMultiPieceSignCoherence]** One-sided aggregate sign mass forbids any
positive epsilon saving for a real refined split. This is the consumer-facing contrapositive of the
exact budget: if one side has zero mass, no bound `coherence ≤ 1 - ε` with `ε > 0` can hold. -/
theorem doorIV_multiPiece_no_eps_slack_one_side_zero_export {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (A : ι → ℝ) {posMass negMass ε : ℝ}
    (hsum : (∑ i ∈ s, A i) = posMass - negMass)
    (hden : (∑ i ∈ s, |A i|) = posMass + negMass)
    (hposMass : 0 ≤ posMass) (hnegMass : 0 ≤ negMass)
    (htotal : 0 < posMass + negMass)
    (hzero : posMass = 0 ∨ negMass = 0) (hε : 0 < ε) :
    ¬ _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.multiPieceCoherence s A ≤ 1 - ε :=
  _root_.ProximityGap.Frontier.DoorIVMultiPieceSignCoherence.not_multiPieceCoherence_le_one_sub_eps_of_one_side_zero
    s A hsum hden hposMass hnegMass htotal hzero hε

/-- **[obstruction, DoorIVWindowConcentrationTrivial]** Single-window occupancy certificates
force the trivial cardinality budget. If the in/out window triangle RHS is at most `B`, then already
`|s| ≤ B`; a coarse small-ball count alone cannot beat the linear ceiling. -/
theorem doorIV_window_budget_forces_card_le_export {ι : Type*} [DecidableEq ι]
    {s W : Finset ι} (hW : W ⊆ s) {B : ℝ}
    (hbudget : (W.card : ℝ) + ((s \ W).card : ℝ) ≤ B) :
    (s.card : ℝ) ≤ B :=
  _root_.ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.window_budget_forces_card_le
    hW hbudget

/-- **[obstruction, DoorIVWindowConcentrationTrivial]** Two-window occupancy certificates force the
trivial cardinality budget. If two disjoint windows and the outside complement fit under `B`, then
already `|s| ≤ B`; any sublinear certificate must use phase cancellation, not occupancy bookkeeping. -/
theorem doorIV_twoWindow_budget_forces_card_le_export {ι : Type*} [DecidableEq ι]
    {s W₁ W₂ : Finset ι} (h₁ : W₁ ⊆ s) (h₂ : W₂ ⊆ s) (hdis : Disjoint W₁ W₂)
    {B : ℝ}
    (hbudget : (W₁.card : ℝ) + (W₂.card : ℝ) + ((s \ (W₁ ∪ W₂)).card : ℝ) ≤ B) :
    (s.card : ℝ) ≤ B :=
  _root_.ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.two_window_budget_forces_card_le
    h₁ h₂ hdis hbudget

/-- **[obstruction, DoorIVWindowConcentrationTrivial]** Finite multi-window occupancy certificates
force the trivial cardinality budget. If the disjoint-window triangle RHS is at most `B`, then
already `|s| ≤ B`; coarse small-ball bookkeeping alone cannot beat the linear ceiling. -/
theorem doorIV_multiWindow_budget_forces_card_le_export {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {Ω : Finset (Finset ι)}
    (hsub : ∀ W ∈ Ω, W ⊆ s)
    (hdis : (↑Ω : Set (Finset ι)).PairwiseDisjoint id)
    {B : ℝ}
    (hbudget : (∑ W ∈ Ω, (W.card : ℝ)) + ((s \ Ω.biUnion id).card : ℝ) ≤ B) :
    (s.card : ℝ) ≤ B :=
  _root_.ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.multi_window_budget_forces_card_le
    hsub hdis hbudget

/-- **[obstruction, DoorIVWindowConcentrationTrivial]** Strict finite multi-window small-ball
certificates are impossible without extra phase cancellation: the occupancy split RHS is exactly
`|s|`, so it cannot fit under any strict budget `B < |s|`. -/
theorem doorIV_no_multiWindow_split_rhs_le_strict_budget_export {ι : Type*} [DecidableEq ι]
    {s : Finset ι} {Ω : Finset (Finset ι)}
    (hsub : ∀ W ∈ Ω, W ⊆ s)
    (hdis : (↑Ω : Set (Finset ι)).PairwiseDisjoint id)
    {B : ℝ} (hB : B < (s.card : ℝ)) :
    ¬ (∑ W ∈ Ω, (W.card : ℝ)) + ((s \ Ω.biUnion id).card : ℝ) ≤ B :=
  _root_.ProximityGap.Frontier.DoorIVWindowConcentrationTrivial.no_multi_window_split_rhs_le_strict_budget
    hsub hdis hB

#print axioms doorIV_window_budget_forces_card_le_export
#print axioms doorIV_twoWindow_budget_forces_card_le_export
#print axioms doorIV_multiWindow_budget_forces_card_le_export
#print axioms doorIV_no_multiWindow_split_rhs_le_strict_budget_export

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** A uniform multiplicative control of the
sup-norm `target` by a candidate functional `F` evaluated at the target's worst frequency `bstar`
(with `F bstar > 0`) FORCES the constant `C ≥ target bstar / F bstar`.  When `F` is decoupled and
small at the worst frequency (probe `smallball_vs_energy`: argmax mismatch at every n), this forces a
large constant. -/
theorem doorIV_argmaxDecoupled_const_ge_ratio_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {bstar : ι}
    (hctrl : _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C)
    (hFpos : 0 < F bstar) :
    target bstar / F bstar ≤ C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.const_ge_ratio_at_argmax
    hctrl hFpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** A claimed absolute constant strictly below the
measured worst-frequency ratio `target bstar / F bstar` (with `F bstar > 0`) is impossible: there is
no such uniform control. -/
theorem doorIV_argmaxDecoupled_no_control_below_ratio_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {bstar : ι}
    (hFpos : 0 < F bstar) (hbelow : C < target bstar / F bstar) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.no_control_below_measured_ratio
    hFpos hbelow

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Exact ratio-envelope characterization:
when the candidate functional is strictly positive at every frequency, `target ≤ C·F` is equivalent to
bounding every pointwise ratio `target i / F i` by `C`. Thus absolute control is exactly a uniform
bound on the ratio envelope, not an argmax-only phenomenon. -/
theorem doorIV_argmaxDecoupled_uniformControl_iff_ratio_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} (hFpos : ∀ i, 0 < F i) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C
      ↔ ∀ i, target i / F i ≤ C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.uniformControl_iff_ratio_le
    hFpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Ratio-envelope no-go: with positive candidate
values, a single frequency whose witness ratio exceeds `C` refutes the claimed `C`-control, whether or
not that frequency is an argmax of the target or candidate. -/
theorem doorIV_argmaxDecoupled_exists_ratio_gt_no_control_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} (hFpos : ∀ i, 0 < F i)
    (hwit : ∃ i, C < target i / F i) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.not_uniformControl_of_exists_ratio_gt
    hFpos hwit


/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support monotonicity: control on a larger
measured support restricts to any smaller support. -/
theorem doorIV_argmaxDecoupled_uniformControlOn_of_subset_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s t : Finset ι} (hst : s ⊆ t)
    (hctrl : _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn
      t target F C) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn s target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.uniformControlOn_of_subset
    hst hctrl

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support obstruction propagates upward:
if `C`-control fails on a measured sub-support, it fails on every larger support containing it. -/
theorem doorIV_argmaxDecoupled_no_controlOn_superset_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s t : Finset ι} (hst : s ⊆ t)
    (hno : ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn
      s target F C) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn t target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.not_uniformControlOn_of_subset_not_control
    hst hno

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support exact ratio-envelope
characterization: on the enumerated probe support `s`, positive-candidate control is equivalent to
bounding every support ratio `target i / F i`. This is the finite-frequency form used by door-(iv)
small-ball/window probes, without silently claiming control outside the measured support. -/
theorem doorIV_argmaxDecoupled_uniformControlOn_iff_ratio_on_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s : Finset ι} (hFpos : ∀ i ∈ s, 0 < F i) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn s target F C
      ↔ ∀ i ∈ s, target i / F i ≤ C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.uniformControlOn_iff_ratio_le_on
    hFpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support ratio witness no-go: if one
measured frequency in the probe support has ratio above `C`, then there is no `C`-control even on that
finite support. -/
theorem doorIV_argmaxDecoupled_exists_ratio_gt_no_controlOn_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s : Finset ι} (hFpos : ∀ i ∈ s, 0 < F i)
    (hwit : ∃ i ∈ s, C < target i / F i) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn s target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.not_uniformControlOn_of_exists_ratio_gt_on
    hFpos hwit



/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support sign hygiene: if a measured
support control holds at one point where both target and candidate are positive, then the control
constant is itself positive. -/
theorem doorIV_argmaxDecoupled_controlOn_constant_pos_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s : Finset ι} {i : ι}
    (hctrl : _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn
      s target F C) (hi : i ∈ s) (hFpos : 0 < F i) (htpos : 0 < target i) :
    0 < C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.controlOn_constant_pos_of_positive_target_and_candidate
    hctrl hi hFpos htpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support point-ratio no-go: a single
measured support point with positive candidate value and ratio above `C` refutes `C`-control on that
support, without assuming the candidate is positive at every measured frequency. -/
theorem doorIV_argmaxDecoupled_point_ratio_gt_no_controlOn_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s : Finset ι} {i : ι} (hi : i ∈ s)
    (hFpos : 0 < F i) (hgt : C < target i / F i) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn s target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.not_uniformControlOn_of_point_ratio_gt_on
    hi hFpos hgt

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support family no-go: if the measured
support witness ratios are unbounded across a family, then every candidate absolute constant fails on
some measured support.  This is the finite-enumeration version of the unbounded-ratio obstruction. -/
theorem doorIV_argmaxDecoupled_no_absolute_constOn_export {ι N : Type*}
    {target F : N → ι → ℝ} {s : N → Finset ι} {bstar : N → ι}
    (hmem : ∀ n, bstar n ∈ s n)
    (hFpos : ∀ n, 0 < F n (bstar n))
    (hunbdd : ∀ C : ℝ, ∃ n, C < target n (bstar n) / F n (bstar n)) :
    ∀ C : ℝ, ∃ n, ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn
      (s n) (target n) (F n) C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.no_absolute_constantOn_of_unbounded_point_ratio
    hmem hFpos hunbdd

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support support constraint:
a positive `C`-control on the measured support `s` forces the candidate to be positive at every support
frequency where the target is positive. -/
theorem doorIV_argmaxDecoupled_candidate_pos_on_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s : Finset ι} {i : ι} (hCpos : 0 < C)
    (hctrl : _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn
      s target F C) (hi : i ∈ s) (htpos : 0 < target i) :
    0 < F i :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.candidate_pos_of_positive_controlOn_at_positive_target
    hCpos hctrl hi htpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support support-inclusion form:
a positive `C`-control on `s` forces `{i | i ∈ s ∧ target i > 0} ⊆ {i | F i > 0}`. -/
theorem doorIV_argmaxDecoupled_positive_support_on_subset_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s : Finset ι} (hCpos : 0 < C)
    (hctrl : _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn
      s target F C) :
    {i | i ∈ s ∧ 0 < target i} ⊆ {i | 0 < F i} :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.positiveTargetOn_subset_positiveCandidate_of_positive_controlOn
    hCpos hctrl

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support endpoint no-go: for any
nonnegative constant `C`, if a measured support frequency has positive target value but nonpositive
candidate value, then no `C`-control holds even on that finite support. -/
theorem doorIV_argmaxDecoupled_no_nonpos_candidate_controlOn_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s : Finset ι} {i : ι} (hC : 0 ≤ C) (hi : i ∈ s)
    (hFnonpos : F i ≤ 0) (htpos : 0 < target i) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn
      s target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.not_uniformControlOn_of_nonpos_candidate_at_positive_target
    hC hi hFnonpos htpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Finite-support zero endpoint: a nonnegative
constant cannot control a positive measured target point through a candidate that vanishes at that
support point. -/
theorem doorIV_argmaxDecoupled_no_zero_candidate_controlOn_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {s : Finset ι} {i : ι} (hC : 0 ≤ C) (hi : i ∈ s)
    (hFzero : F i = 0) (htpos : 0 < target i) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControlOn
      s target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.not_uniformControlOn_of_zero_candidate_at_positive_target
    hC hi hFzero htpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Nontrivial positive control forces the
constant positive: if `target ≤ C·F`, `F i > 0`, and `target i > 0` at even one frequency, then
`C > 0`. Thus positive-control support constraints require no extra sign assumption in the nonzero
positive-candidate regime. -/
theorem doorIV_argmaxDecoupled_control_constant_pos_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {i : ι}
    (hctrl : _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C)
    (hFpos : 0 < F i) (htpos : 0 < target i) :
    0 < C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.control_constant_pos_of_positive_target_and_candidate
    hctrl hFpos htpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Endpoint no-go: for any nonnegative absolute
constant `C`, if the candidate functional is nonpositive at a strictly-positive target peak, then no
uniform multiplicative control exists. This covers the zero/small-window endpoint of the measured
argmax-decoupling obstruction. -/
theorem doorIV_argmaxDecoupled_no_nonpos_candidate_control_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {bstar : ι} (hC : 0 ≤ C)
    (hFnonpos : F bstar ≤ 0) (htpos : 0 < target bstar) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.not_uniformControl_of_nonpos_candidate_at_positive_target
    hC hFnonpos htpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Zero endpoint no-go: a nonnegative constant
cannot control a positive target peak through a candidate functional that vanishes at that peak. -/
theorem doorIV_argmaxDecoupled_no_zero_candidate_control_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {bstar : ι} (hC : 0 ≤ C)
    (hFzero : F bstar = 0) (htpos : 0 < target bstar) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.not_uniformControl_of_zero_candidate_at_positive_target
    hC hFzero htpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Positive-control support constraint: if
`target ≤ C·F` with `C > 0`, then `F` must be positive at every positive target frequency. -/
theorem doorIV_argmaxDecoupled_candidate_pos_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} {i : ι} (hCpos : 0 < C)
    (hctrl : _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C)
    (htpos : 0 < target i) :
    0 < F i :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.candidate_pos_of_positive_control_at_positive_target
    hCpos hctrl htpos

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Set-level form: a positive multiplicative
control forces `{i | target i > 0} ⊆ {i | F i > 0}`.  A candidate whose positive support misses the
true target support is dead before any ratio estimate. -/
theorem doorIV_argmaxDecoupled_positive_support_subset_export {ι : Type*}
    {target F : ι → ℝ} {C : ℝ} (hCpos : 0 < C)
    (hctrl : _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl target F C) :
    {i | 0 < target i} ⊆ {i | 0 < F i} :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.positiveTarget_subset_positiveCandidate_of_positive_control
    hCpos hctrl

/-- **[obstruction, DoorIVArgmaxDecouplingNoControl]** Family no-go: if the per-`n` worst-frequency
witness ratio is UNBOUNDED above (decoupling: the target peaks where `F` is small), then NO single
absolute constant `C` uniformly controls every family member — for each `C` some member fails. -/
theorem doorIV_argmaxDecoupled_no_absolute_const_export {ι N : Type*}
    {target F : N → ι → ℝ} {bstar : N → ι}
    (hFpos : ∀ n, 0 < F n (bstar n))
    (hunbdd : ∀ C : ℝ, ∃ n, C < target n (bstar n) / F n (bstar n)) :
    ∀ C : ℝ, ∃ n, ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.UniformControl
      (target n) (F n) C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVArgmaxDecouplingNoControl.no_absolute_constant_of_unbounded_ratio
    hFpos hunbdd
/-- **[obstruction, DoorIVCollisionExcessPigeonhole]** Collision-free mod-`p` reduction is
exactly injectivity on the char-0 source classes. The zero-defect regime is therefore an elementary
no-merge certificate, not a phase-coherence estimate. -/
theorem doorIV_collision_defect_eq_zero_iff_injOn_export {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) :
    s.card - (s.image f).card = 0 ↔ Set.InjOn f s :=
  _root_.ProximityGap.Frontier.DoorIVCollisionExcessPigeonhole.defect_eq_zero_iff_injOn s f

/-- **[obstruction, DoorIVCollisionExcessPigeonhole]** Positive collision excess is exactly
non-injectivity of the reduction map on the source classes. Thus `Ψ₀ - Ψ_p > 0` certifies a merge
witness only; by itself it is not a cancellation or CORE upper-bound lever. -/
theorem doorIV_collision_defect_pos_iff_not_injOn_export {α β : Type*} [DecidableEq β]
    (s : Finset α) (f : α → β) :
    0 < s.card - (s.image f).card ↔ ¬ Set.InjOn f s :=
  _root_.ProximityGap.Frontier.DoorIVCollisionExcessPigeonhole.defect_pos_iff_not_injOn s f

/-- **[obstruction, door-(iv) Lane-1]** The STRICT worst-frequency peak is a SINGLE coset
(`Ncos(τ→0)=1`).  For an orbit-constant statistic `f` (the `μ_n`-invariant `|η_·|`) whose maximum
value `Mval` is attained at `b₀`, IF every strict maximizer lies in the orbit `G • b₀` (the measured
fact `Ncos(2%)=1`, n=16,32,64), then the exact argmax set is PRECISELY that single orbit.  The worst
frequency peak is isolated, not spread; any door-(iv) Lane-1 'spread the worst-b set' slack lives only
in the near-peak shell `τ>0` = a moment average = dead door (i). -/
theorem doorIV_strict_peak_single_coset_export
    {G : Type*} [Group G] {β : Type*} [MulAction G β] {f : β → ℝ}
    (hf : _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.OrbitConstant (G := G) f)
    {Mval : ℝ} {b₀ : β} (hb₀ : f b₀ = Mval)
    (hsingle : _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.argmaxSet f Mval
      ⊆ MulAction.orbit G b₀) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.argmaxSet f Mval
      = MulAction.orbit G b₀ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.argmaxSet_eq_single_orbit
    hf hb₀ hsingle

/-- **[obstruction, door-(iv) Lane-1]** Every strict maximizer is a coset translate of `b₀`:
`f b = Mval ↔ ∃ g, g • b₀ = b`.  No NEW arithmetic frequency outside the one peak coset is ever a
strict maximizer — the worst-b selector is coset-blind at the peak. -/
theorem doorIV_strict_maximizer_iff_translate_export
    {G : Type*} [Group G] {β : Type*} [MulAction G β] {f : β → ℝ}
    (hf : _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.OrbitConstant (G := G) f)
    {Mval : ℝ} {b₀ : β} (hb₀ : f b₀ = Mval)
    (hsingle : _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.argmaxSet f Mval
      ⊆ MulAction.orbit G b₀) (b : β) :
    f b = Mval ↔ ∃ g : G, g • b₀ = b :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.isMaximizer_iff_translate
    hf hb₀ hsingle b

/-- **[obstruction, door-(iv) Lane-1]** The literal `Ncos = 1` count: under the single-coset
hypothesis, the image of the exact argmax set under the orbit-quotient map `β → β /ₘ G` is the single
class `{⟦b₀⟧}` — the strict peak meets EXACTLY ONE orbit. -/
theorem doorIV_strict_peak_Ncos_eq_one_export
    {G : Type*} [Group G] {β : Type*} [MulAction G β] {f : β → ℝ}
    {Mval : ℝ} {b₀ : β} (hb₀ : f b₀ = Mval)
    (hsingle : _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.argmaxSet f Mval
      ⊆ MulAction.orbit G b₀) :
    (fun x => Quotient.mk (MulAction.orbitRel G β) x) ''
        _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.argmaxSet f Mval
      = {Quotient.mk (MulAction.orbitRel G β) b₀} :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVWorstCosetCountSingleton.orbitQuot_image_argmaxSet_eq_singleton
    hb₀ hsingle

end ArkLib.ProximityGap.Frontier.CampaignProvenIndex

/-! ## Cone axiom audit — every permanent export above is axiom-clean
(`[propext, Classical.choice, Quot.sound]`, no `sorryAx`). -/
namespace ArkLib.ProximityGap.Frontier.CampaignProvenIndex
#print axioms char0_stepRatio_antitone_iff_sharpNewton
#print axioms char0_W3anti_of_sharpNewton_export
#print axioms char0_kstability_cross_le_wick
#print axioms char0_prize_moment_bound_unconditional
#print axioms char0_prize_moment_bound_sq_unconditional
#print axioms char0_nonprincipalEnergyBound_discharged
#print axioms char0_eta_pow_le_unconditional
#print axioms gaussian_moment_telescope
#print axioms convexOrder_gaussian_iff_wick_export
#print axioms prize_of_matchedGaussian_stepLaw_export
#print axioms eta_pow_le_of_nonprincipalEnergyBound_export
#print axioms moment_problem_does_not_give_wick_bracket
#print axioms cumulant_sign_route_refuted
#print axioms resonance_ceiling_below_prize_floor
#print axioms coeff_route_loose_export
#print axioms roughness_does_not_add_bad_primes_export
#print axioms prizeBound_iff_shawValue_le_export
#print axioms strictPrizeBound_iff_shawValue_lt_export
#print axioms strictRawPrizeFamilyBound_iff_strictShawValueFamilyBound_export
#print axioms exists_strictRawPrizeFamilyBound_iff_exists_strictShawValueFamilyBound_export
#print axioms not_exists_strictRawPrizeFamilyBound_iff_not_exists_strictShawValueFamilyBound_export
#print axioms exists_nonneg_strictRawPrizeFamilyBound_iff_exists_nonneg_strictShawValueFamilyBound_export
#print axioms not_exists_nonneg_strictRawPrizeFamilyBound_iff_not_exists_nonneg_strictShawValueFamilyBound_export
#print axioms shawValue_worstPeriod_clean_corridor_export
#print axioms shawValue_clean_corridor_width_eq_export
#print axioms shawValue_bracket_width_eq_sqrt_export
#print axioms worstPeriod_sharp_bracket_export
#print axioms completion_vacuous_below_trivial_ceiling_export
#print axioms shawValue_worstPeriod_torsion_full_corridor_export
#print axioms worstPeriod_torsion_sharp_floor_export
#print axioms charP_wrap_gap_ge_two_mul_sq_export
#print axioms charP_wrap_gap_nonneg_of_logConcave_export
#print axioms charP_transfer_of_dominance_logConcave_export
#print axioms charP_stepRatioMonotoneAt_iff_gap_nonneg_export
#print axioms charP_stepRatioMonotone_false_n32_export
#print axioms charP_no_universal_positive_stepRatioMonotone_export
#print axioms rho_normalized_antitone_and_ceiling_incompatible_export
#print axioms rho_antitone_route_not_universal_export
#print axioms valueShift_nontrivial_forces_flat_histogram_export
#print axioms valueShift_step_zero_of_one_histogram_witness_export
#print axioms valueShift_route_vacuous_of_one_histogram_witness_export
#print axioms wraparound_markov_count_le_export
#print axioms wraparound_markov_bound_vacuous_below_mean_export
#print axioms wraparound_average_control_does_not_bound_sup_export
#print axioms doorIV_naiveIncidenceScale_eq_sqrt_mul_prizeScale_export
#print axioms doorIV_naiveIncidenceBound_iff_shawValue_le_scaled_export
#print axioms doorIV_index_le_sq_of_scaledConstant_le_export
#print axioms doorIV_scaledConstant_le_iff_index_le_sq_export
#print axioms doorIV_not_scaledConstantFamily_le_uniform_of_exists_index_gt_sq_export
#print axioms doorIV_cosetInvariant_blind_to_order_export
#print axioms doorIV_cosetHitting_selector_bound_iff_global_export
#print axioms doorIV_strict_selector_bound_misses_coset_export
#print axioms doorIV_additiveEnergyExcess_eq_zero_iff_sidon_export
#print axioms doorIV_no_positive_additiveEnergyExcess_of_subset_sidon_export
#print axioms doorIV_positive_additiveEnergyExcess_iff_not_sidon_export
#print axioms doorIV_prizeFamilyBound_iff_halfMassFamilyBound_export
#print axioms doorIV_prizeFamilyBound_iff_normalizedHalfMassFamilyBound_export
#print axioms doorIV_prizeFamilyBound_iff_all_halfMassShaw_forms_export
#print axioms doorIV_bddAbove_nonneg_normalizedPrize_export
#print axioms doorIV_bddAbove_nonneg_normalizedHalfMass_export
#print axioms doorIV_bddAbove_nonneg_rawPrize_export
#print axioms doorIV_bddAbove_nonneg_rawHalfMass_export
#print axioms doorIV_bddAbove_prize_iff_nonneg_rawHalfMass_export
#print axioms doorIV_bddAbove_halfMass_iff_nonneg_rawPrize_export
#print axioms doorIV_not_nonneg_rawPrize_iff_prizeDrift_export
#print axioms doorIV_not_nonneg_rawHalfMass_iff_halfMassDrift_export
#print axioms doorIV_not_bddAbove_prize_iff_not_bddAbove_halfMass_export
#print axioms doorIV_not_bddAbove_prize_iff_halfMassDrift_export
#print axioms doorIV_not_bddAbove_halfMass_iff_prizeDrift_export
#print axioms doorIV_bddAbove_prize_iff_not_halfMassDrift_export
#print axioms doorIV_bddAbove_halfMass_iff_not_prizeDrift_export
#print axioms doorIV_corePrize_of_dominated_majorant_export
#print axioms doorIV_shawOOne_of_coreMajorant_export
#print axioms doorIV_landau_shaw_of_dominated_majorant_export
#print axioms doorIV_shawOOne_of_dominated_majorant_export
#print axioms trivial_cocycle_full_concentration_export
#print axioms trivial_cocycle_offSupport_zero_export
#print axioms jacobiCocycleDispersion_iff_shawValue_le_export
#print axioms exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_exists_nonneg_shawValueFamilyBound_pos_export
#print axioms not_exists_nonneg_jacobiCocycleDispersionFamilyBound_iff_not_exists_nonneg_shawValueFamilyBound_pos_export
#print axioms exists_jacobiCocycleDispersionFamilyBound_iff_rawSandwich_export
#print axioms two_faces_are_one_wall_export
#print axioms noFifthDoor_forces_doorIV_export
#print axioms prizeCertifying_subset_doorIV_export
#print axioms doorIV_corridor_export
#print axioms doorIV_corridor_width_pos_export
#print axioms bgkScale_eq_sqrtL_mul_prizeScale_export
#print axioms noFifthDoor_ceilingRespecting_classical_overshoots_export
#print axioms noFifthDoor_forces_doorIV_ceilingRespecting_export
#print axioms noFifthDoor_classical_prize_certificate_violates_provenScale_export
#print axioms noFifthDoor_prize_certificate_doorIV_or_violates_provenScale_export
#print axioms shawGrand_prize_reduces_to_doorIV_export
#print axioms shawGrand_prize_reduces_to_doorIV_of_pos_lt_export
#print axioms shawGrand_prize_reduces_to_doorIV_eventually_export
#print axioms noTighterBound_secondMoment_blind_export
#print axioms noTighterBound_from_symmetric_or_L2_export
#print axioms doorIV_object_moment_corridor_export
#print axioms prize_iff_shawBounded_doorIV_only_and_object_moment_trapped_export
#print axioms doorIV_abs_signed_le_abs_moment_export
#print axioms doorIV_leak_nonneg_export
#print axioms doorIV_abs_moment_bound_transfers_export
#print axioms trivial_cocycle_overshoots_thin_export
#print axioms trivial_overshoot_gap_pos_export
#print axioms allDefect_cs_floor_vacuous_export
#print axioms gaussEnergyStep_incrementOne_lt_two_n_export
#print axioms gaussEnergyStep_step_of_increments_le_export
#print axioms dilationEnergy_step_iff_offdiagonal_export
#print axioms dilationEnergy_deep_step_of_depth2K_energy_export
#print axioms dilationEnergy_not_deep_step_of_offdiagonal_gt_export
#print axioms dilationEnergy_not_depth2K_energy_of_cs_and_offdiagonal_gt_export
#print axioms coreReduction_mStar_gt_of_BCHKS_fails_export
#print axioms coreReduction_mStar_le_iff_BCHKS_export
#print axioms coreReduction_clears_johnson_iff_BCHKS_at_prev_fold_export



/-! ## Door-IV odd signed moment census bridge. Scope: **obstruction/capstone**.

These exports make the exact algebra behind the odd-`r` signed-deep probes permanent: full period
moments equal a zero-sum census, deleting the principal `b = 0` term gives the prize-relevant
`b ≠ 0` identity, and vanishing census forces the rigid value `A_r = -|G|^r`. This pins the
sign-rigidity wall as an exact census identity, not a numerical artifact. -/

/-- **[capstone, GaussPeriodMomentCensus]** Full all-frequency moment ↔ additive zero-sum census
identity, valid at every depth `r` by character orthogonality. -/
theorem gaussPeriod_sum_eta_pow_eq_card_mul_zeroSumCensus_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    ∑ b : F,
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b) ^ r
      = (Fintype.card F : ℂ) *
        (_root_.ProximityGap.Frontier.GaussPeriodMomentCensus.zeroSumCensus G r : ℂ) :=
  _root_.ProximityGap.Frontier.GaussPeriodMomentCensus.sum_eta_pow_eq_card_mul_zeroSumCensus
    hψ G r

/-- **[capstone, GaussPeriodMomentCensus]** Deleted `b ≠ 0` moment ↔ census identity: the
prize-relevant signed moment equals `|F|·W_r - |G|^r`, with the principal term removed exactly. -/
theorem gaussPeriod_sum_eta_pow_deleted_eq_card_mul_zeroSumCensus_sub_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ) :
    ∑ b ∈ (Finset.univ.erase (0 : F)),
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b) ^ r
      = (Fintype.card F : ℂ) *
          (_root_.ProximityGap.Frontier.GaussPeriodMomentCensus.zeroSumCensus G r : ℂ)
        - (G.card : ℂ) ^ r :=
  _root_.ProximityGap.Frontier.GaussPeriodMomentCensus.sum_eta_pow_deleted_eq_card_mul_zeroSumCensus_sub
    hψ G r

/-- **[obstruction, GaussPeriodMomentCensus]** Rigid odd-depth value: if the additive zero-sum
census is zero, the deleted signed moment is exactly `-|G|^r`. Thus the observed odd-`r` sign
rigidity is a census identity, not a sup-norm bound. -/
theorem gaussPeriod_sum_eta_pow_deleted_eq_neg_card_pow_of_census_zero_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (r : ℕ)
    (hcensus : _root_.ProximityGap.Frontier.GaussPeriodMomentCensus.zeroSumCensus G r = 0) :
    ∑ b ∈ (Finset.univ.erase (0 : F)),
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b) ^ r
      = -((G.card : ℂ) ^ r) :=
  _root_.ProximityGap.Frontier.GaussPeriodMomentCensus.sum_eta_pow_deleted_eq_neg_card_pow_of_census_zero
    hψ G r hcensus

#print axioms gaussPeriod_sum_eta_pow_eq_card_mul_zeroSumCensus_export
#print axioms gaussPeriod_sum_eta_pow_deleted_eq_card_mul_zeroSumCensus_sub_export
#print axioms gaussPeriod_sum_eta_pow_deleted_eq_neg_card_pow_of_census_zero_export

/-! ## Door-IV sixth marginal cumulant collapse. Scope: **obstruction**.

These exports make the explicit 6th-marginal rung permanent: when the sixth connected cumulant
vanishes, the sixth moment is exactly its Wick/lower-cumulant value, hence any sixth-moment control
passes through the already-mapped 2nd/4th data. This complements the signed 3-3 connected-correlation
closure below; it is a no-new-sixth-order-lever statement only. -/

/-- **[obstruction, DoorIVSixthCumulant]** Vanishing sixth connected cumulant collapses the sixth
moment to its Wick value. -/
theorem doorIV_m6_eq_wick_of_sixth_cumulant_zero_export
    {m6 wick kappa6 : ℝ}
    (hdecomp : m6 = kappa6 + wick) (hzero : kappa6 = 0) :
    m6 = wick :=
  _root_.ProximityGap.Frontier.DoorIVSixthCumulantVanishes.m6_eq_wick_of_sixth_cumulant_zero
    hdecomp hzero

/-- **[obstruction, DoorIVSixthCumulant]** Explicit lower-cumulant polynomial form: with `κ₆ = 0`,
`m₆ = 15·κ₄·κ₂ + 15·κ₂³`, so the sixth moment carries no independent sixth-order datum. -/
theorem doorIV_m6_eq_lowerCumulant_poly_of_sixth_cumulant_zero_export
    {m6 kappa2 kappa4 kappa6 : ℝ}
    (hdecomp : m6 = kappa6 + (15 * kappa4 * kappa2 + 15 * kappa2 ^ 3))
    (hzero : kappa6 = 0) :
    m6 = 15 * kappa4 * kappa2 + 15 * kappa2 ^ 3 :=
  _root_.ProximityGap.Frontier.DoorIVSixthCumulantVanishes.m6_eq_lowerCumulant_poly_of_sixth_cumulant_zero
    hdecomp hzero

/-- **[obstruction, DoorIVSixthCumulant]** Central-moment polynomial form: with `κ₆ = 0`,
`m₆ = 15·m₄·m₂ - 30·m₂³`, a fixed polynomial in the dead Plancherel/energy data. -/
theorem doorIV_m6_eq_centralMoment_poly_of_sixth_cumulant_zero_export
    {m6 m2 m4 kappa6 : ℝ}
    (hdecomp : m6 = kappa6 + (15 * (m4 - 3 * m2 ^ 2) * m2 + 15 * m2 ^ 3))
    (hzero : kappa6 = 0) :
    m6 = 15 * m4 * m2 - 30 * m2 ^ 3 :=
  _root_.ProximityGap.Frontier.DoorIVSixthCumulantVanishes.m6_eq_centralMoment_poly_of_sixth_cumulant_zero
    hdecomp hzero

/-- **[obstruction, DoorIVSixthCumulant]** A sixth-moment control gives no new door-(iv) lever once
`m₆` Wick-factorizes: the candidate is controlled by the lower-order Wick data. -/
theorem doorIV_control_passes_through_sixth_wick_export
    {M m6 wick : ℝ}
    (hctrl : M ≤ m6) (hfact : m6 = wick) :
    M ≤ wick :=
  _root_.ProximityGap.Frontier.DoorIVSixthCumulantVanishes.control_passes_through_sixth_wick
    hctrl hfact

#print axioms doorIV_m6_eq_wick_of_sixth_cumulant_zero_export
#print axioms doorIV_m6_eq_lowerCumulant_poly_of_sixth_cumulant_zero_export
#print axioms doorIV_m6_eq_centralMoment_poly_of_sixth_cumulant_zero_export
#print axioms doorIV_control_passes_through_sixth_wick_export

/-! ## Door-IV connected-correlation hierarchy closure. Scope: **obstruction/capstone**.

These exports make the newest door-(iv) Lane-1/Lane-3 closure permanent: once the connected fourth
cumulant and the signed 3-3 / sixth-order connected cumulant vanish, every attempted bound routed
through the connected-correlation hierarchy through sixth order factors through the lower-order Wick
/ diagonal data already mapped dead. The order-uniform ladder lemma records the same obstruction for
any finite set of higher cumulant rungs. This is a no-new-correlation-lever statement only; it does
not prove CORE. -/

/-- **[obstruction, DoorIVCorrelationHierarchy]** If the connected triple correlation vanishes,
the canonical signed six-point functional `|κ₃|²` is exactly zero. Thus the first phase-sensitive
sixth-order object supplies no door-(iv) lower-bound content. -/
theorem doorIV_sixPoint_lever_vacuous_export {κ₃ : ℂ} (hzero : κ₃ = 0) :
    Complex.normSq κ₃ = 0 :=
  _root_.ProximityGap.Frontier.DoorIVCorrelationHierarchyCapstone.sixPoint_lever_vacuous hzero

/-- **[capstone, DoorIVCorrelationHierarchy]** Connected-correlation closure through sixth order:
if a candidate is controlled by both the 2-2 and 3-3 moments, and the connected fourth and sixth
cumulants vanish, then both controls pass through the Wick values. No connected-correlation
functional through order six supplies a fresh door-(iv) bound. -/
theorem doorIV_correlation_hierarchy_no_lever_export
    {M m22 wick4 cum4 m33 wick6 cum6 : ℝ}
    (hctrl4 : M ≤ m22) (hctrl6 : M ≤ m33)
    (hdec4 : m22 = wick4 + cum4) (hcum4 : cum4 = 0)
    (hdec6 : m33 = wick6 + cum6) (hcum6 : cum6 = 0) :
    M ≤ wick4 ∧ M ≤ wick6 :=
  _root_.ProximityGap.Frontier.DoorIVCorrelationHierarchyCapstone.correlation_hierarchy_no_lever
    hctrl4 hctrl6 hdec4 hcum4 hdec6 hcum6

/-- **[capstone, DoorIVCorrelationHierarchy]** Full citable closure through sixth order, including
both Wick-factorization of the 4th/6th connected-correlation controls and the exact zero
of the signed six-point functional when `κ₃ = 0`. -/
theorem doorIV_correlation_hierarchy_closed_through_six_export
    {M m22 wick4 cum4 m33 wick6 cum6 : ℝ} {κ₃ : ℂ}
    (hctrl4 : M ≤ m22) (hctrl6 : M ≤ m33)
    (hdec4 : m22 = wick4 + cum4) (hcum4 : cum4 = 0)
    (hdec6 : m33 = wick6 + cum6) (hcum6 : cum6 = 0)
    (htriple : κ₃ = 0) :
    (M ≤ wick4 ∧ M ≤ wick6) ∧ Complex.normSq κ₃ = 0 :=
  _root_.ProximityGap.Frontier.DoorIVCorrelationHierarchyCapstone.correlation_hierarchy_closed_through_six
    hctrl4 hctrl6 hdec4 hcum4 hdec6 hcum6 htriple

/-- **[obstruction, DoorIVTripleCorrelationVanishes]** If the connected triple correlation `κ₃`
vanishes, the signed six-point functional `|κ₃|²` is exactly zero. This is the direct indexed form of
the 6-point connected-correlation wall. -/
theorem doorIV_tripleCorrelation_sixPoint_zero_export {κ₃ : ℂ} (hzero : κ₃ = 0) :
    Complex.normSq κ₃ = 0 :=
  _root_.ProximityGap.Frontier.DoorIVTripleCorrelationVanishes.sixPoint_functional_zero_of_triple_zero
    hzero

/-- **[obstruction, DoorIVTripleCorrelationVanishes]** A six-point lever routed through the signed
triple-correlation functional is vacuous when `κ₃ = 0`: it only supplies `0 ≤ ‖M‖²`. -/
theorem doorIV_tripleCorrelation_sixPoint_vacuous_export {M κ₃ : ℂ}
    (hbound : Complex.normSq κ₃ ≤ Complex.normSq M) (hzero : κ₃ = 0) :
    (0 : ℝ) ≤ Complex.normSq M :=
  _root_.ProximityGap.Frontier.DoorIVTripleCorrelationVanishes.sixPoint_lever_vacuous_of_triple_zero
    hbound hzero

/-- **[obstruction, DoorIVTripleCorrelationVanishes]** With vanishing connected 3-3 cumulant, the
sixth-order 3-3 moment collapses to its Wick/lower-order value, so the candidate adds no new
six-point phase structure beyond already-mapped covariance/diagonal data. -/
theorem doorIV_tripleCorrelation_m33_eq_wick_export {m33 wick cumulant : ℝ}
    (hdecomp : m33 = wick + cumulant) (hzero : cumulant = 0) :
    m33 = wick :=
  _root_.ProximityGap.Frontier.DoorIVTripleCorrelationVanishes.m33_eq_wick_of_cumulant_zero
    hdecomp hzero

/-- **[obstruction, DoorIVCumulantLadder]** Order-uniform single-rung form: for any
moment-cumulant decomposition `mr = wickr + cumr`, a vanishing connected cumulant forces every
control through that rung to pass through the Wick value. -/
theorem doorIV_ladder_control_passes_through_wick_export
    {M mr wickr cumr : ℝ}
    (hctrl : M ≤ mr) (hdecomp : mr = wickr + cumr) (hzero : cumr = 0) :
    M ≤ wickr :=
  _root_.ProximityGap.Frontier.DoorIVCumulantLadderVacuity.ladder_control_passes_through_wick
    hctrl hdecomp hzero

/-- **[capstone, DoorIVCumulantLadder]** Whole finite ladder form: if every connected
cumulant in a finite set of orders vanishes and every moment decomposes as Wick plus cumulant,
then each moment is its Wick value. Climbing to higher connected-correlation rungs adds no new
structure without a nonzero connected cumulant. -/
theorem doorIV_whole_ladder_wick_export
    {R : Finset ℕ} {m wick cum : ℕ → ℝ}
    (hdec : ∀ r ∈ R, m r = wick r + cum r)
    (hladder : ∀ r ∈ R, cum r = 0) :
    ∀ r ∈ R, m r = wick r :=
  _root_.ProximityGap.Frontier.DoorIVCumulantLadderVacuity.whole_ladder_wick hdec hladder

/-- **[capstone, DoorIVCumulantLadder]** Whole finite ladder control form: if a candidate is
bounded at every rung of a finite cumulant ladder whose connected cumulants vanish, it is bounded
at every rung by the corresponding Wick value. This packages the higher-order correlation route
as a Wick-data route, not a fresh anti-concentration lever. -/
theorem doorIV_whole_ladder_control_export
    {R : Finset ℕ} {M : ℝ} {m wick cum : ℕ → ℝ}
    (hctrl : ∀ r ∈ R, M ≤ m r)
    (hdec : ∀ r ∈ R, m r = wick r + cum r)
    (hladder : ∀ r ∈ R, cum r = 0) :
    ∀ r ∈ R, M ≤ wick r :=
  _root_.ProximityGap.Frontier.DoorIVCumulantLadderVacuity.whole_ladder_control hctrl hdec hladder

/-- **[obstruction, DoorIVCrossHalfPhase]** In the probed real-collinear cross-half regime,
the period norm equals the half-mass exactly. The cross-half datum carries no angular saving:
coherence is saturated at `1`. -/
theorem doorIV_crossHalf_norm_add_eq_halfMass_export
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E} {t : ℝ} (ht : 0 ≤ t)
    (h : _root_.ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.crossHalfRatio A B t) :
    ‖A + B‖ = ‖A‖ + ‖B‖ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.norm_add_eq_halfMass_of_real_collinear
    ht h

/-- **[obstruction, DoorIVCrossHalfPhase]** Any fixed multiplier bound through one half,
`‖A+B‖≤c‖A‖`, must already pay the full measured real ratio: `1+t≤c`. Thus a fixed-factor
recursive half route hides the hard frequency-dependent ratio in the constant. -/
theorem doorIV_crossHalf_fixed_multiplier_forces_ratio_le_export
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E} {t c : ℝ} (ht : 0 ≤ t) (hA : 0 < ‖A‖)
    (h : _root_.ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.crossHalfRatio A B t)
    (hbound : ‖A + B‖ ≤ c * ‖A‖) :
    1 + t ≤ c :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.fixed_multiplier_forces_ratio_le
    ht hA h hbound

/-- **[obstruction, DoorIVCrossHalfPhase]** Contrapositive form used by the probe verdict:
if the measured cross-half ratio exceeds the proposed fixed multiplier, the one-half factorization
bound fails at that frequency. -/
theorem doorIV_crossHalf_fixed_multiplier_fails_of_ratio_gt_export
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A B : E} {t c : ℝ} (ht : 0 ≤ t) (hA : 0 < ‖A‖)
    (h : _root_.ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.crossHalfRatio A B t)
    (hgt : c < 1 + t) :
    ¬ ‖A + B‖ ≤ c * ‖A‖ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCrossHalfPhaseUnstructured.fixed_multiplier_fails_of_ratio_gt
    ht hA h hgt

/-- **[obstruction, DoorIVHalfMassBalanceAtArgmax]** A positive balance floor `r` forces any
single-half certificate at a coherent frequency to pay `(1+r)` times the heavier half.  This is the
formal version of the probed worst-b balance enrichment: keeping one dyadic half cannot manufacture a
shrinking anti-concentration gain. -/
theorem doorIV_halfMassBalance_single_half_pays_floor_export
    {E : Type*} [SeminormedAddCommGroup E] {A B : E} {g : ℝ → ℝ} {r : ℝ}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖)
    (hr : r ≤ _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassBalanceAtArgmax.balance A B)
    (hbound : ‖A + B‖ ≤ g (max ‖A‖ ‖B‖)) :
    (1 + r) * max ‖A‖ ‖B‖ ≤ g (max ‖A‖ ‖B‖) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassBalanceAtArgmax.single_half_bound_pays_balance_floor
    hcoh hr hbound

/-- **[obstruction, DoorIVHalfMassBalanceAtArgmax]** At coherent perfect balance the normalized loss
from keeping only the heavier half is exactly `2`, the sharp endpoint of the drop-a-half obstruction. -/
theorem doorIV_halfMassBalance_descent_loss_eq_two_export
    {E : Type*} [SeminormedAddCommGroup E] {A B : E}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hbal : ‖A‖ = ‖B‖)
    (hpos : 0 < max ‖A‖ ‖B‖) :
    ‖A + B‖ / max ‖A‖ ‖B‖ = 2 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassBalanceAtArgmax.descent_loss_eq_two_of_coherent_balanced
    hcoh hbal hpos

/-- **[obstruction, DoorIVHalfMassBalanceAtArgmax]** In any coherent two-half split, dropping to the
heavier half loses at most the constant factor `2`.  The balanced worst-b probes saturate this endpoint,
so this descent shape is constant-factor bookkeeping, not a square-root cancellation lever. -/
theorem doorIV_halfMassBalance_descent_loss_le_two_export
    {E : Type*} [SeminormedAddCommGroup E] {A B : E}
    (hcoh : ‖A + B‖ = ‖A‖ + ‖B‖) (hpos : 0 < max ‖A‖ ‖B‖) :
    ‖A + B‖ ≤ 2 * max ‖A‖ ‖B‖ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassBalanceAtArgmax.descent_loss_le_two hcoh hpos

/-- **[capstone, DoorIVHalfMassDilationForm]** The second coset half is exactly the same
sub-period evaluated at the dilated frequency: `eta(gH,b)=eta(H,g*b)`. -/
theorem doorIV_halfMass_eta_image_smul_eq_eta_dilate_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (H : Finset F) {g b : F} (hg : g ≠ 0) :
    _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ
        (H.image (fun y => g * y)) b =
      _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H (g * b) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassDilationForm.eta_image_smul_eq_eta_dilate H hg

/-- **[capstone, DoorIVHalfMassDilationForm]** On a disjoint index-two split, the full period is
the sum of one sub-period at `b` and the same sub-period at the dilated frequency `g*b`. -/
theorem doorIV_halfMass_eta_index_two_split_dilate_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (H : Finset F) {g b : F} (hg : g ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => g * y))) :
    _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ
        (H ∪ H.image (fun y => g * y)) b =
      _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H b +
        _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H (g * b) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassDilationForm.eta_index_two_split_dilate
    H hg hdisj

/-- **[capstone, DoorIVHalfMassDilationForm]** The open half-mass burden is a bound on a single
sub-period magnitude at two multiplicatively dilated frequencies, `b` and `g*b`. -/
theorem doorIV_halfMass_norm_eta_le_two_dilate_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (H : Finset F) {g b : F} (hg : g ≠ 0)
    (hdisj : Disjoint H (H.image (fun y => g * y))) :
    ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ
        (H ∪ H.image (fun y => g * y)) b‖ ≤
      ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H b‖ +
        ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ H (g * b)‖ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVHalfMassDilationForm.norm_eta_le_two_dilate H hg hdisj

/-- **[obstruction, DoorIVSignCocycleMassBalance]** The positive same-sign/doubling cross-mass
is exactly balanced by the negative opposite-sign/cancellation cross-mass. This is the indexed
mass-level constraint behind the real dilation sign-cocycle: the `+` branch is not a free budget. -/
theorem doorIV_sign_positiveMass_eq_negativeMass_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F}
    (hdisj : Disjoint G (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ G)) :
    (∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.posPart
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re))) =
      ∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.negPart
        ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
          (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re)) :=
  _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.sign_positiveMass_eq_negativeMass
    hψ G hG hdisj

/-- **[obstruction, DoorIVSignCocycleMassBalance]** Nonzero positive same-sign mass rules out
a globally nonnegative sign cocycle. Any nontrivial doubling mass forces an opposite-sign/cancelling
contribution somewhere else; the remaining open problem is only the single worst-frequency word. -/
theorem doorIV_sign_not_all_nonneg_of_positiveMass_pos_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F}
    (hdisj : Disjoint G (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ G))
    (hpos : 0 < ∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.posPart
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re))) :
    ¬ ∀ b : F, 0 ≤
      (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re :=
  _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.not_all_nonneg_of_positiveMass_pos
    hψ G hG hdisj hpos

/-- **[obstruction, DoorIVSignCocycleMassBalance]** Local witness form: nonzero positive
same-sign/doubling mass forces an actually negative opposite-sign frequency. The balance theorem is
therefore concrete spectral cancellation, not just an abstract equality of totals. -/
theorem doorIV_sign_exists_negative_cross_of_positiveMass_pos_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F}
    (hdisj : Disjoint G (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ G))
    (hpos : 0 < ∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.posPart
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re))) :
    ∃ b : F,
      (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re < 0 :=
  _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.exists_negative_cross_of_positiveMass_pos
    hψ G hG hdisj hpos

/-- **[obstruction, DoorIVSignCocycleMassBalance]** Symmetric local witness form: nonzero
opposite-sign/cancelling mass forces an actual same-sign frequency. The exact 50/50 sign-cocycle split
is therefore witnessed on both sides of the finite spectrum. -/
theorem doorIV_sign_exists_positive_cross_of_negativeMass_pos_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F}
    (hdisj : Disjoint G (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ G))
    (hneg : 0 < ∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.negPart
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re))) :
    ∃ b : F, 0 <
      (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re :=
  _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.exists_positive_cross_of_negativeMass_pos
    hψ G hG hdisj hneg

/-- **[obstruction, DoorIVSignCocycleMassBalance]** The same-sign/doubling branch occupies at most
half of the global Cauchy--Schwarz cross budget `q·|G|`. This is only a global mass constraint, not a
worst-frequency CORE bound. -/
theorem doorIV_sign_positiveMass_le_half_card_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint G (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ G)) :
    (∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.posPart
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re))) ≤
      ((Fintype.card F : ℝ) * G.card) / 2 :=
  _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.positiveMass_le_half_card
    hψ G hG hζ hdisj

/-- **[obstruction, DoorIVSignCocycleMassBalance]** The opposite-sign/cancelling branch obeys the
same half-budget cap as the same-sign branch. Neither side of the real sign-cocycle can spend more
than half of the global cross budget. -/
theorem doorIV_sign_negativeMass_le_half_card_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F} (hζ : ζ ≠ 0)
    (hdisj : Disjoint G (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ G)) :
    (∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.negPart
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re))) ≤
      ((Fintype.card F : ℝ) * G.card) / 2 :=
  _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.negativeMass_le_half_card
    hψ G hG hζ hdisj

/-- **[obstruction, DoorIVSignCocycleMassBalance]** Direct norm-cross form: under the disjoint-dilate
sign-cocycle hypotheses, the same-sign branch is exactly one half of
`∑ b, ‖η_b‖ * ‖η_{ζb}‖`. -/
theorem doorIV_sign_positiveMass_eq_half_total_doublingMass_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F}
    (hdisj : Disjoint G (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ G)) :
    (∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.posPart
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re))) =
      (∑ b : F, ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ *
        ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)‖) / 2 :=
  _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.positiveMass_eq_half_total_doublingMass
    hψ G hG hdisj

/-- **[obstruction, DoorIVSignCocycleMassBalance]** Direct norm-cross form for the cancelling branch:
it is also exactly one half of the total norm cross-mass. Any proof narrative that spends only the
same-sign side is therefore globally over-budget. -/
theorem doorIV_sign_negativeMass_eq_half_total_doublingMass_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hG : ∀ x ∈ G, -x ∈ G) {ζ : F}
    (hdisj : Disjoint G (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ G)) :
    (∑ b : F, (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.negPart
      ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b).re *
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)).re))) =
      (∑ b : F, ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ *
        ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G (ζ * b)‖) / 2 :=
  _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.negativeMass_eq_half_total_doublingMass
    hψ G hG hdisj

/-- **[obstruction, DoorIVAlgebraicFloorCyclotomicWall]** The concrete `μ₁₆` gapped minor
(rows `(1,2,5)`, powers `(1,5,9)`) vanishes under the dyadic relation `ζ^8=-1`. This is the
formal cyclotomic wall behind the algebraic-floor probe: generic nonzero-minor reasoning is not
valid on the actual dyadic subgroup without handling these relations. -/
theorem doorIV_gappedMinor125_159_eq_zero_export {ζ : ℂ} (hζ : ζ ^ 8 = -1) :
    _root_.ArkLib.ProximityGap.DoorIVAlgebraicFloorCyclotomicWall.gappedMinor125_159 ζ = 0 :=
  _root_.ArkLib.ProximityGap.DoorIVAlgebraicFloorCyclotomicWall.gappedMinor125_159_eq_zero_of_pow8_eq_neg_one
    hζ

/-- **[obstruction, DoorIVAlgebraicFloorCyclotomicWall]** Contradiction form: any hypothesis that
this explicit dyadic gapped minor is nonzero is false. -/
theorem doorIV_not_gappedMinor125_159_ne_zero_export {ζ : ℂ} (hζ : ζ ^ 8 = -1) :
    ¬ _root_.ArkLib.ProximityGap.DoorIVAlgebraicFloorCyclotomicWall.gappedMinor125_159 ζ ≠ 0 :=
  _root_.ArkLib.ProximityGap.DoorIVAlgebraicFloorCyclotomicWall.not_gappedMinor125_159_ne_zero_of_pow8_eq_neg_one
    hζ

/-- **[obstruction, DoorIVEighthCumulantSignUnstable]** Mixed signs in a candidate eighth-cumulant
statistic refute both universal fixed-sign certificates (`κ ≥ 0` and `κ ≤ 0`). This indexes the
formal constraint supplied by the multiprime door-IV probe; no cumulant bound is claimed. -/
theorem doorIV_eighthCumulant_mixed_sign_forbids_fixed_sign_export
    {ι : Type*} {κ : ι → ℝ} {i j : ι} (hpos : 0 < κ i) (hneg : κ j < 0) :
    ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVEighthCumulantSignUnstable.UniversalNonnegative κ ∧
      ¬ _root_.ArkLib.ProximityGap.Frontier.DoorIVEighthCumulantSignUnstable.UniversalNonpositive κ :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVEighthCumulantSignUnstable.mixed_sign_forbids_universal_fixed_sign
    hpos hneg

/-- **[obstruction, DoorIVEighthCumulantSignUnstable]** Disjunction/contradiction form: once the
same admissible statistic takes both positive and negative values, it cannot provide a universal
fixed-sign eighth-cumulant route. -/
theorem doorIV_eighthCumulant_no_fixedSignCertificate_export
    {ι : Type*} {κ : ι → ℝ} {i j : ι} (hpos : 0 < κ i) (hneg : κ j < 0) :
    ¬ (_root_.ArkLib.ProximityGap.Frontier.DoorIVEighthCumulantSignUnstable.UniversalNonnegative κ ∨
      _root_.ArkLib.ProximityGap.Frontier.DoorIVEighthCumulantSignUnstable.UniversalNonpositive κ) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVEighthCumulantSignUnstable.no_fixedSignCertificate_of_mixed_sign
    hpos hneg

/-- **[capstone, DoorIVXGatedPrizeReduction]** The named open `XGatedRatio` hypothesis, plus its
levelwise `x`-gate, telescopes to the explicit square-root tower factor `√(2^μ)·M₀`. This is the
end-to-end Lane-2 reduction of the corrected door-(iv) scalar to the geometric prize scale; the
`XGatedRatio` input itself remains open. -/
theorem doorIV_levelWorst_le_sqrt_two_pow_mul_of_xGatedRatio_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} {μ : ℕ} {x₀ lnm : ℝ}
    (hx : _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.XGatedRatio ψ G ζ μ x₀ lnm)
    (hgate : ∀ k : ℕ, k ≤ μ → x₀ * lnm ≤ ((_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.levelTower ψ G ζ k).card : ℝ)) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ μ ≤
      Real.sqrt ((2 : ℝ) ^ μ) *
        _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ 0 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedPrizeReduction.levelWorst_le_sqrt_two_pow_mul_of_xGatedRatio
    hx hgate

/-- **[capstone, DoorIVXGatePrizeBudget]** The corrected `√2` per-level gate, a base bound
`M₀≤C√L`, and the dimension registration `(√2)^μ≤√n` compose to the exact prize-shaped budget
`M_μ≤C√(nL)`. This is pure reduction algebra: no proof of the open gate, no CORE claim. -/
theorem doorIV_levelWorst_le_prize_budget_of_xgate_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} {C L n : ℝ} {μ : ℕ}
    (hr : _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.LevelRatioBoundNZ ψ G ζ μ (Real.sqrt 2))
    (h_dim : (Real.sqrt 2) ^ μ ≤ Real.sqrt n)
    (h_base : _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ 0 ≤ C * Real.sqrt L)
    (hC : 0 ≤ C) (hL : 0 ≤ L) (hn : 0 ≤ n) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ μ ≤ C * Real.sqrt (n * L) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatePrizeBudget.levelWorst_le_prize_budget_of_xgate
    hr h_dim h_base hC hL hn

/-- **[obstruction, DoorIVXGatedBaseThreshold]** Split telescope with `k*` factor-2 base levels
and `√2` cancellation above the gate threshold. -/
theorem doorIV_gateThreshold_split_telescope_sqrt2_export (M : ℕ → ℝ) (hpos : ∀ k, 0 ≤ M k)
    (kstar r : ℕ)
    (hbase : ∀ k, k < kstar → M (k + 1) ≤ 2 * M k)
    (hcanc : ∀ j, j < r → M (kstar + j + 1) ≤ Real.sqrt 2 * M (kstar + j)) :
    M (kstar + r) ≤ 2 ^ kstar * (Real.sqrt 2) ^ r * M 0 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThreshold.split_telescope_sqrt2
    M hpos kstar r hbase hcanc

/-- **[obstruction, DoorIVXGatedBaseThreshold]** Any nonzero gate threshold `k* ≥ 1` costs a
strict excess factor over the clean `(√2)^(k*+r)` floor. -/
theorem doorIV_gateThreshold_strictly_above_clean_export {kstar : ℕ} (hk : 1 ≤ kstar) (r : ℕ) :
    (Real.sqrt 2) ^ (kstar + r) < (2 : ℝ) ^ kstar * (Real.sqrt 2) ^ r :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThreshold.gate_threshold_strictly_above_clean
    hk r

/-- **[obstruction, DoorIVXGatedBaseThresholdConcrete]** On the real `levelWorst` character sum,
the thin base step costs the unconditional trivial factor `2`. -/
theorem doorIV_levelWorst_base_step_two_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} (hζ : ζ ≠ 0) (k : ℕ)
    (hdisj : Disjoint
      (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.levelTower ψ G ζ k)
      (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.levelTower ψ G ζ k))) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ (k + 1) ≤
      2 * _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ k :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThresholdConcrete.levelWorst_step_two
    hζ k hdisj

/-- **[obstruction, DoorIVXGatedBaseThresholdConcrete]** Concrete base-corrected bound on the
real `levelWorst` object: `k*` base levels pay factor `2`, only the `r` levels above the gate get `√2`. -/
theorem doorIV_levelWorst_base_corrected_of_gate_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nontrivial F]
    {ψ : AddChar F ℂ} {G : Finset F} {ζ : F} (hζ : ζ ≠ 0) (kstar r : ℕ)
    (hdisj : ∀ k, Disjoint
      (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.levelTower ψ G ζ k)
      (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.dilate ζ
        (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.levelTower ψ G ζ k)))
    (hgate : _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.LevelRatioBoundNZ
      ψ G ζ (kstar + r) (Real.sqrt 2)) :
    _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ (kstar + r)
      ≤ 2 ^ kstar * (Real.sqrt 2) ^ r *
        _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedTelescopeBridge.levelWorst ψ G ζ 0 :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVXGatedBaseThresholdConcrete.levelWorst_le_base_corrected_of_gate
    hζ kstar r hdisj hgate

/-! ## Door-IV direct-proof refutations from the Paley/direct-proof essay. Scope: **obstruction**.

These exports make the latest direct-proof no-go kernels permanent: Gross--Koblitz phase
bookkeeping, Markoff-surface coupling, and Tannakian non-torsion twists. All three are
constraint lemmas only. They refute claimed shortcuts but do not prove CORE. -/

/-- **[obstruction, GKPhaseCoboundary]** The additive Hasse--Davenport coboundary is exactly the
Jacobi phase: under the product relation among unit Gauss phases, `J` is the `√p`-radius phase at
`θ₁ + θ₂ - θ₁₂`. -/
theorem doorIV_gk_coboundary_phase_eq_export {p : ℝ} (hp : 0 < p) (θ₁ θ₂ θ₁₂ : ℝ) {J : ℂ}
    (hJ : ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.gPhase p θ₁ *
        ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.gPhase p θ₂ =
      J * ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.gPhase p θ₁₂) :
    J = ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.gPhase p (θ₁ + θ₂ - θ₁₂) :=
  ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.coboundary_phase_eq
    hp θ₁ θ₂ θ₁₂ hJ

/-- **[obstruction, GKPhaseCoboundary]** A non-positive-real Jacobi factor certifies a nontrivial
coboundary, hence forbids the linear/character-phase model needed for the free `√m` collapse. -/
theorem doorIV_gk_nontrivial_coboundary_not_linearizable_export {p : ℝ} (hp : 0 < p)
    (θ₁ θ₂ θ₁₂ : ℝ) {J : ℂ}
    (hJ : ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.gPhase p θ₁ *
        ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.gPhase p θ₂ =
      J * ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.gPhase p θ₁₂)
    (hJne : J ≠ (Real.sqrt p : ℂ)) :
    Complex.exp ((θ₁ + θ₂ - θ₁₂) * Complex.I) ≠ 1 :=
  ArkLib.ProximityGap.Frontier.GKPhaseCoboundaryNonLinear.nontrivial_coboundary_not_linearizable
    hp θ₁ θ₂ θ₁₂ hJ hJne

/-- **[obstruction, MarkoffCoupling]** A Markoff/twisted weighted period transfers to the real
Paley period only in the constant-weight case; then the weighted period factors as `K` times the
original period. -/
theorem doorIV_markoff_weighted_period_factors_export {ι : Type*} (G : Finset ι)
    (w f : ι → ℂ) (K : ℂ) (hw : ∀ x ∈ G, w x = K) :
    (∑ x ∈ G, w x * f x) = K * (∑ x ∈ G, f x) :=
  _root_.ProximityGap.Frontier.weighted_period_factors G w f K hw

/-- **[obstruction, MarkoffCoupling]** Nonconstant slice weights refute every single-constant
factorization through the Paley period on a two-slice witness. -/
theorem doorIV_markoff_transfer_refuted_export {ι : Type*} [DecidableEq ι] (w : ι → ℂ)
    (x₀ x₁ : ι) (hx : x₀ ≠ x₁) (hprobe : w x₀ ≠ w x₁) :
    ¬ ∃ K : ℂ, ∀ f : ι → ℂ,
        (∑ x ∈ ({x₀, x₁} : Finset ι), w x * f x)
          = K * (∑ x ∈ ({x₀, x₁} : Finset ι), f x) :=
  _root_.ProximityGap.Frontier.markoff_transfer_refuted w x₀ x₁ hx hprobe

/-- **[obstruction, TannakianTwist]** A diagonal multiplicative twist only multiplies a
cyclotomic minor determinant by the product of row weights. -/
theorem doorIV_tannakian_twist_det_eq_export {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] (χ : n → R) (A : Matrix n n R) :
    (Matrix.of fun i j => χ i * A i j).det = (∏ i, χ i) * A.det :=
  ArkLib.ProximityGap.Frontier.Tannakian.twist_det_eq χ A

/-- **[obstruction, TannakianTwist]** Unit-valued diagonal twists preserve determinant vanishing,
so they cannot turn a dyadic cyclotomic vanishing minor into a nonzero one. -/
theorem doorIV_tannakian_twist_det_zero_iff_export {n : Type*} [DecidableEq n] [Fintype n]
    {R : Type*} [CommRing R] [IsDomain R] {χ : n → R} (hχ : ∀ i, χ i ≠ 0)
    (A : Matrix n n R) :
    (Matrix.of fun i j => χ i * A i j).det = 0 ↔ A.det = 0 :=
  ArkLib.ProximityGap.Frontier.Tannakian.twist_det_eq_zero_iff hχ A

/-- **[obstruction, TannakianTwist]** A character whose image orders divide `d` with
`gcd(d, |G|)=1` is trivial on the order-`|G|` subgroup. Thus a coprime non-torsion twist does
nothing on `μ_n`. -/
theorem doorIV_tannakian_coprime_order_trivial_export {G H : Type*} [Group G] [Group H]
    [Fintype G] (χ : G →* H) {d : ℕ} (hdiv : ∀ g : G, orderOf (χ g) ∣ d)
    (hcop : Nat.Coprime d (Fintype.card G)) :
    ∀ g : G, χ g = 1 :=
  ArkLib.ProximityGap.Frontier.Tannakian.coprime_order_trivial_on_mu χ hdiv hcop

/-- **[obstruction, TannakianTwist]** If a twist is trivial on the support, the twisted period
`Σ χ(x)f(x)` is literally the original period `Σ f(x)`. -/
theorem doorIV_tannakian_twist_period_eq_original_export {ι A : Type*} [Semiring A]
    (G : Finset ι) (χ f : ι → A) (hχ : ∀ x ∈ G, χ x = 1) :
    (∑ x ∈ G, χ x * f x) = ∑ x ∈ G, f x :=
  ArkLib.ProximityGap.Frontier.Tannakian.twist_period_eq_original_of_trivial G χ f hχ

/-- **[obstruction, TannakianTwist]** A coprime-order multiplicative twist has no period-level
effect: after embedding its values into any semiring with `1 ↦ 1`, the twisted period equals the
untwisted period. -/
theorem doorIV_tannakian_coprime_twisted_period_eq_original_export {G H A : Type*}
    [Group G] [Group H] [Fintype G] [Semiring A] (χ : G →* H) {d : ℕ}
    (hdiv : ∀ g : G, orderOf (χ g) ∣ d) (hcop : Nat.Coprime d (Fintype.card G))
    (embed : H → A) (hembed_one : embed 1 = 1) (f : G → A) :
    (∑ x : G, embed (χ x) * f x) = ∑ x : G, f x :=
  ArkLib.ProximityGap.Frontier.Tannakian.coprime_order_twisted_period_eq_original
    χ hdiv hcop embed hembed_one f

#print axioms doorIV_gk_coboundary_phase_eq_export
#print axioms doorIV_gk_nontrivial_coboundary_not_linearizable_export
#print axioms doorIV_markoff_weighted_period_factors_export
#print axioms doorIV_markoff_transfer_refuted_export
#print axioms doorIV_tannakian_twist_det_eq_export
#print axioms doorIV_tannakian_twist_det_zero_iff_export
#print axioms doorIV_tannakian_coprime_order_trivial_export

/-- **[descent, ZDegreeEnvelope]** The even/odd descent quadform
`R = Pp^2 - X·Qp^2` has degree at most the larger of the two branch support budgets
`2 deg Pp` and `1 + 2 deg Qp`. -/
theorem doorIV_descent_quadform_degreeEnvelope_export {F : Type*} [Field F]
    (Pp Qp : Polynomial F) :
    (_root_.ArkLib.ProximityGap.EvenOddDescent.descentQuadform Pp Qp).natDegree ≤
      max (2 * Pp.natDegree) (1 + 2 * Qp.natDegree) :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.descentQuadform_natDegree_le_max Pp Qp

/-- **[descent, ZDegreeEnvelope]** Consumer form: the non-symmetric descent `Z` count is
bounded by `max (2 deg Pp) (1 + 2 deg Qp)`, the explicit support envelope. -/
theorem doorIV_descent_Z_card_le_degreeEnvelope_export {F : Type*} [Field F] [DecidableEq F]
    {Pp Qp : Polynomial F}
    (hR : _root_.ArkLib.ProximityGap.EvenOddDescent.descentQuadform Pp Qp ≠ 0)
    (B : Finset F) :
    (B.filter (fun y => (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2)).card
      ≤ max (2 * Pp.natDegree) (1 + 2 * Qp.natDegree) :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.descentZ_card_le_degreeEnvelope hR B

/-- **[descent, ZDegreeEnvelope]** Indicator-sum form matching the descent identity's
`Z` term. -/
theorem doorIV_descent_Z_indicator_sum_le_degreeEnvelope_export {F : Type*} [Field F]
    [DecidableEq F]
    {Pp Qp : Polynomial F}
    (hR : _root_.ArkLib.ProximityGap.EvenOddDescent.descentQuadform Pp Qp ≠ 0)
    (B : Finset F) :
    (∑ y ∈ B, (if (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2 then 1 else 0))
      ≤ max (2 * Pp.natDegree) (1 + 2 * Qp.natDegree) :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.descentZ_indicator_sum_le_degreeEnvelope hR B

/-- **[descent, ZLagrangeBound]** Exponent-controlled form from the G1→G2 bridge:
`Z ≤ 1 + 2 * max (deg Pp) (deg Qp)`. -/
theorem doorIV_descent_Z_card_le_degBound_export {F : Type*} [Field F] [DecidableEq F]
    {Pp Qp : Polynomial F}
    (hR : _root_.ArkLib.ProximityGap.EvenOddDescent.descentQuadform Pp Qp ≠ 0)
    (B : Finset F) :
    (B.filter (fun y => (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2)).card
      ≤ 1 + 2 * max Pp.natDegree Qp.natDegree :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.descentZ_card_le_degBound hR B

/-- **[descent, ZLagrangeBound]** Indicator-sum exponent-controlled form matching the
summed `A + Z` notation: the `Z` indicator sum obeys the same G1→G2 exponent budget. -/
theorem doorIV_descent_Z_indicator_sum_le_degBound_export {F : Type*} [Field F] [DecidableEq F]
    {Pp Qp : Polynomial F}
    (hR : _root_.ArkLib.ProximityGap.EvenOddDescent.descentQuadform Pp Qp ≠ 0)
    (B : Finset F) :
    (∑ y ∈ B, (if (Pp.eval y) ^ 2 = y * (Qp.eval y) ^ 2 then 1 else 0))
      ≤ 1 + 2 * max Pp.natDegree Qp.natDegree :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.descentZ_indicator_sum_le_degBound hR B

/-- **[descent, even-spine]** Global symmetric backbone: summing the even fibre identity over the
base gives exactly twice the lower-level agreement count. -/
theorem doorIV_descentAgreement_even_eq_two_mul_export {F : Type*} [Field F] [DecidableEq F]
    (B : Finset F) (ρ Pf : F → F)
    (hρ0 : ∀ y ∈ B, ρ y ≠ 0) (h2 : (2 : F) ≠ 0) :
    (∑ y ∈ B, (({ρ y, -ρ y} : Finset F).filter (fun x => Pf y + x * 0 = 0)).card)
      = 2 * (B.filter (fun y => Pf y = 0)).card :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.descentAgreement_even_eq_two_mul B ρ Pf hρ0 h2

/-- **[descent, weight-2 even-even spine]** Exact shifted binomial fiber count for the
symmetric weight-2 spine: the count is `gcd(#G,c)` when the target is a `c`-th power and `0`
otherwise. -/
theorem doorIV_weight2_evenSpine_card_eq_if_mem_range_export {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] [IsCyclic G] (c : ℕ) (w : G) :
    (Finset.univ.filter (fun y : G => y ^ c = w)).card
      = if w ∈ (_root_.powMonoidHom c : G →* G).range then (Nat.card G).gcd c else 0 :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.card_pow_eq_target_eq_if_mem_range c w

/-- **[descent, weight-2 even-even spine]** Reachable-target consumer form: when the target is a
`c`-th power, the symmetric spine count is exactly the kernel size `gcd(#G,c)`. -/
theorem doorIV_weight2_evenSpine_card_eq_gcd_export {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] [IsCyclic G] (c : ℕ) (w : G)
    (hw : w ∈ (_root_.powMonoidHom c : G →* G).range) :
    (Finset.univ.filter (fun y : G => y ^ c = w)).card = (Nat.card G).gcd c :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.card_pow_eq_target_eq_gcd_of_mem_range c w hw

/-- **[descent, weight-2 even-even spine]** Off-range consumer form: if the target is not a
`c`-th power, the symmetric spine count is exactly zero. -/
theorem doorIV_weight2_evenSpine_card_eq_zero_export {G : Type*} [CommGroup G]
    [Fintype G] [DecidableEq G] [IsCyclic G] (c : ℕ) (w : G)
    (hw : w ∉ (_root_.powMonoidHom c : G →* G).range) :
    (Finset.univ.filter (fun y : G => y ^ c = w)).card = 0 :=
  _root_.ArkLib.ProximityGap.EvenOddDescent.card_pow_eq_target_eq_zero_of_not_mem_range c w hw

#print axioms doorIV_descent_quadform_degreeEnvelope_export
#print axioms doorIV_descent_Z_card_le_degreeEnvelope_export
#print axioms doorIV_descent_Z_indicator_sum_le_degreeEnvelope_export
#print axioms doorIV_descent_Z_card_le_degBound_export
#print axioms doorIV_descent_Z_indicator_sum_le_degBound_export
#print axioms doorIV_descentAgreement_even_eq_two_mul_export
#print axioms doorIV_weight2_evenSpine_card_eq_if_mem_range_export
#print axioms doorIV_weight2_evenSpine_card_eq_gcd_export
#print axioms doorIV_weight2_evenSpine_card_eq_zero_export

/-- **[obstruction, WorstBHalfMass]** At two-piece coherence one with positive denominator, the
period magnitude equals the half-mass exactly. Thus the cross-half coherence factor contributes no
saving. -/
theorem doorIV_worstB_norm_add_eq_halfMass_of_coherence_one_export {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E] {A B : E}
    (hden : 0 < ‖A‖ + ‖B‖)
    (hρ : _root_.ProximityGap.Frontier.DoorIVComplexRayCoherence.twoPieceNormCoherence A B = 1) :
    ‖A + B‖ = ‖A‖ + ‖B‖ :=
  _root_.ProximityGap.Frontier.DoorIVWorstBHalfMassCarriesAll.norm_add_eq_halfMass_of_coherence_one
    hden hρ

/-- **[obstruction, WorstBHalfMass]** A strict magnitude saving below half-mass requires the two
canonical halves to be non-`SameRay`; same-ray worst-b halves rule out this coherence-saving lever. -/
theorem doorIV_worstB_not_sameRay_of_magnitude_lt_halfMass_export {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E] {A B : E}
    (hlt : ‖A + B‖ < ‖A‖ + ‖B‖) :
    ¬ _root_.SameRay ℝ A B :=
  _root_.ProximityGap.Frontier.DoorIVWorstBHalfMassCarriesAll.not_sameRay_of_magnitude_lt_halfMass hlt

/-- **[obstruction, WorstBHalfMass]** Positive-half-mass capstone: saturated two-piece coherence
`ρ=1` is equivalent to equality of period magnitude and half-mass. -/
theorem doorIV_worstB_coherence_one_iff_magnitude_eq_halfMass_export {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E] {A B : E}
    (hden : 0 < ‖A‖ + ‖B‖) :
    _root_.ProximityGap.Frontier.DoorIVComplexRayCoherence.twoPieceNormCoherence A B = 1 ↔
      ‖A + B‖ = ‖A‖ + ‖B‖ :=
  _root_.ProximityGap.Frontier.DoorIVWorstBHalfMassCarriesAll.coherence_one_iff_magnitude_eq_halfMass
    hden

/-- **[obstruction, WorstBHalfMass]** Positive-half-mass epsilon budget: a coherence saving
`ρ ≤ 1 - ε` is exactly an `ε·H` lower bound on the strict-triangle deficit. -/
theorem doorIV_worstB_eps_halfMass_deficit_iff_export {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [StrictConvexSpace ℝ E] {A B : E}
    (hden : 0 < ‖A‖ + ‖B‖) (ε : ℝ) :
    _root_.ProximityGap.Frontier.DoorIVComplexRayCoherence.twoPieceNormCoherence A B ≤ 1 - ε ↔
      ε * (‖A‖ + ‖B‖) ≤ (‖A‖ + ‖B‖) - ‖A + B‖ :=
  _root_.ProximityGap.Frontier.DoorIVWorstBHalfMassCarriesAll.coherence_le_one_sub_eps_iff_eps_halfMass_le_deficit
    hden ε

/-- **[obstruction, CoherenceSaturationInsufficient]** Under coherence saturation (`M = H`), the
prize-shaped bound is exactly a half-mass bound: `M ≤ C·prizeScale n L ↔ H ≤ C·prizeScale n L`. The
entire prize task transfers onto bounding the half-mass; the index-2 coherence object contributes
nothing. (Probe `probe_dooriv_worstb_coherence_deficit_law.py`: `ρ(b*) ≡ 1`.) -/
theorem doorIV_coherenceSaturation_prizeBound_iff_halfMassBound_export {M H C n L : ℝ}
    (hsat : M = H) :
    M ≤ C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L ↔
      H ≤ C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceSaturationInsufficient.prizeBound_iff_halfMassBound_of_saturation
    hsat

/-- **[obstruction, CoherenceSaturationInsufficient]** In the thin prize regime
(`prizeScale n L < n`, i.e. `√(n·L) < n ⟺ L < n`) any prize constant `0 < C ≤ 1` makes the prize
target strictly below the trivial half-mass ceiling `n`. So coherence saturation supplies none of the
prize gap; the whole burden is a strict-sub-trivial bound on the half-mass (the self-similar
descent). -/
theorem doorIV_coherenceSaturation_prizeTarget_lt_trivial_ceiling_export {C n L : ℝ}
    (hscale : _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L < n)
    (hC0 : 0 < C) (hC1 : C ≤ 1) :
    C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L < n :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceSaturationInsufficient.prizeTarget_lt_trivial_ceiling
    hscale hC0 hC1

/-- **[obstruction, CoherenceSaturationInsufficient]** Under coherence saturation, any measured
half-mass excess over the prize target immediately refutes the corresponding prize bound for `M`.
This is the contrapositive probe-facing form: once `ρ(b*) = 1`, cross-half coherence cannot rescue an
over-budget half-mass. -/
theorem doorIV_coherenceSaturation_halfMass_excess_refutes_prize_export {M H C n L : ℝ}
    (hsat : M = H)
    (hH : C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L < H) :
    ¬ M ≤ C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L := by
  intro hM
  have hHle : H ≤ C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L :=
    (_root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceSaturationInsufficient.prizeBound_iff_halfMassBound_of_saturation
      hsat).mp hM
  exact not_le_of_gt hH hHle

/-- **[obstruction, CoherenceSaturationInsufficient]** Coherence-insufficiency transfer capstone:
at coherence saturation (`M = H`) with the trivial ceiling (`H ≤ n`) in the thin prize regime
(`prizeScale n L < n`), for any prize constant `0 < C ≤ 1` the prize-shaped bound is exactly a
strict-sub-trivial half-mass bound. The kerneled form of the probe verdict
`ρ(b*) ≡ 1 ≫ ρ_needed = √(n·L)/n` ⟹ COHERENCE-INSUFFICIENT: the prize burden lives entirely on the
half-mass descent, not the index-2 coherence object. -/
theorem doorIV_coherenceSaturation_transfers_to_strict_subTrivial_halfMass_export
    {M H C n L : ℝ}
    (hsat : M = H) (hceil : H ≤ n)
    (hscale : _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L < n)
    (hC0 : 0 < C) (hC1 : C ≤ 1) :
    (M ≤ C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L ↔
        H ≤ C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L) ∧
      C * _root_.ArkLib.ProximityGap.Frontier.ShawValueCapstone.prizeScale n L < n :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceSaturationInsufficient.coherenceSaturation_transfers_to_strict_subTrivial_halfMass
    hsat hceil hscale hC0 hC1

#print axioms doorIV_worstB_norm_add_eq_halfMass_of_coherence_one_export
#print axioms doorIV_worstB_not_sameRay_of_magnitude_lt_halfMass_export
#print axioms doorIV_worstB_coherence_one_iff_magnitude_eq_halfMass_export
#print axioms doorIV_worstB_eps_halfMass_deficit_iff_export
#print axioms doorIV_coherenceSaturation_prizeBound_iff_halfMassBound_export
#print axioms doorIV_coherenceSaturation_prizeTarget_lt_trivial_ceiling_export
#print axioms doorIV_coherenceSaturation_halfMass_excess_refutes_prize_export
#print axioms doorIV_coherenceSaturation_transfers_to_strict_subTrivial_halfMass_export

/-- **[obstruction, FractionalMomentNoMaxGain]** The moment-to-max envelope multiplier `c^{1/r}`
(`c = card s`) is ANTITONE in moment depth `r`: a deeper moment gives a tighter overshoot. This is
the direction in Shaw's probe `(N·A_q)^{1/(2q)}` decreasing in `q`. -/
theorem doorIV_envelope_multiplier_antitone_export {c : ℝ} (hc : 1 ≤ c)
    {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₁₂ : r₁ ≤ r₂) :
    c ^ ((1 : ℝ) / r₂) ≤ c ^ ((1 : ℝ) / r₁) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVFractionalMomentNoMaxGain.envelope_multiplier_antitone
    hc hr₁ hr₁₂

/-- **[obstruction, FractionalMomentNoMaxGain]** No max-gain from a smaller moment: for nonempty `s`
and `0 ≤ M`, the high-moment max-envelope `(card s)^{1/r₂}·M` is `≤` the low-moment one
`(card s)^{1/r₁}·M`. Dropping to the fractional / Harper `q<1` regime cannot tighten the worst-case
max bound — the average-vs-max obstruction in kerneled form. -/
theorem doorIV_no_maxGain_from_smaller_moment_export {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    {M : ℝ} (hM : 0 ≤ M) {r₁ r₂ : ℕ} (hr₁ : 1 ≤ r₁) (hr₁₂ : r₁ ≤ r₂) :
    (s.card : ℝ) ^ ((1 : ℝ) / r₂) * M ≤ (s.card : ℝ) ^ ((1 : ℝ) / r₁) * M :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVFractionalMomentNoMaxGain.no_maxGain_from_smaller_moment
    s hs hM hr₁ hr₁₂

#print axioms doorIV_envelope_multiplier_antitone_export
#print axioms doorIV_no_maxGain_from_smaller_moment_export

/-- **[obstruction, GeomMeanBelowMax]** The arithmetic mean / density average lies at or below the
max. This kernels the murmuration-density half of the average-not-max obstruction: an additive
average can witness typical behavior, but it does not control the adversarial worst frequency. -/
theorem doorIV_arithMean_le_max_export {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (lam : ι → ℝ) {M : ℝ} (hM : ∀ i ∈ s, lam i ≤ M) :
    (∑ i ∈ s, lam i) / (s.card : ℝ) ≤ M :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.arithMean_le_max s hs lam hM

/-- **[obstruction, GeomMeanBelowMax]** Uniform arithmetic/density averages above a threshold
expose an entry above that threshold. Density excess is a lower witness for the max, not an upper
control of the adversarial worst frequency. -/
theorem doorIV_arithMean_gt_forces_point_gt_export {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (lam : ι → ℝ) {C : ℝ} (hgt : C < (∑ i ∈ s, lam i) / (s.card : ℝ)) :
    ∃ i ∈ s, C < lam i :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.exists_gt_of_lt_arithMean
    s hs lam hgt

/-- **[obstruction, GeomMeanBelowMax]** Probability-weighted density averages also lie below the
max. This strengthens the murmuration-density obstruction from uniform averages to arbitrary finite
probability weights: changing the averaging measure does not control the adversarial worst frequency. -/
theorem doorIV_weightedMean_le_max_export {ι : Type*} (s : Finset ι) (w lam : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) (hw_sum : (∑ i ∈ s, w i) = 1)
    {M : ℝ} (hM : ∀ i ∈ s, lam i ≤ M) :
    ∑ i ∈ s, w i * lam i ≤ M :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.weightedMean_le_max
    s w lam hw_nonneg hw_sum hM

/-- **[obstruction, GeomMeanBelowMax]** Subprobability-weighted density averages still lie below the
max when `0 ≤ M`. Truncating or thinning the averaging window cannot turn an average-side statistic
into a worst-case max bound. -/
theorem doorIV_weightedSubmean_le_max_export {ι : Type*} (s : Finset ι) (w lam : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) (hw_sum : (∑ i ∈ s, w i) ≤ 1)
    {M : ℝ} (hM_nonneg : 0 ≤ M) (hM : ∀ i ∈ s, lam i ≤ M) :
    ∑ i ∈ s, w i * lam i ≤ M :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.weightedSubmean_le_max
    s w lam hw_nonneg hw_sum hM_nonneg hM

/-- **[obstruction, GeomMeanBelowMax]** Probability-weighted averages that beat a threshold expose
an entry above the same threshold. Average-side murmuration/density evidence is a lower witness for
`max`, not an upper-control mechanism for the adversarial frequency. -/
theorem doorIV_weightedMean_gt_forces_point_gt_export {ι : Type*} (s : Finset ι) (w lam : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) (hw_sum : (∑ i ∈ s, w i) = 1)
    {C : ℝ} (hgt : C < ∑ i ∈ s, w i * lam i) :
    ∃ i ∈ s, C < lam i :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.exists_gt_of_lt_weightedMean
    s w lam hw_nonneg hw_sum hgt

/-- **[obstruction, GeomMeanBelowMax]** Subprobability-weighted averages above a nonnegative
threshold still expose an entry above that threshold. Truncation does not create hidden worst-case
upper control. -/
theorem doorIV_weightedSubmean_gt_forces_point_gt_export {ι : Type*} (s : Finset ι) (w lam : ι → ℝ)
    (hw_nonneg : ∀ i ∈ s, 0 ≤ w i) (hw_sum : (∑ i ∈ s, w i) ≤ 1)
    {C : ℝ} (hC_nonneg : 0 ≤ C) (hgt : C < ∑ i ∈ s, w i * lam i) :
    ∃ i ∈ s, C < lam i :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.exists_gt_of_lt_weightedSubmean
    s w lam hw_nonneg hw_sum hC_nonneg hgt

/-- **[obstruction, GeomMeanBelowMax]** The geometric mean (Mahler-measure / log-average) of the
nonnegative spectrum lies at or below the max: `(∏_{i∈s} lam i)^{1/card s} ≤ M` for `lam i ≤ M` on a
nonempty `s`. Kernels the (b)/(d) literature-cluster verdict (murmuration density / Mahler measure are
AVERAGE objects, the wrong side of the worst-case max). -/
theorem doorIV_geomMean_le_max_export {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (lam : ι → ℝ)
    (hnn : ∀ i ∈ s, 0 ≤ lam i) {M : ℝ} (hM : ∀ i ∈ s, lam i ≤ M) :
    (∏ i ∈ s, lam i) ^ ((1 : ℝ) / s.card) ≤ M :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.geomMean_le_max s hs lam hnn hM

/-- **[obstruction, GeomMeanBelowMax]** A Mahler/geometric-mean excess above a threshold exposes
an entry above that threshold. The log-average object is a lower witness for the worst conjugate,
not an upper-control mechanism for the adversarial max. -/
theorem doorIV_geomMean_gt_forces_point_gt_export {ι : Type*} (s : Finset ι) (hs : s.Nonempty)
    (lam : ι → ℝ) (hnn : ∀ i ∈ s, 0 ≤ lam i) {C : ℝ}
    (hgt : C < (∏ i ∈ s, lam i) ^ ((1 : ℝ) / s.card)) :
    ∃ i ∈ s, C < lam i :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVGeomMeanBelowMax.exists_gt_of_lt_geomMean
    s hs lam hnn hgt

/-- **[obstruction, DoorIVOrderedWalkMajorant]** DIR9 ordered-walk scaffold: the endpoint
norm is bounded by the finite maximal prefix excursion. This makes the ordered Doob/van-der-Corput
object a genuine majorant of the Gauss-period endpoint while making no cancellation claim. -/
theorem doorIV_orderedWalk_endpoint_le_maximalExcursion_export
    {E : Type*} [SeminormedAddCommGroup E] (S : ℕ → E) (n : ℕ) :
    ‖S n‖ ≤
      _root_.ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.maximalExcursion S n :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.endpoint_norm_le_maximalExcursion
    S n

/-- **[obstruction, DoorIVOrderedWalkMajorant]** Consumer form for DIR9: any uniform bound on the
ordered maximal prefix excursion immediately bounds the Gauss-period endpoint. The whole analytic
content remains proving the maximal-excursion bound. -/
theorem doorIV_orderedWalk_endpoint_bound_of_maximal_bound_export
    {E : Type*} [SeminormedAddCommGroup E] {S : ℕ → E} {n : ℕ} {C : ℝ}
    (h : _root_.ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.maximalExcursion S n ≤ C) :
    ‖S n‖ ≤ C :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.endpoint_bound_of_maximalExcursion_bound h

/-- **[obstruction, AvDIR9OrderedWalkMajorant]** In the ordered-walk formulation, the endpoint
period is one of the prefixes, so its norm is dominated by the maximal excursion `R`. -/
theorem doorIV_avDIR9_endpoint_le_R_export {n : ℕ} (a : Fin n → ℂ) :
    ‖_root_.ArkLib.ProximityGap.Frontier.AvDIR9.endpoint a‖ ≤
      _root_.ArkLib.ProximityGap.Frontier.AvDIR9.R a :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9.endpoint_le_R a

/-- **[obstruction, AvDIR9OrderedWalkMajorant]** Per-pair summed cancellation of the ordered
signed-area contributions forces the whole signed-area family sum to vanish. This is a global
phase-blind statement only, not per-worst-frequency cancellation. -/
theorem doorIV_avDIR9_pairAntisym_sum_zero_export {n : ℕ} {B : Type*} [Fintype B]
    (c : B → Fin n → Fin n → ℝ) (hpair : ∀ k l, ∑ b, c b k l = 0) :
    ∑ b, ((1 / 2 : ℝ) *
      ∑ k : Fin n, ∑ l ∈ Finset.univ.filter (fun l : Fin n => (l : ℕ) < (k : ℕ)), c b k l) = 0 :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9.pairAntisym_sum_zero c hpair

/-- **[obstruction, AvDIR9OrderedWalkMajorant]** The abstract DIR9 reduction theorem is exactly
`endpoint≤R`: the unconditional handle is the majorant direction, not a new upper bound. -/
theorem doorIV_avDIR9_majorant_reduces_export :
    _root_.ArkLib.ProximityGap.Frontier.AvDIR9.DIR9MajorantReducesToWall :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9.dir9_majorant_reduces

/-- **[obstruction, JacAutocorrL2SupGap]** Complex Wiener-Khinchin identity for the cyclic
Jacobi/Gauss-sum autocorrelation: the autocorrelation L2 mass equals the convolution L2 mass. -/
theorem doorIV_jacAutocorr_wienerKhinchin_export {m : ℕ} [NeZero m]
    (g : ZMod m → ℂ) :
    ∑ s : ZMod m,
        ‖_root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.cyclicAutocorr g s‖ ^ 2 =
      ∑ d : ZMod m,
        ‖_root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.cyclicConv g d‖ ^ 2 :=
  _root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.sum_normSq_autocorr_eq_sum_normSq_conv g

/-- **[obstruction, JacAutocorrL2SupGap]** The exact L2-to-sup control for one off-diagonal
Jacobi autocorrelation term is the whole off-diagonal L2 mass, i.e. the route loses the square-root
number of shifts unless a new flatness theorem is supplied. -/
theorem doorIV_jacAutocorr_offdiag_le_total_sub_diag_export {m : ℕ} [NeZero m]
    (g : ZMod m → ℂ) {s : ZMod m} (hs : s ≠ 0) :
    ‖_root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.cyclicAutocorr g s‖ ^ 2
      ≤ (∑ d : ZMod m,
          ‖_root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.cyclicConv g d‖ ^ 2) -
        ‖_root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.cyclicAutocorr g 0‖ ^ 2 :=
  _root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.normSq_autocorr_le_total_sub_diag g hs

/-- **[prize-bridge, JacAutocorrL2SupGap]** The named autocorrelation flatness residual removes the
L2-to-sup square-root loss and yields the per-shift prize-shape bound. The residual itself is the open
Door-IV wall, not asserted here. -/
theorem doorIV_jacAutocorr_gap_suffices_export {m : ℕ} [NeZero m] {C : ℝ}
    (g : ZMod m → ℂ) (hm : 2 ≤ m)
    (hgap : _root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.AutocorrL2SupGap C g)
    {s : ZMod m} (hs : s ≠ 0) :
    ‖_root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.cyclicAutocorr g s‖ ^ 2
      ≤ (C * Real.log m / ((m : ℝ) - 1))
          * (∑ t ∈ (Finset.univ.erase (0 : ZMod m)),
              ‖_root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.cyclicAutocorr g t‖ ^ 2) :=
  _root_.ArkLib.ProximityGap.Frontier.JAC1SecondMoment.normSq_autocorr_le_of_gap g hm hgap hs

/-- **[obstruction, AvERG]** Periodic ergodic sums have exact drift by the endpoint period:
there is no new infinite-time cancellation regime beyond the single Door-IV window. -/
theorem doorIV_avERG_drift_export (a : ℕ → ℂ) (n : ℕ)
    (hper : ∀ j, a (j + n) = a j) (k : ℕ) :
    _root_.ArkLib.ProximityGap.Frontier.AvERG.ergodicSum a (n + k) =
      _root_.ArkLib.ProximityGap.Frontier.AvERG.ergodicSum a k +
        _root_.ArkLib.ProximityGap.Frontier.AvERG.periodSum a n :=
  _root_.ArkLib.ProximityGap.Frontier.AvERG.drift a n hper k

/-- **[obstruction, AvERG]** At the prize relation `p = n^4`, the deterministic
Rademacher-Menshov maximal scale exceeds the prize scale for `n ≥ 55`; the route loses a real
`sqrt(log n)` factor. -/
theorem doorIV_avERG_rmScale_gt_prizeScale_export (n : ℕ) (hn : 55 ≤ n) :
    _root_.ArkLib.ProximityGap.Frontier.AvERG.prizeScale n <
      _root_.ArkLib.ProximityGap.Frontier.AvERG.rmScale n :=
  _root_.ArkLib.ProximityGap.Frontier.AvERG.rmScale_gt_prizeScale n hn

/-- **[obstruction, AvERG]** The ergodic/dynamical maximal-function angle reduces to the wall:
zero-entropy drift plus Rademacher-Menshov scale loss are the exact unconditional certificate. -/
theorem doorIV_avERG_ergodic_maximal_reduces_export :
    _root_.ArkLib.ProximityGap.Frontier.AvERG.ErgodicMaximalReducesToWall :=
  _root_.ArkLib.ProximityGap.Frontier.AvERG.ergodic_maximal_reduces

/-- **[obstruction, PhaseBlindRadialStats]** Every finite `normSq`-radial statistic is invariant
under arbitrary pointwise unit twists. This is the kerneled radial side of Shaw's phase-blindness
probe: a `b`-summed moment/radial summary cannot see the adversarial phase alignment Door (iv) needs. -/
theorem doorIV_radialSum_invariant_under_unit_twist_export {ι : Type*} (s : Finset ι)
    (F : ℝ → ℝ) (tw A : ι → ℂ) (htw : ∀ i ∈ s, Complex.normSq (tw i) = 1) :
    (∑ i ∈ s, F (Complex.normSq (tw i * A i))) =
      ∑ i ∈ s, F (Complex.normSq (A i)) :=
  _root_.ArkLib.ProximityGap.Frontier.DoorIVPhaseBlindRadialStats.radialSum_invariant_under_unit_twist
    s F tw A htw

/-- **[capstone, OrderedWalkDoobMajorant]** DIR9 ordered-walk consumer: if the ordered maximal
excursion radius `R` dominates the endpoint period at every family member, then a prize-scale theorem
for `R` transfers verbatim to the endpoint periods. The remaining open obligation is the genuine
per-`b*` maximal-inequality bound for `R`, not another normalization step. -/
theorem doorIV_orderedWalk_corePrize_endpoint_of_majorant_export {ι E : Type*}
    [SeminormedAddCommGroup E] {q n : ι → ℝ} {endpoint : ι → E} {R : ι → ℝ}
    (hdom : _root_.ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.EndpointDominated endpoint R)
    (hR : _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n R) :
    _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n
      (fun i : ι => ‖endpoint i‖) :=
  _root_.ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.corePrizeBoundOn_endpoint_of_orderedWalkMajorant
    hdom hR

/-- **[obstruction, OrderedWalkDoobMajorant]** Contrapositive DIR9 form: if the endpoint periods are
not prize-bounded, then no pointwise-dominating ordered-walk radius can be prize-bounded either. Thus
an ordered-walk/Doob route must prove a bound as strong as the original Paley/BGK wall. -/
theorem doorIV_orderedWalk_not_radius_bound_of_endpoint_not_bound_export {ι E : Type*}
    [SeminormedAddCommGroup E] {q n : ι → ℝ} {endpoint : ι → E} {R : ι → ℝ}
    (hdom : _root_.ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.EndpointDominated endpoint R)
    (hnot : ¬ _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n
      (fun i : ι => ‖endpoint i‖)) :
    ¬ _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n R :=
  _root_.ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.not_corePrizeBoundOn_radius_of_endpoint_not_core
    hdom hnot

/-- **[capstone, OrderedWalkDoobMajorant]** Concrete finite-prefix DIR9 consumer: a prize-scale
bound for the ordered maximal excursion `max_{k≤N_i} ‖S_i k‖` transfers to the endpoint periods
`‖S_i N_i‖`. This composes the finite prefix-max scaffold with the Shaw prize predicate. -/
theorem doorIV_orderedWalk_corePrize_endpoint_of_maximalExcursion_export {ι E : Type*}
    [SeminormedAddCommGroup E] {q n : ι → ℝ} {S : ι → ℕ → E} {N : ι → ℕ}
    (hR : _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n
      (fun i : ι => _root_.ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.maximalExcursion
        (S i) (N i))) :
    _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n
      (fun i : ι => ‖S i (N i)‖) :=
  _root_.ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.corePrizeBoundOn_endpoint_of_maximalExcursion_bound
    hR

/-- **[obstruction, OrderedWalkDoobMajorant]** Concrete contrapositive: if the endpoint
periods are not prize-bounded, then the finite ordered maximal-prefix excursion cannot be
prize-bounded either. -/
theorem doorIV_orderedWalk_not_maximalExcursion_bound_of_endpoint_not_bound_export {ι E : Type*}
    [SeminormedAddCommGroup E] {q n : ι → ℝ} {S : ι → ℕ → E} {N : ι → ℕ}
    (hnot : ¬ _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n
      (fun i : ι => ‖S i (N i)‖)) :
    ¬ _root_.ProximityGap.Frontier.ShawValueCapstone.CorePrizeBoundOn q n
      (fun i : ι => _root_.ArkLib.ProximityGap.Frontier.DoorIVOrderedWalkMajorant.maximalExcursion
        (S i) (N i)) :=
  _root_.ProximityGap.Frontier.DoorIVOrderedWalkDoobMajorant.not_corePrizeBoundOn_maximalExcursion_of_endpoint_not_core
    hnot

/-- **[obstruction, StepanovAtBstar]** Per-`b*` Stepanov supplies only the counting
inequality: if a nonzero auxiliary vanishes to order `M` on the major-arc set `B`, then
`M * |B| ≤ deg F`. -/
theorem doorIV_stepanov_bstar_bound_export {F : Type*} [Field F]
    {B : Finset F} {F' : Polynomial F} {M : ℕ}
    (hF : F' ≠ 0) (hvanish : ∀ x ∈ B, (Polynomial.X - Polynomial.C x) ^ M ∣ F') :
    M * B.card ≤ F'.natDegree :=
  _root_.ProximityGap.Frontier.StepanovAtBstar.stepanov_bstar_bound hF hvanish

/-- **[obstruction, StepanovAtBstar]** A strictly sub-count per-`b*` Stepanov saving is
exactly the named `MajorArcDegenerate` obligation. The natural structured/even auxiliaries have
house=count, so closing this lane requires genuine major-arc algebraic degeneracy beyond the
measured full-rank wall. -/
theorem doorIV_bstar_saving_iff_degenerate_export {F : Type*} [Field F]
    {B : Finset F} {M : ℕ} :
    _root_.ProximityGap.Frontier.StepanovAtBstar.MajorArcDegenerate B M ↔
      ∃ F' : Polynomial F, F' ≠ 0 ∧
        (∀ x ∈ B, (Polynomial.X - Polynomial.C x) ^ M ∣ F') ∧
        F'.natDegree < M * B.card :=
  _root_.ProximityGap.Frontier.StepanovAtBstar.bstar_saving_iff_degenerate

/-- **[obstruction, AvDIR9Reflection]** Endpoint domination for the reflection-Steinitz
ordered walk: for every ordering, the endpoint Gauss period is one of the finite prefixes, so
`‖η_b‖ ≤ R`. This is the wall-facing direction: any bound on the ordered maximal function must
already bound the endpoint period itself. -/
theorem doorIV_avDIR9Reflection_endpoint_le_R_export (a : ℕ → ℂ) (n : ℕ) :
    ‖_root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.endpoint a n‖ ≤
      _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.R a n :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.endpoint_le_R a n

/-- **[obstruction, AvDIR9Reflection]** Endpoint specialization of the antipodal reflection
identity: the full endpoint is `S_h + conj(S_h)`, so the reflection lane exposes the half-period
partial Gauss sum rather than eliminating it. -/
theorem doorIV_avDIR9Reflection_endpoint_id_export {a : ℕ → ℂ} {h : ℕ}
    (hanti : _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.AntipodalIncrements a h) :
    _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.endpoint a (2 * h) =
      _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.S a h +
        (starRingEnd ℂ) (_root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.S a h) :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.endpoint_reflection_id hanti

/-- **[obstruction, AvDIR9Reflection]** Endpoint-only reflection bound `‖η_b‖ ≤ 2·R₁`.
This is a wall certificate, not a prize upper bound, because `R₁` contains the half-period partial
Gauss sum. -/
theorem doorIV_avDIR9Reflection_endpoint_norm_le_two_R1_export {a : ℕ → ℂ} {h : ℕ}
    (hanti : _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.AntipodalIncrements a h) :
    ‖_root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.endpoint a (2 * h)‖ ≤
      2 * _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.R1 a h :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.endpoint_norm_le_two_R1 hanti

/-- **[obstruction, AvDIR9Reflection]** Half-period lower wall: the reflected half-walk must
already carry at least half the endpoint norm. -/
theorem doorIV_avDIR9Reflection_half_norm_ge_endpoint_half_export {a : ℕ → ℂ} {h : ℕ}
    (hanti : _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.AntipodalIncrements a h) :
    ‖_root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.endpoint a (2 * h)‖ / 2 ≤
      ‖_root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.S a h‖ :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.half_norm_ge_endpoint_half hanti

/-- **[obstruction, AvDIR9Reflection]** Exact antipodal reflection gives the full-walk maximal
function bound `R(2h) ≤ 2 R₁(h)`. Iterating this bound loses cancellation and recurses into the
half-scale Gauss-sum wall, so it is a reduction certificate rather than a prize upper bound. -/
theorem doorIV_avDIR9Reflection_bound_two_R1_export {a : ℕ → ℂ} {h : ℕ}
    (hanti : _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.AntipodalIncrements a h) :
    _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.R a (2 * h) ≤
      2 * _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.R1 a h :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.reflection_bound_two_R1 hanti

/-- **[obstruction, AvDIR9Reflection]** The reflection-Steinitz attack reduces to the same
endpoint wall: the permanent certificate is precisely `endpoint_le_R`, with the reflection majorant
pointing in the wrong direction for an unconditional `M` upper bound. -/
theorem doorIV_avDIR9Reflection_reduces_export :
    _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.DIR9ReflectionReducesToWall :=
  _root_.ArkLib.ProximityGap.Frontier.AvDIR9Reflection.dir9_reflection_reduces

/-- **[capstone, ShawValueBracketCenter]** The product of the normalized floor endpoint
`√n/√(nL)` and ceiling endpoint `n/√(nL)` is the closed-form midpoint datum `√n/L`. -/
theorem shawValue_bracket_endpoint_product_export {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.floorEndpoint n L *
        _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.ceilingEndpoint n L =
      Real.sqrt n / L :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.endpoint_product hn hL

/-- **[capstone, ShawValueBracketCenter]** The geometric center of the Shaw-value prize bracket has
the closed form `sqrt (sqrt n) / sqrt L`, i.e. `n^(1/4)/sqrt L`. -/
theorem shawValue_bracket_geomCenter_eq_export {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.geomCenter n L =
      Real.sqrt (Real.sqrt n) / Real.sqrt L :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.geomCenter_eq hn hL

/-- **[capstone, ShawValueBracketCenter]** The geometric center is the multiplicative midpoint of
the Shaw-value floor/ceiling bracket: `ceiling / center = center / floor`. -/
theorem shawValue_bracket_ratio_symmetric_export {n L : ℝ} (hn : 0 < n) (hL : 0 < L) :
    _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.ceilingEndpoint n L /
        _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.geomCenter n L =
      _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.geomCenter n L /
        _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.floorEndpoint n L :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.ratio_symmetric hn hL

/-- **[capstone, ShawValueBracketCenter]** For `1 ≤ n`, the geometric center is an honest point
inside the normalized Shaw-value prize bracket. -/
theorem shawValue_bracket_center_between_export {n L : ℝ} (hn : 1 ≤ n) (hL : 0 < L) :
    _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.floorEndpoint n L ≤
        _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.geomCenter n L ∧
      _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.geomCenter n L ≤
        _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.ceilingEndpoint n L :=
  _root_.ArkLib.ProximityGap.Frontier.ShawValueBracketCenter.center_between hn hL

#print axioms shawValue_bracket_endpoint_product_export
#print axioms shawValue_bracket_geomCenter_eq_export
#print axioms shawValue_bracket_ratio_symmetric_export
#print axioms shawValue_bracket_center_between_export
#print axioms doorIV_arithMean_le_max_export
#print axioms doorIV_arithMean_gt_forces_point_gt_export
#print axioms doorIV_weightedMean_le_max_export
#print axioms doorIV_weightedSubmean_le_max_export
#print axioms doorIV_weightedMean_gt_forces_point_gt_export
#print axioms doorIV_weightedSubmean_gt_forces_point_gt_export
#print axioms doorIV_geomMean_le_max_export
#print axioms doorIV_geomMean_gt_forces_point_gt_export
#print axioms doorIV_orderedWalk_endpoint_le_maximalExcursion_export
#print axioms doorIV_orderedWalk_endpoint_bound_of_maximal_bound_export
#print axioms doorIV_avDIR9_endpoint_le_R_export
#print axioms doorIV_avDIR9_pairAntisym_sum_zero_export
#print axioms doorIV_avDIR9_majorant_reduces_export
#print axioms doorIV_avDIR9Reflection_endpoint_le_R_export
#print axioms doorIV_avDIR9Reflection_endpoint_id_export
#print axioms doorIV_avDIR9Reflection_endpoint_norm_le_two_R1_export
#print axioms doorIV_avDIR9Reflection_half_norm_ge_endpoint_half_export
#print axioms doorIV_avDIR9Reflection_bound_two_R1_export
#print axioms doorIV_avDIR9Reflection_reduces_export
#print axioms doorIV_jacAutocorr_wienerKhinchin_export
#print axioms doorIV_jacAutocorr_offdiag_le_total_sub_diag_export
#print axioms doorIV_jacAutocorr_gap_suffices_export
#print axioms doorIV_avERG_drift_export
#print axioms doorIV_avERG_rmScale_gt_prizeScale_export
#print axioms doorIV_avERG_ergodic_maximal_reduces_export
#print axioms doorIV_radialSum_invariant_under_unit_twist_export
#print axioms doorIV_orderedWalk_corePrize_endpoint_of_majorant_export
#print axioms doorIV_orderedWalk_not_radius_bound_of_endpoint_not_bound_export
#print axioms doorIV_orderedWalk_corePrize_endpoint_of_maximalExcursion_export
#print axioms doorIV_orderedWalk_not_maximalExcursion_bound_of_endpoint_not_bound_export
#print axioms doorIV_stepanov_bstar_bound_export
#print axioms doorIV_bstar_saving_iff_degenerate_export
#print axioms doorIV_tannakian_twist_period_eq_original_export
#print axioms doorIV_tannakian_coprime_twisted_period_eq_original_export
#print axioms shawOOne_bddAbove_range_shawValue_export
#print axioms corePrize_bddAbove_range_shawValue_export
#print axioms corePrize_bddAbove_range_shawValue_of_pos_lt_export
#print axioms shawOOne_unbounded_shawValue_drift_export
#print axioms corePrize_unbounded_shawValue_drift_export
#print axioms corePrize_unbounded_shawValue_drift_of_pos_lt_export
#print axioms doorIV_prize_iff_shawBounded_nonneg_and_doorIV_only_export
#print axioms doorIV_remaining_gap_is_sqrtL_factor_doorIV_only_export
#print axioms doorIV_prize_iff_shawBounded_nonneg_and_floorPrizeRatio_export
#print axioms doorIV_decomposition_block_sum_common_ray_export
#print axioms doorIV_decomposition_partition_invariant_coherence_export
#print axioms doorIV_decomposition_no_partition_beats_one_export
#print axioms doorIV_multiPiece_coherence_mem_Icc_export
#print axioms doorIV_multiPiece_exact_saving_export
#print axioms doorIV_multiPiece_eps_budget_eq_export
#print axioms doorIV_multiPiece_eps_budget_iff_export
#print axioms doorIV_multiPiece_no_eps_slack_one_side_zero_export
#print axioms doorIV_multiWindow_budget_forces_card_le_export
#print axioms doorIV_no_multiWindow_split_rhs_le_strict_budget_export
#print axioms doorIV_argmaxDecoupled_const_ge_ratio_export
#print axioms doorIV_argmaxDecoupled_no_control_below_ratio_export
#print axioms doorIV_argmaxDecoupled_uniformControl_iff_ratio_export
#print axioms doorIV_argmaxDecoupled_exists_ratio_gt_no_control_export
#print axioms doorIV_argmaxDecoupled_uniformControlOn_iff_ratio_on_export
#print axioms doorIV_argmaxDecoupled_uniformControlOn_of_subset_export
#print axioms doorIV_argmaxDecoupled_no_controlOn_superset_export
#print axioms doorIV_argmaxDecoupled_exists_ratio_gt_no_controlOn_export
#print axioms doorIV_argmaxDecoupled_controlOn_constant_pos_export
#print axioms doorIV_argmaxDecoupled_point_ratio_gt_no_controlOn_export
#print axioms doorIV_argmaxDecoupled_no_absolute_constOn_export
#print axioms doorIV_argmaxDecoupled_candidate_pos_on_export
#print axioms doorIV_argmaxDecoupled_positive_support_on_subset_export
#print axioms doorIV_argmaxDecoupled_no_nonpos_candidate_controlOn_export
#print axioms doorIV_argmaxDecoupled_no_zero_candidate_controlOn_export
#print axioms doorIV_argmaxDecoupled_control_constant_pos_export
#print axioms doorIV_argmaxDecoupled_no_nonpos_candidate_control_export
#print axioms doorIV_argmaxDecoupled_no_zero_candidate_control_export
#print axioms doorIV_argmaxDecoupled_candidate_pos_export
#print axioms doorIV_argmaxDecoupled_positive_support_subset_export
#print axioms doorIV_argmaxDecoupled_no_absolute_const_export
#print axioms doorIV_prizeScale_lt_naiveIncidenceScale_of_one_lt_m_export
#print axioms doorIV_constant_lt_scaledConstant_of_one_lt_m_export
#print axioms doorIV_not_scaledConstant_le_constant_of_one_lt_m_export
#print axioms doorIV_constant_lt_scaledConstant_iff_one_lt_m_export
#print axioms doorIV_prizeScale_lt_naiveIncidenceScale_iff_one_lt_m_export
#print axioms doorIV_collision_defect_eq_zero_iff_injOn_export
#print axioms doorIV_collision_defect_pos_iff_not_injOn_export
#print axioms doorIV_sixPoint_lever_vacuous_export
#print axioms doorIV_correlation_hierarchy_no_lever_export
#print axioms doorIV_correlation_hierarchy_closed_through_six_export
#print axioms doorIV_tripleCorrelation_sixPoint_zero_export
#print axioms doorIV_tripleCorrelation_sixPoint_vacuous_export
#print axioms doorIV_tripleCorrelation_m33_eq_wick_export
#print axioms doorIV_ladder_control_passes_through_wick_export
#print axioms doorIV_whole_ladder_wick_export
#print axioms doorIV_whole_ladder_control_export
#print axioms doorIV_crossHalf_norm_add_eq_halfMass_export
#print axioms doorIV_crossHalf_fixed_multiplier_forces_ratio_le_export
#print axioms doorIV_crossHalf_fixed_multiplier_fails_of_ratio_gt_export
#print axioms doorIV_halfMassBalance_single_half_pays_floor_export
#print axioms doorIV_halfMassBalance_descent_loss_eq_two_export
#print axioms doorIV_halfMassBalance_descent_loss_le_two_export
#print axioms doorIV_halfMass_eta_image_smul_eq_eta_dilate_export
#print axioms doorIV_halfMass_eta_index_two_split_dilate_export
#print axioms doorIV_halfMass_norm_eta_le_two_dilate_export
#print axioms doorIV_sign_positiveMass_eq_negativeMass_export
#print axioms doorIV_sign_not_all_nonneg_of_positiveMass_pos_export
#print axioms doorIV_sign_exists_negative_cross_of_positiveMass_pos_export
#print axioms doorIV_sign_exists_positive_cross_of_negativeMass_pos_export
#print axioms doorIV_sign_positiveMass_le_half_card_export
#print axioms doorIV_sign_negativeMass_le_half_card_export
#print axioms doorIV_sign_positiveMass_eq_half_total_doublingMass_export
#print axioms doorIV_sign_negativeMass_eq_half_total_doublingMass_export
#print axioms doorIV_gappedMinor125_159_eq_zero_export
#print axioms doorIV_not_gappedMinor125_159_ne_zero_export
#print axioms doorIV_eighthCumulant_mixed_sign_forbids_fixed_sign_export
#print axioms doorIV_eighthCumulant_no_fixedSignCertificate_export
#print axioms doorIV_levelWorst_le_sqrt_two_pow_mul_of_xGatedRatio_export
#print axioms doorIV_levelWorst_le_prize_budget_of_xgate_export
#print axioms doorIV_gateThreshold_split_telescope_sqrt2_export
#print axioms doorIV_gateThreshold_strictly_above_clean_export
#print axioms doorIV_levelWorst_base_step_two_export
#print axioms doorIV_levelWorst_base_corrected_of_gate_export
#print axioms doorIV_strict_peak_single_coset_export
#print axioms doorIV_strict_maximizer_iff_translate_export
#print axioms doorIV_strict_peak_Ncos_eq_one_export

/-! ## Recent Door-IV capstones: resonator collapse and Rudnev/incidence stall.
Scope: **obstruction/capstone**.

These exports make the latest #444 reductions discoverable from the permanent index. The resonator
brick records that the natural Montgomery-Soundararajan resonator on `μ_n` reproduces the ordinary
moment-ratio floor; the Rudnev brick records, in exponent bookkeeping, why point-plane/sum-product
incidence savings at `β = 4` stall at the `α = 1` census wall rather than the prize `α = 1/2`.
-/

/-- **[obstruction, AvResonator]** The natural resonator on `G` gives exactly the moment-ratio
inequality `Σ‖η‖⁴ ≤ M²·Σ‖η‖²`. Thus this resonator lower-bound route factors through the already
mapped moment/DC-crossover wall; it is a lower witness, not a Door-IV upper-control mechanism. -/
theorem doorIV_resonator_one_gives_moment_floor_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) :
    (∑ b ∈ Finset.univ.erase (0 : F),
        ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ 4)
      ≤ ((Finset.univ.erase (0 : F)).sup' hne
            (fun b => ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ 2))
          * (∑ b ∈ Finset.univ.erase (0 : F),
              ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ 2) :=
  _root_.ArkLib.ProximityGap.Frontier.AvResonator.resonator_one_gives_moment_floor ψ G hne

/-- **[obstruction, RudnevPointPlaneStall]** At the prize exponent `β = 4`, the subgroup density
parameter is exactly the point-plane/sum-product threshold `θ = 1/4`. The known incidence engine is
therefore on the boundary, not in a strict-saving regime. -/
theorem doorIV_rudnev_theta_at_beta_four_export :
    _root_.ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.theta 4 = 1 / 4 :=
  _root_.ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.theta_at_beta_four

/-- **[obstruction, RudnevPointPlaneStall]** To make the incidence exponent reach the prize value
`1/2`, the saving would have to be `κ = β + r - 1`, linear in the depth `r`. Fixed point-plane /
sum-product savings cannot supply this; the remaining gap is the BGK phase-cancellation wall. -/
theorem doorIV_rudnev_prize_needs_r_linear_saving_export (β κ : ℝ) (r : ℕ) (hr : 0 < r) :
    _root_.ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.MExponent β κ r = 1 / 2 ↔
      κ = β + r - 1 :=
  _root_.ArkLib.ProximityGap.Frontier.RudnevPointPlaneStall.prize_needs_r_linear_saving β κ r hr

#print axioms doorIV_resonator_one_gives_moment_floor_export
#print axioms doorIV_rudnev_theta_at_beta_four_export
#print axioms doorIV_rudnev_prize_needs_r_linear_saving_export


/-! ## Door-IV Lane 1 rule-3 thickness-invariance exports.
Scope: **obstruction**.

These exports make the recent near-worst coherence-deficit and half-mass rule-3 negatives permanent:
if the thin and thick regime values of a scalar lever remain comparable within a factor below two,
that lever cannot supply the factor-two regime separation required of a thinness-essential CORE
route.
-/

/-- **[obstruction, DoorIVCoherenceDeficitThicknessInvariant]** If a lever's thin and thick values
are comparable within `K < 2` and the thin value is positive, then it admits no factor-two thin-side
separation. This is the reusable kernel behind the near-worst coherence-deficit rule-3 failure. -/
theorem doorIV_regimeLever_not_factor2_thin_of_comparable_export
    (L : _root_.ProximityGap.Frontier.DoorIVCoherenceDeficitThicknessInvariant.RegimeLever)
    {K : ℝ} (hK : K < 2) (hthin_pos : 0 < L.thin)
    (hcomp : L.Comparable K) : ¬ L.Factor2ThinSeparation :=
  L.not_factor2_thin_of_comparable hK hthin_pos hcomp

/-- **[obstruction, DoorIVCoherenceDeficitThicknessInvariant]** The exact probe-facing equivalence:
no factor-two thin separation is the same as `thick < 2*thin`. -/
theorem doorIV_regimeLever_no_factor2_thin_iff_export
    (L : _root_.ProximityGap.Frontier.DoorIVCoherenceDeficitThicknessInvariant.RegimeLever) :
    (¬ L.Factor2ThinSeparation) ↔ L.thick < 2 * L.thin :=
  L.no_factor2_thin_iff_thick_lt_two_thin

/-- **[obstruction, DoorIVCoherenceDeficitThicknessInvariant]** The half-mass companion:
comparability within the measured factor `1.07 < 2` forbids both thin- and thick-side factor-two
separation. The worst-`b` half-mass is therefore thickness-blind, not a thin-specific leak. -/
theorem doorIV_halfMass_lever_not_separating_either_side_export
    (L : _root_.ProximityGap.Frontier.DoorIVCoherenceDeficitThicknessInvariant.RegimeLever)
    (hthin_pos : 0 < L.thin) (hthick_pos : 0 < L.thick)
    (hcomp : L.Comparable (107 / 100 : ℝ)) :
    (¬ L.Factor2ThinSeparation) ∧ (¬ L.Factor2ThickSeparation) :=
  L.halfMass_lever_not_separating_either_side hthin_pos hthick_pos hcomp

#print axioms doorIV_regimeLever_not_factor2_thin_of_comparable_export
#print axioms doorIV_regimeLever_no_factor2_thin_iff_export
#print axioms doorIV_halfMass_lever_not_separating_either_side_export


/-! ## Door-IV Lane 1 finite coherent-argmax slack obstructions.
Scope: **obstruction**.

These exports package the probe-native finite-support wrappers for the coherent-argmax no-go: if the
observed finite argmax itself has full coherence, adding a zero-slack baseline, affine baseline, or
multiplicative normalized factor cannot rescue a slack certificate whose baseline is below the peak.
-/

open _root_.ArkLib.ProximityGap.Frontier.DoorIVCoherenceSlackVacuousAtArgmax

/-- **[obstruction, DoorIVCoherenceSlackVacuousAtArgmax]** Finite observed-argmax baseline form:
when the coherent argmax has peak mass above `g 0`, a baseline slack certificate cannot hold. -/
theorem doorIV_no_coherenceSlackWithBaseline_finsetArgmax_export {ι : Type*}
    {mass coh : ι → ℝ} {g : ℝ → ℝ} {s : Finset ι} {bstar : ι}
    (hbs : bstar ∈ s) (hmax : ∀ i ∈ s, mass i ≤ mass bstar)
    (hcoh : coh bstar = 1) (hsmall : g 0 < mass bstar) :
    ¬ CoherenceSlackBoundWithBaseline mass coh g :=
  no_coherenceSlackBoundWithBaseline_of_small_baseline_finsetArgmax
    hbs hmax hcoh hsmall

/-- **[obstruction, DoorIVCoherenceSlackVacuousAtArgmax]** Finite affine form: a below-peak
additive baseline cannot be rescued by a slack penalty at a fully coherent observed argmax. -/
theorem doorIV_no_affineCoherenceSlack_finsetArgmax_export {ι : Type*}
    {mass coh : ι → ℝ} {B : ℝ} {g : ℝ → ℝ} {s : Finset ι} {bstar : ι}
    (hbs : bstar ∈ s) (hmax : ∀ i ∈ s, mass i ≤ mass bstar)
    (hcoh : coh bstar = 1) (hsmall : B < mass bstar) :
    ¬ AffineCoherenceSlackBound mass coh B g :=
  no_affineCoherenceSlackBound_of_small_baseline_finsetArgmax
    hbs hmax hcoh hsmall

/-- **[obstruction, DoorIVCoherenceSlackVacuousAtArgmax]** Finite multiplicative form: a below-peak
baseline times a normalized slack factor cannot hold at a fully coherent observed argmax. -/
theorem doorIV_no_multiplicativeCoherenceSlack_finsetArgmax_export {ι : Type*}
    {mass coh : ι → ℝ} {B : ℝ} {g : ℝ → ℝ} {s : Finset ι} {bstar : ι}
    (hbs : bstar ∈ s) (hmax : ∀ i ∈ s, mass i ≤ mass bstar)
    (hcoh : coh bstar = 1) (hsmall : B < mass bstar) :
    ¬ MultiplicativeCoherenceSlackBound mass coh B g :=
  no_multiplicativeCoherenceSlackBound_of_small_baseline_finsetArgmax
    hbs hmax hcoh hsmall

#print axioms doorIV_no_coherenceSlackWithBaseline_finsetArgmax_export
#print axioms doorIV_no_affineCoherenceSlack_finsetArgmax_export
#print axioms doorIV_no_multiplicativeCoherenceSlack_finsetArgmax_export


/-! ## Door-IV Lane 2 floor-ladder capstone exports.
Scope: **lower-floor/capstone**.

These exports make the general moment-ratio lower-floor ladder permanent and discoverable.
They are floor statements: they certify unavoidable mass of the worst frequency, and explicitly do
not prove the CORE upper bound. The value is the citable `M² · Aᵣ ≥ Aᵣ₊₁` capstone that subsumes
`√3`, `√5`, and `√7` below the documented DC-crossover ceiling.
-/

/-- **[lower-floor, AvFloorLadder]** General abstract moment-ratio ladder: for every depth `r`,
`∑_{b≠0} ‖η_b‖^(2(r+1)) ≤ M² * ∑_{b≠0} ‖η_b‖^(2r)`, where
`M² = sup'_{b≠0} ‖η_b‖²`. This is the permanent index form of the citable `M² · Aᵣ ≥ Aᵣ₊₁`
floor capstone, not a cancellation upper bound. -/
theorem doorIV_avFloorLadder_momentSucc_le_sup_moment_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) (r : ℕ) :
    (∑ b ∈ Finset.univ.erase (0 : F),
        ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ (2 * (r + 1)))
      ≤ ((Finset.univ.erase (0 : F)).sup' hne
            (fun b => ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ 2))
          * (∑ b ∈ Finset.univ.erase (0 : F),
              ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ (2 * r)) :=
  _root_.ArkLib.ProximityGap.Frontier.AvFloorLadder.momentSucc_le_sup'_moment ψ G hne r

/-- **[lower-floor, AvFloorLadder]** General energy-form ladder: substituting the exact nonzero
moment identity gives `q*E_{r+1} - n^(2(r+1)) ≤ M² * (q*E_r - n^(2r))` for every `r`. This
packages the `√3/√5/√7/...` moment-ratio floor family under one indexed theorem. -/
theorem doorIV_avFloorLadder_energy_moment_floor_general_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    (hne : (Finset.univ.erase (0 : F)).Nonempty) (r : ℕ) :
    (Fintype.card F : ℝ) * _root_.ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G (r + 1)
        - (G.card : ℝ) ^ (2 * (r + 1))
      ≤ ((Finset.univ.erase (0 : F)).sup' hne
            (fun b => ‖_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b‖ ^ 2))
          * ((Fintype.card F : ℝ)
              * _root_.ArkLib.ProximityGap.SubgroupGaussSumMoment.rEnergy G r
              - (G.card : ℝ) ^ (2 * r)) :=
  _root_.ArkLib.ProximityGap.Frontier.AvFloorLadder.energy_moment_floor_general hψ G hne r

#print axioms doorIV_avFloorLadder_momentSucc_le_sup_moment_export
#print axioms doorIV_avFloorLadder_energy_moment_floor_general_export


/-! ## Door-IV Lane 3 sum-product/incidence census-stall exports.
Scope: **obstruction/capstone**.

These exports make the beta-four incidence-threshold obstruction permanent. They record that
newer sum-product and incidence levers either point in the wrong direction, sit on the `θ = 1/4`
boundary at beta four, or deliver only the best-case `κ = 1/15`, far short of the prize `κ = 1`.
-/

/-- **[obstruction, SumProductCensusStall]** The Stevens-de Zeeuw best-case exponent saving is
`κ = 1/15`, positive but strictly below the prize saving `κ = 1`. -/
theorem doorIV_sumProduct_sdz_does_not_reach_prize_export :
    (0 : ℝ) < 1 / 15 ∧ (1 : ℝ) / 15 < 1 :=
  _root_.ArkLib.ProximityGap.SP0Scratch.sdz_does_not_reach_prize

/-- **[obstruction, SumProductCensusStall]** At beta four the point-plane/SdZ threshold is exactly
met, not strictly exceeded: `¬ (1/4 > 1/4)`. Thus the strict-saving incidence engine is boundary
blocked in the prize regime. -/
theorem doorIV_sumProduct_pointplane_boundary_beta4_export :
    ¬ ((1 : ℝ) / 4 > 1 / 4) :=
  _root_.ArkLib.ProximityGap.SP0Scratch.pointplane_threshold_boundary_at_beta4

/-- **[obstruction, SumProductCensusStall]** The census-stall capstone: all `0 ≤ κ < 1` savings are
vacuous for the prize target, `κ = 1/15` is in that vacuous range, and the prize `κ = 1` is not
delivered by the cluster. -/
theorem doorIV_sumProduct_census_stall_confirmed_export :
    (∀ κ : ℝ, 0 ≤ κ → κ < 1 →
        _root_.ArkLib.ProximityGap.SP0Scratch.SumProductEnergyVacuousAtBeta4 κ) ∧
      _root_.ArkLib.ProximityGap.SP0Scratch.SumProductEnergyVacuousAtBeta4 (1 / 15) ∧
      ¬ _root_.ArkLib.ProximityGap.SP0Scratch.SumProductEnergyVacuousAtBeta4 1 :=
  _root_.ArkLib.ProximityGap.SP0Scratch.census_stall_confirmed

/-- **[obstruction, SumProductCensusStall]** Kurihara-style valuation data does not determine the
archimedean energy count: the same total count can be compatible with energies `T` and `T²`, and for
`T ≥ 2` these differ strictly. -/
theorem doorIV_kurihara_valuation_not_count_export (T : ℝ) (hT : 2 ≤ T) : T < T ^ 2 :=
  _root_.ArkLib.ProximityGap.SP0Scratch.kurihara_is_valuation_not_count T hT

#print axioms doorIV_sumProduct_sdz_does_not_reach_prize_export
#print axioms doorIV_sumProduct_pointplane_boundary_beta4_export
#print axioms doorIV_sumProduct_census_stall_confirmed_export
#print axioms doorIV_kurihara_valuation_not_count_export


/-! ## Door-IV Lane 3 every-angle failure-step exports.
Scope: **obstruction/capstone**.

These exports make the newest exact failure-step certificates permanent and discoverable. They are
not new moment grinding and not CORE upper bounds: the SOS export pins the finite `n = 16` Hankel
obstruction to a uniform SOS certificate; the depth export pins why the sum-product cluster is
confined to a vacuous depth-2 input at `β = 4`; the monodromy export pins that every `b`-summed
correlation remains an abelian lattice count, so the A5 non-abelian-growth escape has no sheaf to
apply to.
-/

/-- **[obstruction, A1SOSLadderN16]** At the exact Fermat-prime `n = 16`, `q = 65537` witness,
the integral Wick-deficit Hankel minor `d̃₁*d̃₃ - d̃₂^2` is strictly negative. Thus the true
per-depth deficits are not a positive-measure moment sequence, blocking a single degree-extending
SOS/Gram certificate in the moment degree. -/
theorem doorIV_A1SOS_hankel_minor2_negative_export :
    _root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.dTilde 1
        * _root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.dTilde 3
      - _root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.dTilde 2 ^ 2 < 0 :=
  _root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.hankel_minor2_negative

/-- **[obstruction, A1SOSLadderN16]** The exact `n = 16`, `q = 65537` beta-four window sanity:
`n^4 ≤ q` and `n ∣ q-1`. This keeps the SOS/Hankel witness inside the proper thin-prime regime,
not the full-group false-positive regime. -/
theorem doorIV_A1SOS_window_export :
    _root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.n ^ 4
        ≤ _root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.q ∧
      _root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.n ∣
        (_root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.q - 1) :=
  _root_.ArkLib.ProximityGap.Frontier.A1SOSLadderN16.window

/-- **[obstruction, A3DepthConfinement]** The capstone depth mismatch: at beta four, the native
sum-product/depth-2 engine is vacuous even with optimal `E₂`, remains vacuous for any `E₂` exponent
`a ≥ 2`, and Wick-fed saving starts only after depth four. This is the exact depth/order mismatch
that prevents a second-energy sum-product input from being the prize mechanism. -/
theorem doorIV_A3_depth_order_mismatch_export :
    (1 : ℝ) < _root_.ArkLib.ProximityGap.Frontier.A3DepthConfinement.momentEngineExp 4 2 2 ∧
    (∀ a : ℝ, 2 ≤ a →
      (1 : ℝ) < _root_.ArkLib.ProximityGap.Frontier.A3DepthConfinement.momentEngineExp 4 a 2) ∧
    (_root_.ArkLib.ProximityGap.Frontier.A3DepthConfinement.wickFedExp 4 = 1 ∧
      ∀ r : ℝ, 4 < r →
        _root_.ArkLib.ProximityGap.Frontier.A3DepthConfinement.wickFedExp r < 1) :=
  _root_.ArkLib.ProximityGap.Frontier.A3DepthConfinement.depth_order_mismatch

/-- **[obstruction, A5TwistedMonodromy]** Every `b`-summed Gauss-period correlation is a `q` times
an integer lattice count with zero imaginary part, uniformly in all orders. Hence the proposed
A5 growing non-abelian monodromy route has no non-abelian `√q` contribution to exploit. -/
theorem doorIV_A5_monodromy_abelian_all_orders_export
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) :
    ∀ a c : ℕ, ∃ N : ℕ,
      (∑ b : F,
          _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b ^ a
            * (starRingEnd ℂ)
                (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b ^ c))
        = (Fintype.card F : ℂ) * (N : ℂ) ∧
      (∑ b : F,
          _root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b ^ a
            * (starRingEnd ℂ)
                (_root_.ArkLib.ProximityGap.SubgroupGaussSumSecondMoment.eta ψ G b ^ c)).im = 0 :=
  _root_.ArkLib.ProximityGap.Frontier.A5TwistedMonodromyAbelianVerdict.monodromy_abelian_all_orders hψ G

#print axioms doorIV_A1SOS_hankel_minor2_negative_export
#print axioms doorIV_A1SOS_window_export
#print axioms doorIV_A3_depth_order_mismatch_export
#print axioms doorIV_A5_monodromy_abelian_all_orders_export

end ArkLib.ProximityGap.Frontier.CampaignProvenIndex
