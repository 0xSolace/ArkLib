# ArkLib open-math issue triage (2026-06-07)

Systematic review of all 12 open issues at github.com/lalalune/ArkLib/issues against the
current tree, classifying the *exact* remaining mathematical content and whether it is
closable from in-tree + mathlib facts (vs. external-paper formalization or open conjecture).

Tree invariants at review time: 0 live `sorry`/`admit` (sorry_census), flagship `axiom_audit`
green (17 decls ⊆ {propext, Classical.choice, Quot.sound}), 11 named residual `axiom`s in
scripts/residual_axioms.txt (each issue-tracked), forbidden-token gate clean.

## Closed this session (axiom → kernel-clean theorem, verified, pushed)
- **#138/#139** `B_coeff_weight_le` — assembled from proven ingredients (degree-decomposition
  route: B_coeff_weight_le_hasse ▸ weight_Λ_over_𝒪_le_of_mk_eq ▸
  weight_Λ_le_natDegreeY_mul_add_degreeX ▸ hasseCoeffRepr𝒪_natDegreeY_le).
- **#138/#139** `embeddingOf_hasseCoeffReprO_cleared_uniform_residual` — was UNSOUND (i1=0 /
  deltaSave=1 demands natDegreeY p ≤ R.natDegree−1−m, false generically; omega counterexample);
  replaced with a correct proven lemma at k = natDegreeY p. HenselNumerator.lean now axiom-free.

## Remaining — genuine open math (NOT closable in-session without fabrication)

| Issue | Remaining content | Class |
|-------|-------------------|-------|
| #141 / #171 | `mcaConjecture` / `epsMCAgs_prizeBound_conjecture` — the proximity-gap **prize** | OPEN RESEARCH CONJECTURE (unsolved) |
| #81 `bchks25_kk25_rs_epsCA_lower_capacity` | near-capacity epsCA lower-bound construction | external paper (BCHKS25+KK25) |
| #82 `cs25_rs_epsCA_breakdown_lower` | reduced in-tree to ONE second-moment inequality `hSM` (RS ball-intersection in entropy band) = CS25's actual theorem | external paper (CS25 Cor 1) |
| #83 `bchks25_rs_epsCA_johnson_jump` | Johnson-jump witness family | external paper (BCHKS25) |
| #84 `gkl24_cubeRoot_mca_bound`, `bgks20_etaMargin_ca_bound` | ∛-radius / 1.5-Johnson MCA + η-margin CA (needs the ∛-radius list-decoding count) | external papers (GKL24, BGKS20) |
| #85 `bchks25_rs_epsMCA_johnson_range` | Johnson-range RS epsMCA | external paper (BCHKS25) |
| #86 `gg25_subspaceDesign_epsMCA`, `gg25_frs_epsMCA_capacity` | subspace-design + folded-RS capacity MCA | external paper (GG25) |
| #87 `bchks25_rs_epsCA_item2` | δ_min/3-to-Johnson RS epsCA | external paper (BCHKS25) |
| #106 `fenziSanso_upperBound_attack_concrete_residual` | ∃ violating instance with 2^70 ≤ winningSet.ncard over KoalaBear-sextic RS | deep attack construction |
| #116 | completeness-unroll DONE (`fiatShamir_completeness_unroll_discharged`). SR-soundness⇒soundness = the `fiatShamir_soundnessTransferResidual` (the whole FS soundness stack is gated on it). HVZK⇒ZK open. | deep formalization gap |
| #138/#139 | `AlphaGenuineRegularWeightLe` / `DivWeightLe` / `RestrictedFaaDiBrunoMatch` (def : Prop residuals — the structured BCIKS20 App-A α/β invariant + restricted Faà-di-Bruno match) | deep formalization gap |
| #13 | `SubPhaseSoundnessResidual` / `SubPhaseCompletenessResidual` (append composition lemmas ALREADY proven; remaining = outer LogUp + embedded-sumcheck-through-liftContext) | deep formalization gap |
| #14 | `fri_query_soundness` — probabilistic query-round acceptance bound (Claim 8.2) | paper-length |
| #29 | RingSwitching — 5 **design-blocked** holes (need design decisions, not pure proof) | design-blocked |
| #62 | BCS compiler beyond statement-level scaffolding | paper-length |
| #113 | WHIR: construct Vector IOPP + perfect completeness + `whir_rbr_soundness` | paper-length |
| #114 | Spartan: 2nd sumcheck + final CheckClaim + composition + rbr knowledge soundness | paper-length |
| #140 | repair the *refuted* `lineDecodable_imp_epsMCA_le_target`; correct form needs GG25 multi-γ overlap-coverage extraction | external paper (GG25) |

## FS #116 SR-soundness — best-progress route (for a dedicated session)
Reduced the coupled transfer to a single tail goal: apply `hSR` to a manual srProver that
REPLAYS `prover.output` (state-matching); `le_trans ?_ (hSR srProver)`; unfold srSoundnessGame;
`rw [Reduction.run_of_prover_first, Verifier.StateFunction.probEvent_optionT_mk_eq_elim]`; THREE
simp passes mirroring the PROVEN `fiatShamir_runCollapse` (BasicCompleteness.lean) — this aligns
both sides to an identical srInit→sendMessage→output prefix. Peel it with
`Verifier.StateFunction.probEvent_bind_mono_heteroEvent ×3`. Residual WALL = the tail: LHS bundles
deriveTranscriptSR+V.verify+getM in one OptionT simulateQ (Option-of-Option) + a collapsible
doubled-addLift; RHS splits them (single Option). Need a soundness-side run-collapse lemma
(adversarial-prover analogue of fiatShamir_runCollapse) to expose a shared base, then
`probEvent_mono` via `hstmtIn` (valid: stmtIn fixed, stmtIn∉langIn ⇒ SR event ≡ FS event).
