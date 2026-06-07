# Issue #33 — Binius Steps: close 9 named residuals after Prelude port lands

**Status:** OPEN / not closeable. The 9 named Steps residuals are *written* as genuine proofs (no
`sorry`/`admit` anywhere in the Binius tree), but they cannot be **compiled / verified green**
because every Steps module transitively depends on the **never-compiled Binius Soundness layer**
(`Soundness/Lift.lean`, `Soundness/QueryPhasePrelims.lean`, and the rest of the 7-module subtree),
which has deep build errors. That layer is a separate, in-progress harvest from `CompBinius`, not a
Steps residual. The `FoldPreservesBBFCodeMembershipResidual` (Lemma 4.13 port) also remains, also
separate.

## Ask (issue scope)

After the Prelude port (#32) lands, close the named Binius **Steps** residuals: 3 step
perfect-completeness theorems repaired with `hInit : NeverFail init`,
`foldKnowledgeStateFunction.toFun_full`, `foldOracleVerifier_rbrKnowledgeSoundness`, `commitKState`,
and finalSumcheck `toFun_next`/`toFun_full` back-transport.

## What is done

- The Steps residuals are written as real theorems with real tactic proofs (no `sorry`):
  - `Steps/Commit.lean:148` `commitOracleReduction_perfectCompleteness (hInit : NeverFail init)`,
    `Steps/Fold.lean:162` `foldOracleReduction_perfectCompleteness (hInit : NeverFail init)`,
    `Steps/Relay.lean:146` `relayOracleReduction_perfectCompleteness (hInit : NeverFail init)`,
    `Steps/FinalSumcheck.lean:141` `finalSumcheckOracleReduction_perfectCompleteness`.
  - `toFun_full` extractor proofs in Fold/Commit/FinalSumcheck/Relay.
  - `*_rbrKnowledgeSoundness` in all four steps.
- `#32` (Prelude port) resolved.
- Whole-tree comment-stripped scan of `ArkLib/ProofSystem/Binius/BinaryBasefold/**` → **zero**
  `sorry`/`admit`.

## Why the green build cannot be confirmed (the real blocker)

The four `Steps/*.lean` modules all `import ReductionLogic`, and
`ReductionLogic.lean` imports `Soundness.Lift`. `Steps/Fold.lean` additionally imports the
`Soundness` umbrella and uses `Soundness.Incremental` bad-event machinery
(`incrementalFoldingBadEvent`, `incrementalBadFoldEvent`, `incrementalBadEventExistsProp`). The
entire `Soundness/` subtree is **never-compiled** (all 7 oleans absent) and currently does not build:

- `Soundness/Lift.lean` — `rewrite` failures (`:198`, `:213`), instance-synthesis failure (`:330`),
  application type mismatches (`:328`, `:370`).
- `Soundness/QueryPhasePrelims.lean` — ~50 errors: `Invalid argument name h_ℓ_add_R_rate` for
  `queryBlockSourceIdx`/`queryBlockDestIdx`(`_le`) (signature drift), `Unknown identifier`
  for `lt_r_of_lt_ℓ`/`lt_r_of_le_ℓ`/`k_mul_ϑ_lt_ℓ`/`queryBlockDestIdx_eq_queryBlockSourceIdx_succ`/
  `UDRClose_of_fin_eq`, kernel `unknown constant extractSuffixFromChallenge_congr_destIdx`, and two
  `whnf` heartbeat timeouts (`:833`, `:951`).
- `Soundness/{Proposition4_21,Incremental,FoldDistance,BadBlocks,QueryPhaseSoundness}` — also
  uncompiled (oleans absent); `BadBlocks` imports `QueryPhasePrelims`.

Repairing this whole layer is a substantial multi-session port against the refactored Binius
soundness API (signature drift + missing lemmas + proof-perf), clearly separate from "close the 9
Steps residuals." Until it builds, the Steps proofs cannot be machine-checked.

## The other remaining frontier residual (separate from Steps)

`FoldPreservesBBFCodeMembershipResidual` (`Code.lean:992`, `class : Prop`) — the Lemma 4.13
code-membership consequence. Legitimate named residual (not a `sorry`), consumed only by the
soundness lift (`Soundness/Lift.lean:185`), **not by any Steps file**. Gated on porting the
general-`i` reconstruction stack (`getINovelCoeffs`, `degree_intermediateEvaluationPoly_lt`,
`intermediateEvaluationPoly_from_inovel_coeffs_eq_self`, `fold_advances_evaluation_poly`); CompPoly
provides the general-`i` building blocks (`intermediateEvaluationPoly`, `intermediateNovelBasisX`,
`evaluation_poly_split_identity`) but only the `i = 0` reconstruction (`intermediate_poly_P_base`).
Predominantly CompPoly-layer work. Audited under `0c5a2b2df` /
`docs/kb/audits/issue-33-binius-branch-harvest-2026-06-06.md`.

## Cleanest decoupling lever (concrete next step for 3 of the 4 Steps)

`Steps/Commit`, `Steps/Relay`, `Steps/FinalSumcheck` import only `ReductionLogic` (not the
`Soundness` umbrella). `ReductionLogic` in turn imports the broken `Soundness.Lift` for **exactly
one** symbol: the 2-line self-contained helper `bitsOfIndex` (`Soundness/Lift.lean:41`,
`fun j => if Nat.getBit j.val k.val = 1 then 1 else 0`). Relocating `bitsOfIndex` into a stable
low module (e.g. a new `BinaryBasefold/BitsOfIndex.lean`, or `Basic.lean`) that both `Lift` and
`ReductionLogic` import — and dropping `import Soundness.Lift` from `ReductionLogic` — decouples the
entire Steps **completeness** layer from the broken Soundness lift. That should let
`Steps/{Commit,Relay,FinalSumcheck}` compile and machine-verify 3 of the 4 step residuals without
any soundness-layer repair. (Note: it must MOVE the def, not duplicate it — `Steps/Fold` imports
both `ReductionLogic` and the `Soundness` umbrella, so two `Binius.BinaryBasefold.bitsOfIndex`
definitions would collide there.) `Steps/Fold` additionally needs `Soundness.Incremental` and the
umbrella, so it stays gated on the soundness-layer port until that lands. Not executed here because
the clean move edits the actively-refactored (API-drifting) `Soundness/Lift.lean`, which is unsafe
to touch concurrently in the shared multi-agent tree.

## Recommendation

Keep #33 open. The Steps proofs are written, but their green-build verification is gated on a
separate effort to repair the never-compiled Binius `Soundness/` subtree (Lift + QueryPhasePrelims
+ siblings) — which should likely be tracked as its own issue — and on the Lemma 4.13 reconstruction
port. Neither is a Steps-residual defect.
