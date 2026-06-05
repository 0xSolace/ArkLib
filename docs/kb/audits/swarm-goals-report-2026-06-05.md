# Swarm Goals Report

Date: 2026-06-05

Baseline report: [`zkvm-total-verification-report-2026-06-05.md`](zkvm-total-verification-report-2026-06-05.md)

Primary ledger: [`proximity-prize/GRIND-LEDGER.md`](proximity-prize/GRIND-LEDGER.md)

## Purpose

This report is the current dispatch note for a swarm of subagents working on ArkLib verification
closure. Treat the baseline report as the status source of truth and this file as the coordination
brief for the next wave of work.

## Current Baseline

ArkLib is buildable, but routine validation is not clean: `./scripts/validate.sh` reaches a Lean
build and then fails the ArkLib/Data non-sorry warning budget. The proximity-prize keystone has a
real conditional bridge in
`ArkLib.BetaToCurveCoeffPolys.curveCoeffPolys_of_betaRec`, but it still needs its section-5
extraction/setup hypotheses supplied and connected to the in-place `Curves.lean` theorem.

The existing audit distinguishes genuine kernel-clean bricks from wrappers that assume the target
goal. Subagents must preserve that distinction. A result only counts when it is kernel-clean or when
its remaining assumptions are explicitly named and justified as external section-5 data.

## Goals

1. Close the proximity-prize keystone without duplicating already completed work.
2. Assemble the real route from `betaRec` to `CurveCoeffPolys` by supplying the missing section-5
   data: matching points/cardinality, divisibility `Hlift H ∣ R`, gamma recentering, representative
   and degree hypotheses, and the `Pz`/boundary facts required by the existing conditional theorem.
3. Replace the trivial in-tree `beta_regular` path with `betaRec`, then prove `hcoeffPoly` and close
   `correlatedAgreement_affine_curves` in `Curves.lean`.
4. De-taint downstream STIR, WHIR, and FRI round-by-round soundness only after the upstream theorem
   is genuinely closed.
5. Reduce remaining executable `sorry`s where they sit on active proof paths, prioritizing real
   proof discharge over wrapper APIs.
6. Make `./scripts/validate.sh` green by reducing the ArkLib/Data warning budget, with targeted
   module builds after each warning batch.
7. Audit external admits, conjectures, and explicit hypotheses, separating acceptable formal
   interfaces from unresolved mathematical obligations.
8. Map claimed ArkLib theorems to the full zkVM verification stack and state which end-to-end
   components remain outside ArkLib.

## Subagent Instructions

Work from the current checkout and read the baseline report before starting. Avoid editing generated
files such as `ArkLib.lean` or derived output under `.lake/`, `blueprint/web/`, `blueprint/print/`,
`dependency_graphs/`, or `home_page/docs/`. Do not revert changes made by other agents. Coordinate
before touching shared high-contention files such as `Curves.lean`, `Agreement.lean`, and the
proximity-prize bridge files.

Every subagent report must include exact files, declarations, commands run, proof status, axiom
status where relevant, remaining assumptions, and blockers. Do not report a wrapper as proof
closure if it assumes the target theorem or the decisive witness. Prefer small kernel-clean Lean
proofs, targeted `lake build <module>` checks, and updates to the audit docs with concrete evidence.

## Suggested Workstreams

- Keystone integration: start from `ArkLib/ToMathlib/BetaToCurveCoeffPolys.lean` and the
  integration notes under `docs/kb/audits/proximity-prize/integration-2026-06-05/`; connect the
  existing `betaRec` bridge to section-5 data rather than re-proving the bridge.
- Gamma and beta path: fix the `x₀`/gamma recentering issue, replace `β_regular` with `betaRec`,
  and thread the resulting hypotheses into the `Curves.lean` front door.
- Warning budget: remove low-risk ArkLib/Data style warnings first, run targeted module builds, and
  then re-run `./scripts/validate.sh`.
- Sorry audit: inventory remaining executable `sorry`s on proof-critical paths and distinguish
  active gaps from documentation-only or intentionally abstract interfaces.
- ZKVM map: extend the baseline report's whole-stack analysis with theorem-to-component evidence
  and clear statements of what ArkLib does not yet verify.
