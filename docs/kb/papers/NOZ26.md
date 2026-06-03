---
kind: paper
bibkey: NOZ26
title: "Hachi: Efficient Lattice-Based Multilinear Polynomial Commitments over Extension Fields"
year: "2026"
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2026/156
source_metadata: ../sources/NOZ26/metadata.yml
status: seeded
related_modules:
  - ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness.lean
---

# NOZ26

## At A Glance

`NOZ26` ("Hachi") is a concretely efficient lattice-based multilinear polynomial commitment scheme
over extension fields, improving on Greyhound (CRYPTO 2024). For ArkLib its relevance is the
security-analysis machinery rather than the commitment construction: it states the **multi-round
form of coordinate-wise special soundness** (Definition 3) and the soundness-error bound (Lemma 4)
that ArkLib targets for verification.

## What ArkLib Uses From This Paper

- **Definition 3 (coordinate-wise special soundness, multi-round).** This is the notion ArkLib
  formalizes as `Verifier.coordinateWiseSpecialSound`: existence of a tree-based extractor that
  turns any structured, accepting tree of transcripts into a valid input witness.
- **Lemma 4 (knowledge error).** The CWSS-to-knowledge-soundness bound `∑ᵢ ℓᵢ·kᵢ / |Sᵢ|^{ℓᵢ}`,
  formalized as `CWSSStructure.knowledgeError` and stated in
  `coordinateWiseSpecialSound_implies_knowledgeSoundness`.
- The §2.3 description of the special-sound family `SS(S, ℓ, k)`, rendered as
  `CoordinateWise.IsSpecialSoundFamily`.

## Main ArkLib Touchpoints

- [`ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness.lean`](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness.lean)
  cites `NOZ26` in its module docstring and follows its Definition 3 / Lemma 4 for the multi-round
  notion and the knowledge-error bound.

## Version Notes

- Cryptology ePrint Archive, Paper 2026/156. ArkLib tracks the ePrint version.
- Read together with [`FMN24.md`](FMN24.md), which introduces coordinate-wise special soundness, and
  [`AFK22.md`](AFK22.md), whose forking/Fiat–Shamir analysis underlies the rewinding extractor.

## Known Divergences From ArkLib

- ArkLib phrases the definition over its own IOR machinery (`ProtocolSpec`, `Verifier`,
  `ChallengeTree`) rather than the paper's interactive-argument syntax. The transcript tree is made
  arity-indexed and challenge-branching only, abstracting away the commitment scheme of the paper.

## Open Formalization Gaps

- The implication `coordinateWiseSpecialSound_implies_knowledgeSoundness` (Lemma 4) is currently
  stated with a `sorry`; the rewinding/forking construction of the tree of transcripts is future
  work.

## Source Access

- Source metadata: [`../sources/NOZ26/metadata.yml`](../sources/NOZ26/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
