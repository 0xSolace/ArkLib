# DRY / unification audit — 2026-06-10/11 campaign surface

Systematic duplication and symmetry audit over the files landed in the #329/#334/#340
campaigns, plus the pre-existing surfaces they touch. Each item: the duplication, the
consolidation, and its status.

## Consolidated this pass

1. **`ProximityGap.exists_dual_ne_zero` duplicated Mathlib** — Mathlib's
   `Module.Projective.exists_dual_ne_zero` (`LinearAlgebra/Dual/Lemmas.lean`) proves the same
   fact for projective modules (vector spaces are free hence projective); my basis-coordinate
   proof was a re-derivation. **Done**: the ArkLib lemma is now a thin wrapper (kept for the
   `A →ₗ[F] F` spelling its consumer `eq_zero_of_curve_agree_many` uses).

## Already-DRY by construction (the campaign's positive symmetries)

2. **`SubspaceAvoidance` as the shared counting engine** — one file serves: the #329 RLC
   kernel leaf (codim-1 count), [Jo26] Thm 4.2's avoidance/averaging (#334 K1/K2), the
   `A(q,s)` sharpness certificate (A2), and Thm 5.8's per-`V_T` capacity bound. Four
   consumers, zero clones.
3. **`curveExplainSubmodule_ne_top_of_no_witness`** — the standard-basis properness argument
   extracted once (`GG25WeightedTransfer.lean`) and shared by Theorems 5.7 and 5.8 (5.7's
   inline copy predates the extraction; see item 6).
4. **`curve_through_values`** (module-valued Lagrange) — built for Lemma 5.2, deliberately
   shaped for the planned `V_T`-style constructions; submodule-span membership is part of the
   statement so consumers never re-derive coefficient membership.
5. **Theorem 5.5's converse welds bricks 2/3/4** — no new machinery; the far-codeword
   close-set pinning reuses Lemma 5.4 exactly where a fresh argument would have duplicated
   its instance construction.

## Documented refactor debt (not done this pass — import-order or ownership constraints)

6. **Thm 5.7's inline properness block** (`GG25ExactPreservation.lean`) predates the
   extraction in item 3; replacing it with a call to
   `curveExplainSubmodule_ne_top_of_no_witness` would invert the current import direction
   (`GG25WeightedTransfer` imports `GG25ExactPreservation`). Consolidation = move the lemma
   into `GG25ExactPreservation.lean` and rewrite 5.7's `hproper` to consume it. Mechanical;
   touches two of my files only.
7. **`relationRound_last_iff` (deg-3, `TightMidLeaves.lean:97`) vs
   `relationRound_last_iff_deg` (deg-generic, `TightFinalLeaf.lean:55`)** — the generic lives
   *later* in the import chain; dedup requires moving the generic into `TightMidLeaves` (or a
   shared brick file) and restating the deg-3 form as a corollary. Known since the #329
   closeout (catalogued there).
8. **The `sfx*` direction facts and `vsum_two_pos`/`sumcheckPSpec_dir_zero` are cloned 3×**
   (`ComposedCompleteness.lean`, `TightComposedFull.lean` (primed), and the textual-transform
   regenerated `TightComposedCompleteness.lean`) — all `private`, so consolidation = a shared
   public `SpartanDirFacts.lean` + three import swaps. The clones are proof-identical by
   construction (two were generated from the first); drift risk is low but nonzero.
9. **Inline `⊥ ≠ ⊤` proofs** (the all-ones-vector argument) appear in
   `Jo26GeneratorDichotomy.lean` and `GG25ExactPreservation.lean` — both could use
   `bot_ne_top` once a `Nontrivial (Fin s → F)` instance is threaded (needs `1 ≤ s` locally);
   a 3-line shared lemma `Submodule.bot_ne_top_of_pos` parameterized on `0 < s` would serve
   both.
10. **The 6-phase `ComposedTightRbrKnowledge.lean` vs the 8-phase `TightComposedFull.lean`**
    — the 6-phase file is a strict ancestor of the 8-phase apex; its endpoint (`tightRelG`)
    is now interior to the full chain. Candidate for deprecation-by-docstring pointing at the
    apex (not deletion: it documents the shorter assembly pattern).

## Method note

The census-wave triage (#337–#347) repeatedly found duplication's *audit-side* twin: residual
Props whose discharges exist under different names. The same root cause — name-based search
missing semantic identity — drives both. The docstring/tree-first rule
(`docs/wiki/append-residuals-and-elaboration-patterns.md`) is the countermeasure on the audit
side; this file is the countermeasure on the proof side.
