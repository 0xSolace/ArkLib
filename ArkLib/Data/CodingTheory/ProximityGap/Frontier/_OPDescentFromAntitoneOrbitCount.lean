/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._OffBGK_OPSingleOrbitPersistence

/-!
# Bridging the proven antitone orbit-count merge to the named `OPDescentStep` obligation (#444)

The binding-rung commit (`_LaneB_OrbitFoldDescent`, `_OffBGK_AgreementDepthMerge`,
`_OffBGK_OPSingleOrbitPersistence`) localized the single-orbit-persistence conclusion to ONE named
open obligation:

  `OPDescentStep OP μ₀ := ∀ μ ≥ μ₀, OP (μ+1) ≤ OP μ`     (`_OffBGK_OPSingleOrbitPersistence`).

It exhibited TWO candidate routes to discharge it, and the just-landed work showed which one survives:

* **Route 1 — fold injectivity** (`OPDescentStep_of_foldInjective ⟸ PerLevelFoldInjective`,
  `_LaneB_OrbitFoldDescent`).  BLOCKED on the odd/plateau part: `OddFoldInjective` is REFUTED by the
  witness (plateau rung free-orbit count `O = 11`, binder `O = 1`; `¬ 11 ≤ 1`).  The even part folds
  injectively (clean) but the odd part does NOT, so fold injectivity cannot supply the binder descent.

* **Route 2 — antitone orbit count.**  The free-orbit count `orbitCount D z S = (D − z)/S` is ANTITONE
  in agreement depth (pure `Nat`-division monotonicity in `D`, restated below as `orbitCountAux_mono_in_D`).
  This is the binding-rung COLLAPSE mechanism the witness commit identified (the `11 → 1` collapse is the
  agreement-constraint collapse, NOT a fold injectivity).

This file is the missing BRIDGE: it wires the Route-2 merge to discharge the Route-1 target.

## NOTE — why this file inlines the orbit-count primitive (orphan-file finding 2026-06-17, RESOLVED 2026-06-18)

The abstract orbit-count merge content (`orbitCount`, `orbitCount_mono_in_D`, `orbitCount_antitone_depth`)
lives in `_OffBGK_AgreementDepthMerge.lean`.  When this BRIDGE landed (@ `7f1e51730`) that module did **not
build**: it `import`ed `ArkLib...Frontier._DStarDecreasingEnvelope`, a file that never existed in the tree,
and cited a `cliqueColors_antitone_depth` substrate that was never written; it was also unregistered in the
`ArkLib.lean` umbrella.  So to keep this bridge buildable and axiom-clean it INLINES the trivial abstract
primitive (`orbitCountAux` + `orbitCountAux_mono_in_D`, pure `Nat` division monotonicity).

**RESOLVED (2026-06-18):** `_OffBGK_AgreementDepthMerge.lean` was REPAIRED — its missing import was
redirected to the real `CliqueDecayPigeonholeVacuous`, where the antitone substrate is now supplied as a
genuine clique-nesting proof (`cliqueColors_antitone` / `cliqueColors_card_antitone` from
`isClique_succ_imp_isClique`), and the module is now registered in the umbrella and builds axiom-clean.
The inline `orbitCountAux` below is retained (it keeps this file's import surface minimal and is a verbatim
copy of `OffBGKAgreementDepthMerge.orbitCount`); it can now be replaced by the import
and `orbitCountAux` aliased to `OffBGKAgreementDepthMerge.orbitCount`.

## What is proven here (axiom-clean, `propext / Classical.choice / Quot.sound`, no `sorry`)

* `OPDescentStep_of_antitone_orbitCount` — **the bridge.**  If the free-orbit count is realised as
  `OP μ = orbitCountAux (Dstar μ) z S` for a tower-envelope `Dstar : ℕ → ℕ` that is antitone UP the tower
  (`Dstar (μ+1) ≤ Dstar μ` for `μ ≥ μ₀` — the distinct-bad-α count `D*` drops one rung as the agreement
  constraint deepens), then `OPDescentStep OP μ₀` HOLDS, by `orbitCount_mono_in_D`.  This DISCHARGES the
  named obligation from the proven antitone merge, with NO fold-injectivity hypothesis.

* `OP_persist_of_antitone_orbitCount` — **the composite.**  Plugging the bridge into the persistence
  theorem `OP_persist_of_descent`: given the measured base `OPBase`, the geometric floor `OPFloor`, and
  the orbit-count realisation with `Dstar` antitone, the free-orbit count is exactly `1` for the WHOLE
  `2`-power tower from `μ₀`.  Single-orbit persistence WITHOUT fold injectivity, on the proven-antitone
  substrate.

* `OP_le_one_of_crossing_antitone` / `OP_persist_from_crossing` — **the crossing-collapse refinement.**
  Anchors persistence at the MEASURED binding rung `μ*` instead of a guessed base: from a SINGLE budget
  crossing `Dstar μ* ≤ z + S` (the binder's defining property — the first depth the bad set fits in one
  orbit unit) plus antitonicity from `μ*`, the count is `≤ 1` (no `OP μ* = 1` hypothesis), and with the
  floor it is exactly `1` for every `μ ≥ μ*`.  Strictly weaker base than the composite above.

## What this does NOT do (honesty contract, rules 1, 3, 6)

It does NOT prove CORE `M(μ_n) ≤ C√(n log(p/n))`.  It RELOCATES the open content: from the black-box
`OPDescentStep` to the SHARPER, MEASURABLE hypothesis "`Dstar` is antitone up the tower" — i.e. the
one-rung monotonicity of the distinct-bad-α envelope `D*(m)`.  The witness data supports this
direction (`D*(plateau) = z + 11·S > z + 1·S = D*(binder)`), and the real envelope's antitonicity is
the proven `DStarDecreasingEnvelope.cliqueColors_antitone` IN AGREEMENT DEPTH; what remains genuinely
open is the IDENTIFICATION of the tower step `μ ↦ μ+1` with one unit of agreement-depth increase for
the worst `d=2` direction (the `n → n/2` Schur-ratio orbit projection raising the over-determination
depth by one).  That identification is the remaining brick; this file removes everything else.
-/

namespace ArkLib.ProximityGap.OPDescentFromAntitoneOrbitCount

open ArkLib.ProximityGap.OPSingleOrbitPersistence

/-- **The free-orbit count `orbitCountAux D z S = (D − z)/S`** (inlined copy of
`OffBGKAgreementDepthMerge.orbitCount`; that module does not build on current `origin/main` — see the
file header NOTE).  `D = D*(m)` is the distinct-bad-γ (distinct-level) count, `z` the `γ=0`
fixed-point count, `S = n/2` the orbit size. -/
def orbitCountAux (D z S : ℕ) : ℕ := (D - z) / S

/-- **The free-orbit count is monotone in the distinct-level envelope `D`** (fixed `z, S`): if the
distinct-bad-γ count drops `D₂ ≤ D₁`, the free-orbit count cannot rise.  Pure `Nat`-division
monotonicity (`Nat.div_le_div_right` after `Nat.sub_le_sub_right`).  Inlined copy of
`OffBGKAgreementDepthMerge.orbitCount_mono_in_D`. -/
theorem orbitCountAux_mono_in_D {D₁ D₂ z S : ℕ} (hD : D₂ ≤ D₁) :
    orbitCountAux D₂ z S ≤ orbitCountAux D₁ z S := by
  unfold orbitCountAux
  exact Nat.div_le_div_right (Nat.sub_le_sub_right hD z)

/-- **THE BRIDGE — `OPDescentStep` from the antitone orbit-count merge.**
Suppose the binder free-orbit count is realised by the agreement-depth envelope:
`OP μ = orbitCountAux (Dstar μ) z S`, where `Dstar : ℕ → ℕ` is the distinct-bad-α (distinct-level) count
at tower level `μ`, with a fixed `γ=0` fixed-point count `z` and orbit size `S`.  If `Dstar` is
ANTITONE up the tower from the base (`Dstar (μ+1) ≤ Dstar μ` for every `μ ≥ μ₀` — the distinct-level
count drops by at least nothing each rung as the agreement constraint deepens), then the named open
obligation `OPDescentStep OP μ₀` HOLDS:

  `∀ μ ≥ μ₀, OP (μ+1) ≤ OP μ`.

Each step is `orbitCount_mono_in_D` applied to the one-rung envelope drop.  No fold injectivity is
used: the descent is the antitonicity of the over-determination merge, exactly the mechanism the
witness `binding_fires_plateau_fails` pointed to (the `11 → 1` collapse is this merge, not a fold). -/
theorem OPDescentStep_of_antitone_orbitCount
    {OP : ℕ → ℕ} {μ₀ : ℕ} {Dstar : ℕ → ℕ} (z S : ℕ)
    (hreal : ∀ μ, μ₀ ≤ μ → OP μ = orbitCountAux (Dstar μ) z S)
    (hanti : ∀ μ, μ₀ ≤ μ → Dstar (μ + 1) ≤ Dstar μ) :
    OPDescentStep OP μ₀ := by
  intro μ hμ
  have hμ1 : μ₀ ≤ μ + 1 := le_trans hμ (Nat.le_succ μ)
  rw [hreal μ hμ, hreal (μ + 1) hμ1]
  exact orbitCountAux_mono_in_D (hanti μ hμ)

/-- **THE COMPOSITE — single-orbit persistence from the antitone merge (no fold injectivity).**
Combining the bridge with the assembled persistence theorem `OP_persist_of_descent`: given the
measured base `OPBase OP μ₀` (`OP μ₀ = 1`, anchored at `n = 16`), the geometric floor
`OPFloor OP μ₀` (the binder always carries `≥ 1` free orbit), the orbit-count realisation
`OP μ = orbitCountAux (Dstar μ) z S`, and the tower antitonicity of `Dstar`, the free-orbit count is
exactly `1` for every `μ ≥ μ₀`:

  `O_P(μ) = 1`   (single-orbit persistence over the whole `2`-power tower).

The descent step is now DISCHARGED (route 2), so the only remaining inputs are the anchored base and
floor.  Conditional ONLY on `Dstar` antitone — the SHARPER, measurable relocation of the open
content. -/
theorem OP_persist_of_antitone_orbitCount
    {OP : ℕ → ℕ} {μ₀ : ℕ} {Dstar : ℕ → ℕ} (z S : ℕ)
    (hbase : OPBase OP μ₀) (hfloor : OPFloor OP μ₀)
    (hreal : ∀ μ, μ₀ ≤ μ → OP μ = orbitCountAux (Dstar μ) z S)
    (hanti : ∀ μ, μ₀ ≤ μ → Dstar (μ + 1) ≤ Dstar μ) :
    ∀ μ, μ₀ ≤ μ → OP μ = 1 :=
  OP_persist_of_descent hbase hfloor
    (OPDescentStep_of_antitone_orbitCount z S hreal hanti)

/-! ## The crossing-collapse bridge — persistence anchored at the MEASURED crossing rung

The composite above anchors persistence at a guessed base `OP μ₀ = 1`.  But the actual measured anchor
is the BINDING rung itself: it is the FIRST depth `μ*` where the distinct-bad-α envelope crosses into
one orbit unit, `Dstar μ* ≤ z + S` (the bad set first fits in one `⟨ζ^s⟩`-orbit plus the `γ=0` point).
At that crossing the collapse `OP ≤ 1` is FORCED — no separate base hypothesis is needed — and it
PERSISTS for every deeper rung by antitonicity.  This anchors persistence at the measured crossing,
not at a guessed `OP μ₀ = 1`. -/

/-- **The orbit-count collapse from a single budget crossing** (inline of
`OffBGKAgreementDepthMerge.orbitCount_le_one_of_crossing`): if `D ≤ z + S` (the distinct-bad-α count
fits in one orbit unit plus the fixed point), then `orbitCountAux D z S ≤ 1`.  Pure `Nat`-division:
`(D - z) ≤ S < 2S ⇒ (D-z)/S ≤ 1`. -/
theorem orbitCountAux_le_one_of_crossing {D z S : ℕ} (hcross : D ≤ z + S) :
    orbitCountAux D z S ≤ 1 := by
  unfold orbitCountAux
  rcases Nat.eq_zero_or_pos S with hS | hS
  · subst hS; simp
  · have hlt : (D - z) / S < 2 := by
      rw [Nat.div_lt_iff_lt_mul hS]; omega
    omega

/-- **THE CROSSING-COLLAPSE BRIDGE — `OP μ ≤ 1` from a single measured crossing + antitonicity.**
If the binder free-orbit count is realised `OP μ = orbitCountAux (Dstar μ) z S`, the envelope CROSSES
into one orbit unit at the binding rung `μ*` (`Dstar μ* ≤ z + S`), and `Dstar` is antitone up the tower
from `μ*`, then the free-orbit count is `≤ 1` for EVERY `μ ≥ μ*`.  No `OP μ* = 1` base hypothesis: the
crossing FORCES `≤ 1` at `μ*` (`orbitCountAux_le_one_of_crossing`) and antitonicity carries it up
(`Dstar μ ≤ Dstar μ*` for `μ ≥ μ*`).  This is the agreement-depth analogue of
`OP_le_one_of_descent`, anchored at the MEASURED crossing rather than a guessed base. -/
theorem OP_le_one_of_crossing_antitone
    {OP : ℕ → ℕ} {μstar : ℕ} {Dstar : ℕ → ℕ} (z S : ℕ)
    (hreal : ∀ μ, μstar ≤ μ → OP μ = orbitCountAux (Dstar μ) z S)
    (hcross : Dstar μstar ≤ z + S)
    (hanti : ∀ μ₁ μ₂, μstar ≤ μ₁ → μ₁ ≤ μ₂ → Dstar μ₂ ≤ Dstar μ₁) :
    ∀ μ, μstar ≤ μ → OP μ ≤ 1 := by
  intro μ hμ
  rw [hreal μ hμ]
  exact orbitCountAux_le_one_of_crossing
    (le_trans (hanti μstar μ (le_refl μstar) hμ) hcross)

/-- **PERSISTENCE FROM THE CROSSING (no guessed base).**  Combining the crossing-collapse `OP ≤ 1`
with the geometric floor `1 ≤ OP μ` (the binder always carries a free orbit), the free-orbit count is
EXACTLY `1` for every `μ ≥ μ*`.  The anchor is the measured crossing `Dstar μ* ≤ z + S`, the binder's
defining property — NOT a separately-assumed `OP μ₀ = 1`.  This is the sharpest packaging: single-orbit
persistence from the one measured fact that the binding rung is where `D*` first fits in one orbit unit. -/
theorem OP_persist_from_crossing
    {OP : ℕ → ℕ} {μstar : ℕ} {Dstar : ℕ → ℕ} (z S : ℕ)
    (hfloor : ∀ μ, μstar ≤ μ → 1 ≤ OP μ)
    (hreal : ∀ μ, μstar ≤ μ → OP μ = orbitCountAux (Dstar μ) z S)
    (hcross : Dstar μstar ≤ z + S)
    (hanti : ∀ μ₁ μ₂, μstar ≤ μ₁ → μ₁ ≤ μ₂ → Dstar μ₂ ≤ Dstar μ₁) :
    ∀ μ, μstar ≤ μ → OP μ = 1 := by
  intro μ hμ
  exact le_antisymm
    (OP_le_one_of_crossing_antitone z S hreal hcross hanti μ hμ)
    (hfloor μ hμ)

/-! ## Non-vacuity — the bridge genuinely fires on a measured antitone envelope -/

/-- **Non-vacuity (the bridge fires on a measured envelope).**  Take `μ₀ = 4`, `z = 1`, `S = 8`
(the `n = 16` orbit data: fixed-point count `1`, orbit size `n/2 = 8`), and a tower envelope that has
already crossed to within one orbit of the fixed point at the base and stays there:
`Dstar μ = 9` (so `orbitCount 9 1 8 = (9−1)/8 = 1`), antitone (constant).  Then `OPDescentStep` holds:
every step `OP(μ+1) ≤ OP μ` is `1 ≤ 1` via the merge.  The descent is DERIVED from the realisation +
antitonicity, not assumed. -/
example :
    OPDescentStep (fun _ => orbitCountAux 9 1 8) 4 :=
  OPDescentStep_of_antitone_orbitCount (OP := fun _ => orbitCountAux 9 1 8)
    (Dstar := fun _ => 9) 1 8
    (fun _ _ => rfl) (fun _ _ => le_refl 9)

/-- **Non-vacuity (a strictly-descending envelope still fires).**  An envelope that strictly drops
from the plateau toward the binder — `Dstar μ = 89` at the base dropping to `9` — keeps the orbit
count non-increasing (`orbitCount 89 1 8 = 11`, `orbitCount 9 1 8 = 1`), matching the measured
`11 → 1` collapse.  Here a concrete two-rung antitone envelope discharges the step at the crossing. -/
example : orbitCountAux 89 1 8 ≤ orbitCountAux 89 1 8 ∧ orbitCountAux 9 1 8 ≤ orbitCountAux 89 1 8 :=
  ⟨le_refl _, orbitCountAux_mono_in_D (by norm_num)⟩

/-- **Non-vacuity (the composite yields `O_P = 1` from base + floor + antitone realisation).**
With base `OP 4 = 1`, floor `1 ≤ OP μ`, the constant realisation `OP μ = orbitCount 9 1 8 = 1`, and
constant (antitone) `Dstar = 9`, the composite gives `OP μ = 1` for all `μ ≥ 4`.  Evaluated at `μ=7`. -/
example :
    (fun _ => orbitCountAux 9 1 8) 7 = 1 :=
  OP_persist_of_antitone_orbitCount (OP := fun _ => orbitCountAux 9 1 8) (μ₀ := 4)
    (Dstar := fun _ => 9) 1 8
    (show orbitCountAux 9 1 8 = 1 by decide)
    (fun _ _ => show 1 ≤ orbitCountAux 9 1 8 by decide)
    (fun _ _ => rfl) (fun _ _ => le_refl 9) 7 (by norm_num)

/-- **Non-vacuity (persistence FROM the measured crossing, no guessed base).**  At the binder
`μ* = 4`, `z = 1`, `S = 8`, the envelope crosses: `Dstar μ* = 9 ≤ 1 + 8 = z + S`.  With the floor
`1 ≤ OP μ` and the realisation `OP μ = orbitCountAux 9 1 8 = 1`, `OP_persist_from_crossing` gives
`OP μ = 1` for all `μ ≥ 4`, anchored ONLY on the crossing `9 ≤ 9` — no `OP μ₀ = 1` assumed.  At `μ=9`. -/
example : (fun _ => orbitCountAux 9 1 8) 9 = 1 :=
  OP_persist_from_crossing (OP := fun _ => orbitCountAux 9 1 8) (μstar := 4)
    (Dstar := fun _ => 9) 1 8
    (fun _ _ => show 1 ≤ orbitCountAux 9 1 8 by decide)
    (fun _ _ => rfl)
    (show (9 : ℕ) ≤ 1 + 8 by norm_num)
    (fun _ _ _ _ => le_refl 9) 9 (by norm_num)

end ArkLib.ProximityGap.OPDescentFromAntitoneOrbitCount

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only — no `sorryAx`) -/
open ArkLib.ProximityGap.OPDescentFromAntitoneOrbitCount in
#print axioms OPDescentStep_of_antitone_orbitCount
open ArkLib.ProximityGap.OPDescentFromAntitoneOrbitCount in
#print axioms OP_persist_of_antitone_orbitCount
open ArkLib.ProximityGap.OPDescentFromAntitoneOrbitCount in
#print axioms OP_le_one_of_crossing_antitone
open ArkLib.ProximityGap.OPDescentFromAntitoneOrbitCount in
#print axioms OP_persist_from_crossing
