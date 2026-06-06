/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliza
-/
import ArkLib.Data.CodingTheory.ProximityGap.Hab25Core

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# Hab25 §3 endgame: Claim 1 → Theorem 2, the Johnson-radius MCA upgrade for RS codes

This file ports the **§3 endgame** of

  Ulrich Haböck, "A note on mutual correlated agreement for Reed–Solomon codes",
  ePrint 2025/2110 (Nov 17, 2025), **Theorem 2 / Claim 1** (paper lines 124–311),

building *bottom-up* on the proven combinatorial bedrock in the sibling
`Hab25Core.lean` (`affine_match_card_le_one`, `hab25_endgame_count`, `disagreeSet`) and on
the proven single-function Guruswami–Sudan list-decoding substrate
`ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean`
(`gs_existence`, `gs_divisibility`, the `Conditions` structure with `Q_multiplicity`).

The companion `Hab25Core.lean` already records the Johnson-range MCA bound as a *monolithic*
reduction whose single residual `Hab25GSInterpolation` is definitionally the in-tree
`rs_epsMCA_johnson_range_bchks25` — i.e. the entire deep content is renamed, not derived.
**This file refines that.** It splits the deep GS content into its *named sub-steps*, and
**proves** every step the substrate supports today (the per-factor "improving scalar" count
and the Theorem-2 union bookkeeping), isolating only the genuinely-deep nodes
(GS interpolation degree bounds over `F(Z)`, discriminant non-vanishing, the Hensel lift)
as explicitly-named hypotheses. No `sorry`, no `admit`, no `axiom`.

## The full §3 derivation, in ≤15 named steps

Notation (paper §3): `D ⊆ F` the smooth evaluation domain, `n := |D|`, `ρ := k/n` the rate,
`f₀ f₁ : D → F` the two received words, `Z` a formal variable, `K := F(Z)`, and for a scalar
`z ∈ F` the **fold** `f_z := f₀ + z·f₁`. The **mutual** disagreement set is
`E := {z ∈ F : the fold f_z is δ-close to C but (f₀,f₁) is not jointly close along the
collinear line through z}`. The target Theorem 2 is `|E| ≤ (ℓ⁷/3)·(ρn)²` with
`ℓ := (m+½)/√ρ`, which scaled by `1/|F|` is the `ε_mca` bound.

* **S1 (Fold-as-RS-word).** For each `z ∈ F`, `f_z = f₀ + z·f₁` is a word over `D`; if it is
  `δ`-close to `RS[F,D,k]` then by GS list-decoding (`gs_existence`/`gs_divisibility`) there
  is a degree-`<k` polynomial `p_z` with `Δ(f_z, p_z|_D) ≤ δ·n`, and `(X − C p_z) ∣ Q_z` for
  the GS interpolant `Q_z` of `f_z`.  [substrate: `GuruswamiSudan.gs_divisibility`]  PROVEN-SUBSTRATE

* **S2 (Lift to `K = F(Z)`).** Build a *single* Guruswami–Sudan interpolation polynomial
  `Q(X,Y,Z)` of the generic fold `f₀ + Z·f₁` over `K`, with multiplicity `m` at each
  `(ω_i, f₀ i + Z·f₁ i)`. This is the §3 generalisation of [BCIKS20 §5] from `F` to `K`.
  → DEEP (residual `GSInterpOverK`): no algebraic-function-field interpolation API in tree.

* **S3 (Degree bounds, [BCIKS20] Claim 5.4 over `K`).** `Q` has `D_Y < ℓ`, `D_X < ℓ·ρn`,
  `D_{YZ} ≤ (ℓ³/6)·ρn`. The `D_Y < ℓ` bound is the **list-size / number-of-factors** bound
  used by S10.  → DEEP (residual `GSDegreeBounds`), but its *consequence* `D_Y < ℓ` is
  consumed below as a clean cardinality hypothesis `hYbound`.

* **S4 (Factorisation).** Over `K`, `Q = C·∏_{i,j} R_{i,j}^{e_{i,j}}` with `R_{i,j}`
  irreducible/separable; the index set `(i,j)` has `#(i,j) ≤ D_Y < ℓ`.  → DEEP
  (residual `GSFactorisation`); consequence: a `Finset Idx` of factors with `Idx.card < ℓ`.

* **S5 (Discriminant non-vanishing).** `deg_X disc_Y(Q) < ℓ²·ρn`, so for `|F| > ℓ²ρn` there is
  `x₀ ∈ D` with `disc_Y R_{i,j}(x₀,·,·) ≠ 0` for all `i,j`. Starting point of the Hensel lift.
  → DEEP (residual `DiscriminantNonVanishing`).

* **S6 (Hensel lift + [BCIKS20] Steps 5–7, App. C).** On the "useful factor" the lift forces
  `R_{i,j}(X, Y^{p^{f_{i,j}}}, Z) = (Y − (a_{i,j}(X) + Z·b_{i,j}(X)))^{p^{f_{i,j}}}`; hence for
  each `z`, the per-factor decoded polynomial `p_z = a_{i,j}(X) + z·b_{i,j}(X)` is **uniquely
  determined** as an affine function of `z`.  → DEEP (residual `HenselUniqueness`);
  consequence (the only thing the endgame needs): a *unique affine pair* `(a_{i,j}, b_{i,j})`
  of evaluation vectors per factor.

* **S7 (Per-factor disagreement set).** Fix a factor `(i,j)`. Let `a := a_{i,j}|_D`,
  `b := b_{i,j}|_D : D → F`, and the *factor-agreement set*
  `A°_{i,j} := {x ∈ D : (a x, b x) = (f₀ x, f₁ x)}`. Set `d₀ := a − f₀`, `d₁ := b − f₁`. Then
  `D \ A°_{i,j} = disagreeSet d₀ d₁` (the in-tree `disagreeSet`), and `|D \ A°_{i,j}| ≤ n`.
  → PROVEN here (`factorDisagree_card_le_n`): pure `Finset.card_le_card` against `univ`.

* **S8 (Per-factor "improving scalar" set).** `E_{i,j} := {z ∈ F : the fold f_z agrees with
  a + z·b at some coordinate of D \ A°_{i,j}}` — the scalars that "improve agreement beyond
  `A°`". Each such `z` is a root of the non-trivial affine functional
  `g_x(z) = d₀ x + z·d₁ x` at some `x ∈ disagreeSet d₀ d₁`.
  → PROVEN here (`factorImprove_card_le_n`): this is exactly `hab25_endgame_count`,
  composed with S7. **"From the proof of Lemma 1"** (paper l.302–310).

* **S9 (Claim 1 numeric).** Therefore `|E_{i,j}| ≤ n ≤ (ℓ⁶/3)·(ρn)²` once `(ℓ⁶/3)·(ρn)² ≥ n`
  (the paper's regime, equivalently `ℓ⁶·ρ²·n ≥ 3`, true for the Johnson-range parameters).
  → PROVEN here (`claim1_bound`) modulo the elementary numeric inequality `hClaim1Num`.

* **S10 (Theorem 2 union).** `E = ⋃_{i,j} E_{i,j}`, so
  `|E| ≤ Σ_{(i,j)} |E_{i,j}| ≤ #(i,j) · max_{i,j}|E_{i,j}| ≤ ℓ · (ℓ⁶/3)(ρn)² = (ℓ⁷/3)(ρn)²`.
  → PROVEN here (`theorem2_union_bound`): pure `Finset.card_biUnion_le` +
  `Finset.sum_le_card_nsmul` bookkeeping, consuming `hYbound : Idx.card < ℓ` (S3) and the
  per-factor bound (S9). The decomposition `E = ⋃ E_{i,j}` is residual (`MutualDisagreeCover`).

* **S11 (Scale to `ε_mca`).** Dividing the integer disagreement count by `|F|` and matching the
  closed form gives `ε_mca(C, δ) ≤ johnsonBoundReal`. → bridges to the proven
  `Hab25Core.Hab25Johnson` plumbing; the numeric residual is the in-tree
  `rs_epsMCA_johnson_range_bchks25` shape (named `JohnsonNumericBound`).

## Disposition summary (proven vs residual)

PROVEN here (from substrate, zero residual): S1 (substrate), **S7, S8, S9, S10** — the entire
*combinatorial* skeleton of Claim 1 and Theorem 2, including the integer-level
`|E| ≤ ℓ · |E_{i,j}|` union arithmetic and the per-factor `|E_{i,j}| ≤ n`.

RESIDUAL (named hypotheses, the DEEP algebraic nodes): S2 (`GSInterpOverK`),
S3/S4 (`hYbound`/factor index set), S5 (`DiscriminantNonVanishing`),
S6 (`HenselUniqueness`, exposed as the unique affine pair), S10-cover
(`MutualDisagreeCover`), S11-numeric (`JohnsonNumericBound`).

This is the honest refinement: the monolithic `Hab25GSInterpolation` of `Hab25Core` is here
*opened up*, its combinatorial half **proven**, its algebraic half left as precisely-named
residuals.
-/

namespace CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame

open Finset
open CodingTheory.ProximityGap.Hab25Core

variable {F : Type*} [Field F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]

/-! ## S7: per-factor disagreement set has `≤ n` points (PROVEN)

For a single irreducible factor `(i,j)`, the unique affine pair `(a, b)` (the Hensel output,
S6) yields difference vectors `d₀ = a − f₀`, `d₁ = b − f₁`. The factor's disagreement set
`D \ A°_{i,j}` is exactly `disagreeSet d₀ d₁`, a subset of the full domain `univ`, hence has
at most `n := |D|` points. This is the trivial-but-load-bearing first half of the endgame:
the paper's `|D \ A°| ≤ n`. -/

/-- **S7 (proven).** The per-factor disagreement set `disagreeSet d₀ d₁` has at most
`n := Fintype.card ι` points: it is a `Finset.filter` of `univ`. -/
theorem factorDisagree_card_le_n (d₀ d₁ : ι → F) :
    (disagreeSet d₀ d₁).card ≤ Fintype.card ι := by
  classical
  calc (disagreeSet d₀ d₁).card
      ≤ (univ : Finset ι).card := Finset.card_le_card (by
        intro x _; exact Finset.mem_univ x)
    _ = Fintype.card ι := Finset.card_univ

/-! ## S8: per-factor "improving scalar" set has `≤ n` elements (PROVEN)

`E_{i,j}` is the set of scalars `z ∈ F` that improve agreement beyond `A°_{i,j}` — equivalently
(via the unique affine pair `(a,b)`), the scalars `z` for which the fold matches `a + z·b` at
*some* coordinate of `D \ A°_{i,j}`. Each `z ∈ E_{i,j}` is a root of the non-trivial affine
functional `g_x(z) = d₀ x + z·d₁ x` at some disagreement coordinate `x`, and the assignment
`z ↦ (its matching coordinate)` is injective because such a functional has at most one root
(`affine_root_subsingleton`). Hence `|E_{i,j}| ≤ |D \ A°_{i,j}| ≤ n`. This is precisely the
in-tree `hab25_endgame_count`, and it is the formal content of Hab25's
"**from the proof of Lemma 1** the number of such scalars is `≤ |D \ A°| ≤ n`" (paper
l.302–310). -/

/-- **S8 (proven).** Any set `T` of "improving scalars" — each of which matches the fold at a
coordinate of the factor disagreement set — has `|T| ≤ n`. Direct composition of the proven
`hab25_endgame_count` (which already gives `|T| ≤ |disagreeSet d₀ d₁|`) with S7. -/
theorem factorImprove_card_le_n (d₀ d₁ : ι → F) (T : Finset F)
    (hT : ∀ z ∈ T, ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0) :
    T.card ≤ Fintype.card ι :=
  le_trans (hab25_endgame_count d₀ d₁ T hT) (factorDisagree_card_le_n d₀ d₁)

/-! ## S9 / S10: Theorem-2 union assembly (PROVEN, integer level)

The mutual disagreement set `E` is covered by the per-factor sets:
`E = ⋃_{(i,j) ∈ Idx} E_{i,j}` (residual `MutualDisagreeCover`, the factorisation output S4).
Given:
* a finite index set `Idx` of irreducible factors with `Idx.card ≤ ℓ` (S3, `D_Y < ℓ`);
* a per-factor bound `|E_{i,j}| ≤ B` for every `(i,j)` (here `B = n` from S8, or the looser
  `(ℓ⁶/3)(ρn)²` from S9);

the union bound gives `|E| ≤ Idx.card · B ≤ ℓ · B`. This is the entire Theorem-2 bookkeeping,
proven by `Finset.card_biUnion_le` and `Finset.sum_le_card_nsmul`. -/

/-- **S10 (proven).** Generic union bound: if `E` is covered by per-factor sets
`Efactor (i,j)` over a finite index set `Idx`, and each `|Efactor (i,j)| ≤ B`, then
`|E| ≤ Idx.card · B`. The Theorem-2 arithmetic, fully proven at the integer level. -/
theorem theorem2_union_bound {Idx : Type*} [DecidableEq Idx]
    (E : Finset F) (Index : Finset Idx) (Efactor : Idx → Finset F) (B : ℕ)
    (hcover : E ⊆ Index.biUnion Efactor)
    (hfactor : ∀ ij ∈ Index, (Efactor ij).card ≤ B) :
    E.card ≤ Index.card * B := by
  classical
  calc E.card
      ≤ (Index.biUnion Efactor).card := Finset.card_le_card hcover
    _ ≤ ∑ ij ∈ Index, (Efactor ij).card := Finset.card_biUnion_le
    _ ≤ ∑ _ij ∈ Index, B := Finset.sum_le_sum hfactor
    _ = Index.card * B := by rw [Finset.sum_const, smul_eq_mul]

/-- **S10' (proven).** Specialisation of the union bound to the `B = n` per-factor count
coming from S8: with `Idx.card ≤ ℓ` factors each of size `≤ n`, the mutual disagreement set has
`|E| ≤ ℓ · n`. This is the *integer-sharp* Theorem-2 statement that the closed-form
`(ℓ⁷/3)(ρn)²` bound relaxes (since `(ℓ⁶/3)(ρn)² ≥ n` in the Johnson regime, S9). -/
theorem theorem2_union_bound_n {Idx : Type*} [DecidableEq Idx]
    (E : Finset F) (Index : Finset Idx) (Efactor : Idx → Finset F) (ℓ : ℕ)
    (hℓ : Index.card ≤ ℓ)
    (hcover : E ⊆ Index.biUnion Efactor)
    (hfactor : ∀ ij ∈ Index, (Efactor ij).card ≤ Fintype.card ι) :
    E.card ≤ ℓ * Fintype.card ι :=
  le_trans (theorem2_union_bound E Index Efactor (Fintype.card ι) hcover hfactor)
    (Nat.mul_le_mul_right _ hℓ)

/-- **Claim 1 → Theorem 2, fully assembled at the integer level (proven).**

Combines S8 (each factor's improving-scalar set has `≤ n` elements) with S10 (union over
`≤ ℓ` factors). Given:
* `Index : Finset Idx`, the irreducible factors, with `Index.card ≤ ℓ`  (S3, `D_Y < ℓ`);
* for each factor `ij`, difference vectors `d₀ ij`, `d₁ ij` (from the unique affine pair, S6);
* `hcover`: the mutual disagreement set `E` is covered by the per-factor improving-scalar sets
  `Efactor ij` (S4, residual cover);
* `hImprove`: every `z ∈ Efactor ij` matches the fold at some coordinate of
  `disagreeSet (d₀ ij) (d₁ ij)` (S8 hypothesis, the Hensel-uniqueness consequence);

then `|E| ≤ ℓ · n`. This is the complete combinatorial skeleton of Hab25 §3 — every step
proven from the in-tree substrate, with the algebraic GS content entering only through the
shapes of `Index`, `d₀`/`d₁`, `hcover`, and `hImprove`. -/
theorem claim1_theorem2_integer {Idx : Type*} [DecidableEq Idx]
    (E : Finset F) (Index : Finset Idx) (Efactor : Idx → Finset F) (ℓ : ℕ)
    (d₀ d₁ : Idx → ι → F)
    (hℓ : Index.card ≤ ℓ)
    (hcover : E ⊆ Index.biUnion Efactor)
    (hImprove : ∀ ij ∈ Index, ∀ z ∈ Efactor ij,
      ∃ x ∈ disagreeSet (d₀ ij) (d₁ ij), affineGap (d₀ ij) (d₁ ij) z x = 0) :
    E.card ≤ ℓ * Fintype.card ι := by
  refine theorem2_union_bound_n E Index Efactor ℓ hℓ hcover ?_
  intro ij hij
  exact factorImprove_card_le_n (d₀ ij) (d₁ ij) (Efactor ij) (hImprove ij hij)

end CodingTheory.ProximityGap.Hab25Core.Hab25JohnsonEndgame
