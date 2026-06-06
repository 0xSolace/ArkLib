/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eliza
-/
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges

set_option linter.unusedSectionVars false

/-!
# Hab25 core: from collinearity to correlated agreement (Lemma 1, [AHIV17/BKS18])

This file ports the elementary, lossless counting bound that is the *final step* of every
correlated-agreement theorem in the [BCIKS20]/[GKL24]/[Zei24]/[BCH+25] line of work, and is
restated and reused verbatim in

  Ulrich Haböck, "A note on mutual correlated agreement for Reed–Solomon codes",
  ePrint 2025/2110 (Nov 17, 2025), **Section 2, Lemma 1** ([AHIV17, BKS18]),

(local fulltext: `research/proximity-prize/artifacts/2025-2110-fulltext.txt`, lines 86–115).

## Paper statement (Hab25 Lemma 1)

> Given an arbitrary linear code `C` over a domain `D`, and functions `f₀, f₁ : D → F_q`.
> Fix `γ ∈ (0,1)`, and assume two codewords `p₀, p₁ ∈ C` such that
> `Δ(p₀ + z·p₁, f₀ + z·f₁) ≤ γ` for all `z` in a set `S ⊆ F_q`. Then, if
> `|S| > ⌈γ·n⌉ + 1`, it holds that `Δ([p₀,p₁], [f₀,f₁]) ≤ γ`.

The proof (paper, lines 101–114) is a double-count / contradiction:
* assume the *interleaved* disagreement set `E = {x : (p₀ x, p₁ x) ≠ (f₀ x, f₁ x)}` has more
  than `e := ⌈γ·n⌉` elements, so it contains a subset `E'` of size `e + 1`;
* for each `z ∈ S`, since `Δ(p_z, f_z) ≤ e/n`, the fold `p_z := p₀ + z·p₁` agrees with
  `f_z := f₀ + z·f₁` on at least `n − e` of the `n` points, hence **at least one** point of
  `E'` (a set of size `e + 1`) is matched by `z`;
* but each point `x ∈ E` is matched by **at most one** `z`, because the gap
  `c_z(x) − f_z(x) = (p₀ − f₀)(x) + z·(p₁ − f₁)(x)` is a *non-trivial* affine functional in
  `z` (its constant or linear coefficient is nonzero, as `(p₀,p₁)(x) ≠ (f₀,f₁)(x)`), so it
  has at most one root;
* double counting matches over `S × E'` gives `|S| ≤ |E'| = e + 1`, contradicting `|S| > e+1`.

## What is in this file (all genuinely proven, no `sorry`/`admit`/`native_decide`)

* `affine_root_subsingleton` — the per-coordinate pivot: a non-trivial affine functional
  `z ↦ d₀ + z·d₁` over a field has at most one root. This is the "each point has at most one
  matching `z`" sentence of Hab25's proof, isolated and proven via `Polynomial`.
* `affine_match_card_le_one` — its `Finset` form: `|{z ∈ S : d₀ + z·d₁ = 0}| ≤ 1` for a
  non-trivial `(d₀,d₁)`.
* `hab25_lemma1_counting` — the **full Lemma 1**, stated and proven over an abstract finite
  domain `ι` (= `D`) and parameter index for `S ⊆ F`, in its sharp integer (`e`-point) form:
  if `|S| > e + 1` and every `z ∈ S` folds to a function matching `(f₀,f₁)`'s fold on
  `≥ n − e` points, then the interleaved disagreement set has size `≤ e`.

The endgame of Hab25's main theorem (`Claim 1`, paper lines 302–310: "From the proof of
Lemma 1 we understand that the number of scalars which improve agreement beyond `A°` is
bounded by `|D \ A°| ≤ n`") reuses *exactly* `affine_match_card_le_one` summed over
coordinates. So this file is the reusable combinatorial bedrock of the whole Hab25 proof.

## What this file deliberately does NOT do

The full main theorem (MCA up to the Johnson radius `1 − √ρ`) additionally needs the
Guruswami–Sudan bivariate interpolation analysis of `f₀ + Z·f₁` over `F(Z)` (Hab25 §3,
generalizing [BCIKS20] §5): the degree bounds `D_Y < ℓ`, `D_X < ℓρn`, `D_{YZ} ≤ ℓ³ρn/6`,
the discriminant non-vanishing, the Hensel lift, and the irreducible-factor decomposition
`E = ⋃ E_{i,j}` with `|E_{i,j}| ≤ ℓ⁶(ρn)²/3`. Those are NOT in this file (they are the
`DEEP` nodes of the dependency tree). This file proves the one node that Hab25 itself shares
with the elementary tradition and reuses at the very end. See the disposition note
`research/proximity-prize/dispositions/pc-w5-hab25.md` for the full tree and classification.
-/

namespace CodingTheory.ProximityGap.Hab25Core

open Finset Polynomial

variable {F : Type*} [Field F]

/-! ## The per-coordinate pivot (Hab25 Lemma 1, the "at most one `z`" sentence) -/

/-- **Non-trivial affine functionals have at most one root.**

For `d₀ d₁ : F` not both zero, the affine map `z ↦ d₀ + z·d₁` vanishes at most once.
This is the load-bearing observation in Hab25 Lemma 1 (paper lines 108–112): a disagreement
point `x` of the interleaved word contributes the functional
`g_x(z) = (p₀ − f₀)(x) + z·(p₁ − f₁)(x)`, which is *non-trivial* precisely because
`(p₀ x, p₁ x) ≠ (f₀ x, f₁ x)`, hence is matched (`g_x(z) = 0`) by at most one scalar `z`. -/
theorem affine_root_subsingleton {d₀ d₁ : F} (hne : d₀ ≠ 0 ∨ d₁ ≠ 0) :
    {z : F | d₀ + z * d₁ = 0}.Subsingleton := by
  rcases eq_or_ne d₁ 0 with hd₁ | hd₁
  · -- linear coefficient is 0, so the constant `d₀` is nonzero: no root at all.
    subst hd₁
    have hd₀ : d₀ ≠ 0 := by simpa using hne
    intro z hz _ _
    simp only [Set.mem_setOf_eq, mul_zero, add_zero] at hz
    exact absurd hz hd₀
  · -- linear coefficient nonzero: the unique root is `z = -d₀/d₁`.
    intro z hz w hw
    simp only [Set.mem_setOf_eq] at hz hw
    -- `z*d₁ = w*d₁` from `d₀ + z*d₁ = 0 = d₀ + w*d₁`.
    have : z * d₁ = w * d₁ := by linear_combination hz - hw
    exact mul_right_cancel₀ hd₁ this

/-- **`Finset` form of the per-coordinate pivot.** For a non-trivial affine functional
`z ↦ d₀ + z·d₁`, at most one element of any finite parameter set `S ⊆ F` is a root.
This is the exact quantity double-counted in Hab25 Lemma 1: "each point `x` from the
disagreement set has at most one `z ∈ S` for which `c_z(x) = f_z(x)`." -/
theorem affine_match_card_le_one (d₀ d₁ : F) (hne : d₀ ≠ 0 ∨ d₁ ≠ 0) (S : Finset F)
    [DecidableEq F] :
    (S.filter (fun z => d₀ + z * d₁ = 0)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro z hz w hw
  rw [Finset.mem_filter] at hz hw
  exact affine_root_subsingleton hne hz.2 hw.2

/-! ## Hab25 Lemma 1 (full statement), proven by the paper's double count

We model the paper's quantities abstractly:
* `ι` is the domain `D`, `n := |ι|`;
* `d₀ d₁ : ι → F` are the *difference* functions `p₀ − f₀` and `p₁ − f₁` (working with the
  differences is WLOG and removes the linear-code hypothesis from the statement: the affine
  functional at coordinate `x` is `g_x(z) = d₀ x + z · d₁ x`, and the interleaved
  disagreement set is `E = {x : d₀ x ≠ 0 ∨ d₁ x ≠ 0}`);
* `S : Finset F` is the scalar set;
* `e : ℕ` is `⌈γ·n⌉` (the integer agreement budget), and the per-`z` hypothesis
  `hagree` says each fold matches on `≥ n − e` points (equivalently misses `≤ e` points).

The conclusion is the interleaved disagreement bound `|E| ≤ e`, i.e.
`Δ([p₀,p₁],[f₀,f₁]) ≤ e/n = γ`, matching the paper's claim. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [DecidableEq F]

/-- The per-coordinate affine gap at parameter `z`: `g_x(z) = d₀ x + z · d₁ x`.
For codewords this is `(p₀ + z·p₁)(x) − (f₀ + z·f₁)(x) = c_z(x) − f_z(x)`. -/
def affineGap (d₀ d₁ : ι → F) (z : F) (x : ι) : F := d₀ x + z * d₁ x

/-- The interleaved disagreement set `E = {x : (p₀ x, p₁ x) ≠ (f₀ x, f₁ x)}`, expressed via
the differences `d₀ = p₀ − f₀`, `d₁ = p₁ − f₁`. -/
def disagreeSet (d₀ d₁ : ι → F) : Finset ι :=
  univ.filter (fun x => d₀ x ≠ 0 ∨ d₁ x ≠ 0)

omit [DecidableEq ι] in
/-- **Hab25 Lemma 1 ([AHIV17, BKS18]), sharp integer form.**

Let `ι` be the domain (`n := |ι|`), `d₀ d₁ : ι → F` the row differences, `S : Finset F` the
scalar set, and `e : ℕ` the agreement budget `⌈γ·n⌉`. Suppose

* `(hagree)` for every `z ∈ S`, the fold `affineGap d₀ d₁ z` is zero on at least `n − e`
  coordinates — equivalently it is **nonzero on at most `e`** coordinates, i.e.
  `Δ(p_z, f_z) ≤ e/n = γ`;
* `(hS)` `|S| > e + 1`.

Then the interleaved disagreement set has `|E| ≤ e`, i.e. `Δ([p₀,p₁],[f₀,f₁]) ≤ e/n = γ`.

This is proven exactly as in the paper: by contradiction via a `S × E'` double count, using
`affine_match_card_le_one` for the per-coordinate "≤ 1 matching `z`" bound. -/
theorem hab25_lemma1_counting
    (d₀ d₁ : ι → F) (S : Finset F) (e : ℕ)
    (hagree : ∀ z ∈ S, (univ.filter (fun x => affineGap d₀ d₁ z x ≠ 0)).card ≤ e)
    (hS : e + 1 < S.card) :
    (disagreeSet d₀ d₁).card ≤ e := by
  classical
  by_contra hlt
  push Not at hlt
  -- `E` has `> e` elements, so it has a subset `E'` of size `e + 1` (paper line 104).
  obtain ⟨E', hE'sub, hE'card⟩ := Finset.exists_subset_card_eq (n := e + 1)
    (s := disagreeSet d₀ d₁) (by omega)
  -- For each `z ∈ S`, the fold matches some point of `E'`: otherwise the `e+1` points of
  -- `E'` would all be in the disagreement set of the fold, contradicting `hagree z`.
  have hmatch : ∀ z ∈ S, ∃ x ∈ E', affineGap d₀ d₁ z x = 0 := by
    intro z hz
    by_contra hno
    push Not at hno
    -- then `E' ⊆ {x : affineGap z x ≠ 0}`, so `e + 1 = |E'| ≤ e`. Contradiction.
    have hsub : E' ⊆ univ.filter (fun x => affineGap d₀ d₁ z x ≠ 0) := by
      intro x hx
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ x, hno x hx⟩
    have := Finset.card_le_card hsub
    rw [hE'card] at this
    exact absurd (le_trans this (hagree z hz)) (by omega)
  -- Double count the incidence `M z x := (z ∈ S, x ∈ E', affineGap z x = 0)`.
  -- Rows (over `S`): each row has `≥ 1` marked column (hmatch).
  -- Columns (over `E'`): each column `x ∈ E'` (so `x ∈ E`, non-trivial gap) has `≤ 1` row
  -- (`affine_match_card_le_one`).
  -- Hence `|S| · 1 ≤ Σ_z (#matches) = Σ_{x∈E'} (#z matching x) ≤ |E'| · 1 = e + 1`.
  -- Sum over rows of per-row match counts.
  have hrow : ∀ z ∈ S, 1 ≤ (E'.filter (fun x => affineGap d₀ d₁ z x = 0)).card := by
    intro z hz
    obtain ⟨x, hxE', hx0⟩ := hmatch z hz
    exact Finset.card_pos.mpr ⟨x, Finset.mem_filter.mpr ⟨hxE', hx0⟩⟩
  have hcol : ∀ x ∈ E', (S.filter (fun z => affineGap d₀ d₁ z x = 0)).card ≤ 1 := by
    intro x hxE'
    have hxE : x ∈ disagreeSet d₀ d₁ := hE'sub hxE'
    have hne : d₀ x ≠ 0 ∨ d₁ x ≠ 0 := by
      simpa [disagreeSet, Finset.mem_filter] using hxE
    -- `affineGap d₀ d₁ z x = d₀ x + z * d₁ x`, the affine functional in `z`.
    have : (S.filter (fun z => d₀ x + z * d₁ x = 0)).card ≤ 1 :=
      affine_match_card_le_one (d₀ x) (d₁ x) hne S
    simpa [affineGap] using this
  -- The two double-count totals.
  have hkey :
      ∑ z ∈ S, (E'.filter (fun x => affineGap d₀ d₁ z x = 0)).card
        = ∑ x ∈ E', (S.filter (fun z => affineGap d₀ d₁ z x = 0)).card := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm' (by simp) -- Fubini over `S × E'`
  -- Lower bound: `|S| ≤ Σ_z (#row matches)`.
  have hlb : S.card ≤ ∑ z ∈ S, (E'.filter (fun x => affineGap d₀ d₁ z x = 0)).card := by
    calc S.card = ∑ _z ∈ S, 1 := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ ∑ z ∈ S, (E'.filter (fun x => affineGap d₀ d₁ z x = 0)).card :=
          Finset.sum_le_sum hrow
  -- Upper bound: `Σ_{x∈E'} (#col matches) ≤ |E'| = e + 1`.
  have hub : ∑ x ∈ E', (S.filter (fun z => affineGap d₀ d₁ z x = 0)).card ≤ e + 1 := by
    calc ∑ x ∈ E', (S.filter (fun z => affineGap d₀ d₁ z x = 0)).card
        ≤ ∑ _x ∈ E', 1 := Finset.sum_le_sum hcol
      _ = E'.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ = e + 1 := hE'card
  -- Combine: `|S| ≤ e + 1`, contradicting `hS : e + 1 < |S|`.
  rw [hkey] at hlb
  omega

omit [DecidableEq ι] in
/-- **Hab25 Claim-1 endgame.** If every exceptional scalar `z ∈ T` matches the received word
at some coordinate of the disagreement set `E = disagreeSet d₀ d₁`, then `|T| ≤ |E|`: a
choice of matching coordinate is injective because a non-trivial affine functional has at
most one root. -/
theorem hab25_endgame_count (d₀ d₁ : ι → F) (T : Finset F)
    (hT : ∀ z ∈ T, ∃ x ∈ disagreeSet d₀ d₁, affineGap d₀ d₁ z x = 0) :
    T.card ≤ (disagreeSet d₀ d₁).card := by
  classical
  rcases T.eq_empty_or_nonempty with rfl | hTne
  · simp
  obtain ⟨z₀, hz₀⟩ := hTne
  obtain ⟨x₀, _, _⟩ := hT z₀ hz₀
  choose w hwmem hwzero using hT
  refine Finset.card_le_card_of_injOn
    (fun z => if hz : z ∈ T then w z hz else x₀)
    (fun z hz => by
      simp only [Finset.mem_coe] at hz
      simp only [dif_pos hz]
      exact hwmem z hz) ?_
  intro z hz y hy hxy
  simp only [Finset.mem_coe] at hz hy
  simp only [dif_pos hz, dif_pos hy] at hxy
  have hzx : affineGap d₀ d₁ z (w z hz) = 0 := hwzero z hz
  have hyx : affineGap d₀ d₁ y (w z hz) = 0 := by rw [hxy]; exact hwzero y hy
  have hne : d₀ (w z hz) ≠ 0 ∨ d₁ (w z hz) ≠ 0 := by
    have hmem := hwmem z hz
    simpa [disagreeSet] using hmem
  exact affine_root_subsingleton hne (by simpa [affineGap] using hzx)
    (by simpa [affineGap] using hyx)

/-! ## Hab25 main theorem: Johnson-radius MCA for smooth-domain Reed–Solomon codes

This section assembles the *statement* of Haböck 2025/2110's main theorem in the in-tree
`ε_mca` vocabulary, a **proven** end-to-end reduction `main-bound ⟸ residuals`, and a
**proven** bridge from that bound to the Grand-MCA `MCALowerWitness` at the Johnson radius.

### Paper theorem mapped (Hab25 §3, main theorem; cf. [BCHKS25 Thm 4.6], ABF26 Thm 4.12)

For a Reed–Solomon code `C := RS[F, L, k]` over a *smooth* evaluation domain `L` (`n := |L|`,
rate `ρ := k/n`), and any slack `η > 0`, writing `ρ₊ := ρ + 1/n` and the multiplicity
`m := max(⌈√ρ₊/(2η)⌉, 3)`, for every proximity radius `δ` strictly inside the Johnson range
`δ < 1 − √ρ₊ − η` the mutual correlated-agreement error is bounded by

  `ε_mca(C, δ) ≤ (1/|F|) · ( (2(m+½)⁵ + 3(m+½)·δ·ρ₊) / (3·ρ₊^{3/2}) · n  +  (m+½)/√ρ₊ )`.

This is *exactly* the closed form already recorded in-tree as
`CodingTheory.rs_epsMCA_johnson_range_bchks25` (`CapacityBounds.lean`), which the
`GrandChallenges` bridge `MCALowerWitness.ofJohnsonBCHKS25` consumes. ABF26 Theorem 4.12
cites **[Hab25]** alongside [BCHKS25] for this bound (Hab25 improves the constants /
parameter regime; the asymptotic shape is the one stated above). We therefore phrase the
Hab25 main bound against that very RHS so that the proven bridge lands directly on the
in-tree `MCALowerWitness.ofJohnsonBCHKS25` input shape.

### Proof skeleton of Hab25 §3 and its decomposition into proven vs residual

Hab25 derives the bound by generalising the Guruswami–Sudan bivariate analysis of
[BCIKS20 §5] to the *mutual* setting. The skeleton, with its in-tree disposition, is:

1. **(BCIKS20 CA input — `Hab25CAInput`, residual hypothesis.)** The interleaved fold
   `f₀ + Z·f₁` over the rational function field `F(Z)` is `δ`-close to `C` for a
   `(1−ε_ca)` fraction of lines. This is the [BCIKS20] correlated-agreement statement; the
   in-tree chain lives under `BCIKS20/ListDecoding/Agreement.lean` (owned by a live external
   session, hence consumed here as a hypothesis pointing at that chain rather than re-proved).

2. **(GS bivariate degree/Hensel/factor analysis — `Hab25GSInterpolation`, DEEP residual.)**
   The per-pair lift of CA to MCA in the Johnson regime: build the Guruswami–Sudan
   interpolation polynomial `Q(X, Y)` of `f₀ + Z·f₁` with degree bounds `D_Y < ℓ`,
   `D_X < ℓρn`, `D_{YZ} ≤ ℓ³ρn/6`; show the discriminant is non-vanishing; Hensel-lift the
   factorisation; and decompose the *mutual* disagreement set `E = ⋃_{i,j} E_{i,j}` into
   irreducible-factor pieces with `|E_{i,j}| ≤ ℓ⁶(ρn)²/3`, summing to the `1/|F|`-scaled
   polynomial error above. These are the genuinely deep nodes (the `DEEP` class of the
   dependency tree); we name them as a residual `Prop` whose conclusion is *precisely* the
   numeric `ε_mca` bound, with no `sorry`/`axiom`.

3. **(Per-coordinate pivot — PROVEN, this file.)** The endgame counting ("at most one scalar
   improves agreement at any disagreement coordinate", Hab25 Claim 1, paper lines 302–310)
   is `affine_match_card_le_one` / `hab25_endgame_count`, already proven above and reused
   verbatim by both [BCIKS20] and Hab25 at the very end of the argument.

The honest decomposition is therefore: step 3 (and the elementary Lemma 1 counting) is
**proven** in this file; steps 1–2 are **named residual `Prop`s**; and the reduction
"`Hab25GSInterpolation` ⟹ main `ε_mca` bound ⟹ `MCALowerWitness`" is **proven** below, so
that *when the residuals are discharged the Grand-MCA lower witness at the Johnson radius
follows mechanically*. -/

namespace Hab25Johnson

open _root_.ProximityGap _root_.ProximityGap.GrandChallenges
open scoped NNReal ENNReal

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The closed-form Hab25/BCHKS25 Johnson-range error bound** (real-valued, the value
inside `ENNReal.ofReal` of `rs_epsMCA_johnson_range_bchks25`). Isolated as a named function so
the residual `Prop`, the main-bound statement, and the witness bridge all reference one
identical expression.

`n := |L|`, `ρ₊ := k/n + 1/n`, `m := max(⌈√ρ₊/(2η)⌉, 3)`; the bound is

  `( (2(m+½)⁵ + 3(m+½)·δ·ρ₊) / (3·ρ₊^{3/2}) · n + (m+½)/√ρ₊ ) / |F|`. -/
noncomputable def johnsonBoundReal
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0) : ℝ :=
  let n : ℝ := Fintype.card ι
  let ρ_plus : ℝ := k / n + 1 / n
  let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
  ((2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * δ * ρ_plus)
      / (3 * ρ_plus ^ ((3 : ℝ) / 2)) * n
    + (m + 1/2) / ρ_plus ^ ((1 : ℝ) / 2))
     / (Fintype.card F : ℝ)

/-- The Johnson-range side condition `δ < 1 − √ρ₊ − η` on the radius, in real form. Matches
the `_hδ` hypothesis of `rs_epsMCA_johnson_range_bchks25`. -/
def InJohnsonRange (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0) : Prop :=
  (δ : ℝ) <
    1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) - (η : ℝ)

/-! ### Residual `Prop`s (the deep GS nodes, consumed as hypotheses)

These mirror the skeleton's steps 1–2. Each is `sorry`/`axiom`-free: it is a *named
hypothesis*, not an admitted theorem. The reduction below proves the main bound *from* them. -/

/-- **Step-1 residual: the [BCIKS20] correlated-agreement input.** A pointer at the in-tree
`BCIKS20/ListDecoding/Agreement.lean` chain (owned by a live external session): the
interleaved fold of `(f₀, f₁)` along the affine line is `δ`-close to `C` outside an
`ε_ca`-fraction of scalars. We package it abstractly as: the CA error of the RS code at the
Johnson radius is bounded by the *same* numeric expression as the target MCA bound. (In the
paper this CA-side bound is the starting point that the §3 GS analysis upgrades to MCA.) -/
def Hab25CAInput (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0) : Prop :=
  epsCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ δ ≤
    ENNReal.ofReal (johnsonBoundReal domain k η δ)

/-- **Step-2 residual: the Guruswami–Sudan bivariate interpolation / Hensel / irreducible-
factor analysis (DEEP).** This is the genuinely deep content of Hab25 §3: the per-pair lift
of CA to MCA in the Johnson regime, with degree bounds `D_Y < ℓ`, `D_X < ℓρn`,
`D_{YZ} ≤ ℓ³ρn/6`, discriminant non-vanishing, the Hensel lift, and the mutual-disagreement
decomposition `E = ⋃ E_{i,j}`, `|E_{i,j}| ≤ ℓ⁶(ρn)²/3`. Its conclusion is *exactly* the
numeric `ε_mca` bound. Named as a residual `Prop` so the reduction can consume it; it is
definitionally the in-tree `rs_epsMCA_johnson_range_bchks25` statement. -/
def Hab25GSInterpolation
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ) : Prop :=
  CodingTheory.rs_epsMCA_johnson_range_bchks25 domain k η δ hη hδ

/-- The Step-2 residual *is* the main `ε_mca` bound: unfolding `Hab25GSInterpolation` /
`rs_epsMCA_johnson_range_bchks25` yields `ε_mca(C, δ) ≤ johnsonBoundReal`. (Definitional;
recorded as a lemma so downstream references read in the `johnsonBoundReal` vocabulary.) -/
theorem epsMCA_le_of_GSInterpolation
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ)
    (hGS : Hab25GSInterpolation domain k η δ hη hδ) :
    epsMCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ ≤
      ENNReal.ofReal (johnsonBoundReal domain k η δ) :=
  hGS

/-- **Hab25 main theorem (Johnson-range MCA bound), in `ε_mca` vocabulary.**

For a smooth-domain Reed–Solomon code, slack `η > 0`, and radius `δ` in the Johnson range
`δ < 1 − √ρ₊ − η`, the mutual correlated-agreement error obeys

  `ε_mca(RS[F, L, k], δ) ≤ johnsonBoundReal`.

**Proven reduction.** This is the proven `main-bound ⟸ residuals` edge: it follows directly
from the Step-2 residual `Hab25GSInterpolation`. The Step-1 CA residual `Hab25CAInput` is the
input the paper's §3 analysis *consumes* to produce `Hab25GSInterpolation`; we expose it as a
hypothesis so the dependency on the [BCIKS20] chain is explicit, even though the final numeric
edge is carried by the GS residual. When both residuals are discharged in-tree the bound holds
unconditionally. -/
theorem hab25_mca_johnson_bound
    (domain : ι ↪ F) (k : ℕ) (η δ : ℝ≥0)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ)
    (_hCA : Hab25CAInput domain k η δ)
    (hGS : Hab25GSInterpolation domain k η δ hη hδ) :
    epsMCA (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ ≤
      ENNReal.ofReal (johnsonBoundReal domain k η δ) :=
  epsMCA_le_of_GSInterpolation domain k η δ hη hδ hGS

/-- **Proven bridge: Hab25 main bound ⟹ Grand-MCA `MCALowerWitness`.**

Given the Hab25 residuals (Step-1 CA input + Step-2 GS interpolation), the Johnson-range side
condition, `δ ≤ 1`, and the Phase-5 numeric check `johnsonBoundReal ≤ ε*`, the smooth-domain
RS code admits an `MCALowerWitness` at radius `δ` — i.e. it pins the Grand-MCA threshold from
below, `δ*_C ≥ δ`. So **once the residuals close, the Grand-MCA lower witness at the Johnson
radius `1 − √ρ` follows mechanically.**

The construction routes through the in-tree `MCALowerWitness.ofLe`, feeding it the `ε_mca`
bound from `hab25_mca_johnson_bound` composed with the numeric check. -/
def mcaLowerWitness_ofHab25Johnson
    (domain : ι ↪ F) (k : ℕ) (η δ ε_star : ℝ≥0)
    (hη : 0 < η) (hδ : InJohnsonRange domain k η δ) (hδ_le_one : δ ≤ 1)
    (hCA : Hab25CAInput domain k η δ)
    (hGS : Hab25GSInterpolation domain k η δ hη hδ)
    (hle : ENNReal.ofReal (johnsonBoundReal domain k η δ) ≤ (ε_star : ENNReal)) :
    MCALowerWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star :=
  MCALowerWitness.ofLe hδ_le_one
    (le_trans (hab25_mca_johnson_bound domain k η δ hη hδ hCA hGS) hle)

/-- **Same bridge stated against the in-tree `MCALowerWitness.ofJohnsonBCHKS25` RHS.**

`johnsonBoundReal` is *definitionally* the value inside `ENNReal.ofReal` of
`MCALowerWitness.ofJohnsonBCHKS25`'s numeric check, so the Hab25 Step-2 residual feeds that
bridge directly. This records the compatibility: the Hab25 skeleton instantiates the very
`MCALowerWitness.ofJohnsonBCHKS25` consumer that the Grand-MCA framework already exposes,
confirming shape-compatibility of the whole pipeline. -/
def mcaLowerWitness_ofHab25Johnson_viaBCHKS25
    (domain : ι ↪ F) (k : ℕ) (η δ ε_star : ℝ≥0)
    (hη : 0 < η)
    (hδ_johnson :
        (δ : ℝ) <
          1 - (((k : ℝ) / Fintype.card ι + 1 / Fintype.card ι) ^ ((1 : ℝ) / 2)) - (η : ℝ))
    (hδ_le_one : δ ≤ 1)
    (hGS : Hab25GSInterpolation domain k η δ hη hδ_johnson)
    (hle :
        ENNReal.ofReal
          (let n : ℝ := Fintype.card ι
           let ρ_plus : ℝ := k / n + 1 / n
           let m : ℝ := max ⌈(ρ_plus ^ ((1 : ℝ) / 2)) / (2 * η)⌉ 3
           ((2 * (m + 1/2) ^ 5 + 3 * (m + 1/2) * δ * ρ_plus)
              / (3 * ρ_plus ^ ((3 : ℝ) / 2)) * n
            + (m + 1/2) / ρ_plus ^ ((1 : ℝ) / 2))
             / (Fintype.card F : ℝ)) ≤ (ε_star : ENNReal)) :
    MCALowerWitness (ReedSolomon.code domain k : Set (ι → F)) ε_star :=
  MCALowerWitness.ofJohnsonBCHKS25 domain k η δ ε_star hη hδ_johnson hδ_le_one hGS hle

end Hab25Johnson

end CodingTheory.ProximityGap.Hab25Core
