/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.Frontier.PencilAutocorrelation
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._KelleyOwenDilationPencil

set_option linter.style.longLine false

/-!
# LEVER K, completed: the M=1 autocorrelation hypothesis YIELDS the Stepanov √N root bound (#407/#444)

`PencilAutocorrelation.lean` proved the **bridge** (the pencil overlap is exactly the multiplicative
autocorrelation of the root set `S`, `inter_dilate_eq_autocorr`) and, at the `M = 1` extreme, that
the *punctured* pencil blocks are pairwise **disjoint**
(`punctured_blocks_disjoint_of_autocorr_le_one`). Its own docstring asserts that this *"recovers
`KelleyOwenDilationPencil.pencil_card_core`, here re-derived from the autocorrelation viewpoint"*,
but it **never actually performs that derivation**: it stops at punctured-disjointness and never
produces the root-count inequality `r·(r−1)+1 ≤ n`.

`_KelleyOwenDilationPencil.lean` proves `pencil_card_core` (a family of `r` size-`r` blocks through a
common point, pairwise meeting **exactly** at that point ⟹ `r·(r−1)+1 ≤ |univ|`) and the extraction
`stepanov_sqrt_bound` (`r·(r−1)+1 ≤ N ⟹ (r−1)² < N`). But it consumes the **exact-singleton**
intersection hypothesis `Bᵢ ∩ Bⱼ = {p}` indexed over `Fin r`, NOT the autocorrelation bound.

This file supplies the **missing wiring** between the two (the brick that makes LEVER K's docstring
claim true):

1. `pencil_inter_eq_singleton_of_autocorr_le_one` : `M(S) ≤ 1` + distinct roots `ζᵢ ≠ ζⱼ ∈ S` ⟹ the
   **full** (un-punctured) blocks meet in **exactly** `{1}`: `pencilBlock ζᵢ S ∩ pencilBlock ζⱼ S = {1}`.
   (The autocorr file only gave the *punctured* disjointness; the exact-singleton form, which
   `pencil_card_core` requires, is upgraded here using `1 ∈` both blocks.)

2. `pencil_card_bound_of_autocorr_le_one` : the assembled root-count bound, in the autocorrelation
   language: `M(S) ≤ 1` over the order-`n` subgroup `μ ⊆ G` with `S ⊆ μ`, `|S| = r ≥ 1`, ⟹
   `r·(r−1)+1 ≤ n`. (We enumerate `S` by an equiv `S ≃ Fin r` to build the `Fin r`-indexed block
   family `pencil_card_core` consumes, and discharge its hypotheses from (1).)

3. `pencil_sqrt_bound_of_autocorr_le_one` : the Stepanov `√n` conclusion `(r−1)² < n` (i.e.
   `r ≤ ½ + √n`), via `stepanov_sqrt_bound`.

So in the clean, **field-free** autocorrelation language the whole `t = 3` / trinomial face of the
prize agreement polynomial is now end-to-end: an `M = 1` autocorrelation of the root set forces
`O(√n)` roots in the order-`n` subgroup. This is the `M = 1` extreme the autocorr docstring promised.

## Honest scope (the SAME limit `PencilAutocorrelation.autocorr_ge_coset_core` already pins)

This is **NOT** a closure of the prize. The `M ≤ 1` hypothesis is exactly the trinomial (`t = 3`,
`k = 1`) face. For the prize-relevant general `t = k+2` worst case `S = (coset of size n/2) ∪
{straggler}`, the companion obstruction `autocorr_ge_coset_core` gives `M(S) ≥ n/2`, so the `M ≤ 1`
hypothesis **fails** and this bound is **inapplicable** (exactly as it should be): the dilation-pencil
double-count over the full `S` provably reaches only Johnson there, never sub-Johnson. This file is
the proven `t=3` rung in autocorrelation form, NOT the wall. The prize CORE
`M(μ_n) ≤ C·√(n·log(p/n))` stays OPEN. Probe-verified on PROPER thin 2-power subgroups
(`scripts/probes/probe_pencil_autocorr_rootbound.py`): every `M = 1` set satisfies
`r·(r−1)+1 ≤ n` and `(r−1)² < n` and respects the `½+√n` ceiling, while every coset-core set has
`M(S) ≥ d` (hypothesis fails).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.
-/

open Finset

namespace ProximityGap.Frontier.PencilAutocorrRootBound

open ProximityGap.Frontier.PencilAutocorrelation
open ProximityGap.Frontier.KelleyOwenDilationPencil

variable {G : Type*} [CommGroup G] [DecidableEq G]

/-- **Exact-singleton upgrade.** If the multiplicative autocorrelation of `S` is `≤ 1` at every
nontrivial shift, then for distinct roots `ζᵢ ≠ ζⱼ` in `S` the **full** pencil blocks meet in
**exactly** `{1}`:

  `pencilBlock ζᵢ S ∩ pencilBlock ζⱼ S = {1}`.

This is the exact-singleton intersection hypothesis `pencil_card_core` consumes (strictly stronger
than the punctured-disjointness `punctured_blocks_disjoint_of_autocorr_le_one` already proves, since
it also fixes the common point). `⊇`: both blocks contain `1` (as `ζᵢ, ζⱼ ∈ S`). `⊆`: the bridge
`inter_dilate_eq_autocorr` turns the intersection into `|S ∩ ρ·S| ≤ 1` (`ρ = ζⱼζᵢ⁻¹ ≠ 1` by
distinctness), and a set of card `≤ 1` containing `1` is exactly `{1}`. -/
theorem pencil_inter_eq_singleton_of_autocorr_le_one {S : Finset G}
    (hM : ∀ ρ : G, ρ ≠ 1 → (S ∩ dilate ρ S).card ≤ 1)
    {zi zj : G} (hzi : zi ∈ S) (hzj : zj ∈ S) (hne : zi ≠ zj) :
    pencilBlock zi S ∩ pencilBlock zj S = {1} := by
  have h1mem : (1 : G) ∈ pencilBlock zi S ∩ pencilBlock zj S :=
    Finset.mem_inter.mpr ⟨one_mem_pencilBlock hzi, one_mem_pencilBlock hzj⟩
  -- the shift ρ = zj zi⁻¹ is ≠ 1 by distinctness
  have hρne : (zj * zi⁻¹) ≠ 1 := by
    intro h
    apply hne
    have : zj * zi⁻¹ * zi = (1 : G) * zi := by rw [h]
    rw [inv_mul_cancel_right, one_mul] at this
    exact this.symm
  have hcardle : (pencilBlock zi S ∩ pencilBlock zj S).card ≤ 1 := by
    rw [inter_dilate_eq_autocorr]; exact hM _ hρne
  -- a finset of card ≤ 1 containing 1 equals {1}
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨h1mem, ?_⟩
  intro x hx
  by_contra hxne
  -- {1, x} ⊆ inter has card 2 > 1, contradiction
  have hsub : ({1, x} : Finset G) ⊆ pencilBlock zi S ∩ pencilBlock zj S := by
    intro y hy
    rw [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl
    · exact h1mem
    · exact hx
  have hc2 : ({1, x} : Finset G).card = 2 := by
    rw [Finset.card_insert_of_notMem
          (by rw [Finset.mem_singleton]; exact fun h => hxne h.symm),
      Finset.card_singleton]
  have := Finset.card_le_card hsub
  rw [hc2] at this
  omega

/-- **The root-count bound, assembled in autocorrelation language.** Let `μ ⊆ G` be the order-`n`
multiplicative subgroup (as a `Finset`) and `S ⊆ μ` the root set with `|S| = r ≥ 1`. If the
multiplicative autocorrelation of `S` is `≤ 1` at every nontrivial shift (the `M = 1` / trinomial
face), then

  `r·(r−1) + 1 ≤ n`.

We build the `Fin r`-indexed block family `pencil_card_core` needs by enumerating `S` through the
canonical equiv `S ≃ Fin r`: block `i` is `pencilBlock (e i) S` for the `i`-th element of `S`. Each
block has card `r` (`card_pencilBlock`), all contain `1` (`one_mem_pencilBlock`, since `e i ∈ S`),
and distinct blocks meet exactly at `{1}` (the singleton upgrade above, distinctness from `e`
injective). Every block sits inside the `μ`-translate set, and `pencilBlock z S ⊆ μ` when `z ∈ μ`
and `S ⊆ μ` (a subgroup is closed under the dilation `z⁻¹·x`), so the common universe is `μ` with
`|μ| = n`. -/
theorem pencil_card_bound_of_autocorr_le_one {μ S : Finset G} {n r : ℕ}
    (hμcard : μ.card = n)
    (hSμ : S ⊆ μ)
    (hμmul : ∀ a ∈ μ, ∀ b ∈ μ, a * b ∈ μ)
    (hμinv : ∀ a ∈ μ, a⁻¹ ∈ μ)
    (hr : S.card = r) (hr1 : 1 ≤ r)
    (hM : ∀ ρ : G, ρ ≠ 1 → (S ∩ dilate ρ S).card ≤ 1) :
    r * (r - 1) + 1 ≤ n := by
  classical
  -- enumerate S by an equiv with Fin r
  have hcardS : S.card = r := hr
  let e : Fin r ≃ {x // x ∈ S} := (Fintype.equivFinOfCardEq (by simp [hcardS])).symm
  -- the block family
  let B : Fin r → Finset G := fun i => pencilBlock (e i : G) S
  -- pencilBlock z S ⊆ μ for z ∈ μ: every w ∈ pencilBlock z S has z*w ∈ S ⊆ μ, so
  -- w = z⁻¹ * (z*w) ∈ μ (closure under inv + mul).
  have hBμ : ∀ i, B i ⊆ μ := by
    intro i x hx
    have hzμ : (e i : G) ∈ μ := hSμ (e i).2
    rw [mem_pencilBlock] at hx
    have hzx : (e i : G) * x ∈ μ := hSμ hx
    have : (e i : G)⁻¹ * ((e i : G) * x) ∈ μ := hμmul _ (hμinv _ hzμ) _ hzx
    simpa [inv_mul_cancel_left] using this
  -- apply pencil_card_core with univ = μ, common point 1
  have key : r * (r - 1) + 1 ≤ μ.card := by
    apply pencil_card_core μ r hr1 B (1 : G) hBμ
    · -- each block has card r
      intro i
      change (pencilBlock (e i : G) S).card = r
      rw [card_pencilBlock, hr]
    · -- every block contains 1
      intro i; exact one_mem_pencilBlock (e i).2
    · -- pairwise intersection = {1}
      intro i j hij
      have hzij : (e i : G) ≠ (e j : G) := by
        intro h
        apply hij
        have : e i = e j := Subtype.ext h
        exact e.injective this
      exact pencil_inter_eq_singleton_of_autocorr_le_one hM (e i).2 (e j).2 hzij
  rwa [hμcard] at key

/-- **The Stepanov `√n` conclusion, in autocorrelation language.** From the `M = 1` autocorrelation
of the root set `S` (`|S| = r ≥ 1`) inside the order-`n` subgroup `μ`,

  `(r − 1)² < n`,

i.e. `r − 1 < √n`, `r ≤ ½ + √n`. This is `pencil_card_bound_of_autocorr_le_one` chained through
`stepanov_sqrt_bound` , the `t = 3` / trinomial face of the prize agreement polynomial has `O(√n)`
roots in the order-`n` subgroup, with the `√` in the **subgroup order** `n`, not the field size. -/
theorem pencil_sqrt_bound_of_autocorr_le_one {μ S : Finset G} {n r : ℕ}
    (hμcard : μ.card = n)
    (hSμ : S ⊆ μ)
    (hμmul : ∀ a ∈ μ, ∀ b ∈ μ, a * b ∈ μ)
    (hμinv : ∀ a ∈ μ, a⁻¹ ∈ μ)
    (hr : S.card = r) (hr1 : 1 ≤ r)
    (hM : ∀ ρ : G, ρ ≠ 1 → (S ∩ dilate ρ S).card ≤ 1) :
    (r - 1) * (r - 1) < n :=
  stepanov_sqrt_bound
    (pencil_card_bound_of_autocorr_le_one hμcard hSμ hμmul hμinv hr hr1 hM)

end ProximityGap.Frontier.PencilAutocorrRootBound

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Frontier.PencilAutocorrRootBound.pencil_inter_eq_singleton_of_autocorr_le_one
#print axioms ProximityGap.Frontier.PencilAutocorrRootBound.pencil_card_bound_of_autocorr_le_one
#print axioms ProximityGap.Frontier.PencilAutocorrRootBound.pencil_sqrt_bound_of_autocorr_le_one
