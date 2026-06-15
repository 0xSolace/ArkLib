/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumDilationRecursion

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option autoImplicit false

/-!
# The ORBIT-REDUCTION of the subgroup Gauss period (I031 foundation, #334/#357/#407)

The campaign's best lead (handle **I031**): the Gauss period `η_b(G) = ∑_{x∈G} ψ(b·x)` over the
smooth `2^μ`-subgroup `G = μ_n ⊆ F^*` is **orbit-invariant** — `η_{ζ·b} = η_b` for every `ζ ∈ G`
— because multiplication by a member `ζ` *permutes* `G` (`ζ•G = G`). Consequently the period is
**constant on each multiplicative coset** `b·G`, so there are only `[F^* : G] = (q-1)/n` distinct
periods, indexed by the quotient `F^* / G`.

This is the metric-entropy collapse that I031 needs: group-invariant chaining on the **quotient**
(of `m = (q-1)/n` cosets) rather than the full multiplicative group collapses the entropy from
`log q` (the wall — why generic chaining failed) to `log(q/n)` (the floor's log factor),
recovering the target exponent `1/2` in `M ≲ C·√(n·log(q/n))`.

## What this file proves (axiom-clean, the formal foundation of I031)

For a **multiplicatively closed** `Finset G` (the Finset form of a finite multiplicative subgroup
/ the `n`-th roots of unity), and `ζ ∈ G`:

* `dilate_subset_of_mem`     : `ζ•G ⊆ G`                              (closure).
* `dilate_eq_self_of_mem`    : `ζ•G = G`                              (mult. by a member permutes).
* `eta_orbit_invariant`      : `η_{ζ·b}(G) = η_b(G)` for `ζ ∈ G`      (**ORBIT-INVARIANCE**).
* `eta_const_on_coset`       : `η` is constant on each coset `b·G`.
* `eta_image_subset_of_cosetCover` / `card_distinct_eta_le` :
    for any coset-covering `T`, the set of distinct periods injects into `T`, so
    `|{distinct η_b}| ≤ |T|` — the **quotient factoring (3)**: at most `[F^* : G]+1` periods.

Built on `SubgroupGaussSumDilationRecursion` (`dilate`, `eta_dilate`, `card_dilate`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

open Finset AddChar

namespace ArkLib.ProximityGap.SubgroupGaussSumOrbitReduction

open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A `Finset` is **multiplicatively closed** if the product of any two of its elements is again
in the set. The `2^μ`-subgroup `μ_n` of `F^*` (or any finite multiplicative subgroup) satisfies
this. We use the Finset-with-closure form so it plugs directly into the `dilate`/`eta` API. -/
def MulClosed (G : Finset F) : Prop := ∀ ⦃a⦄, a ∈ G → ∀ ⦃b⦄, b ∈ G → a * b ∈ G

/-- **`ζ•G ⊆ G`** when `G` is multiplicatively closed and `ζ ∈ G`. -/
theorem dilate_subset_of_mem {G : Finset F} (hG : MulClosed G) {ζ : F} (hζG : ζ ∈ G) :
    dilate ζ G ⊆ G := by
  intro y hy
  rw [dilate, Finset.mem_image] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact hG hζG hx

/-- **Dilation by a member fixes the set: `ζ•G = G`.** If `G` is multiplicatively closed and
`ζ ∈ G` (with `ζ ≠ 0`), multiplication by `ζ` permutes `G`. Subset from closure, equality from
`card_dilate` (the map is injective so cardinalities agree). -/
theorem dilate_eq_self_of_mem {G : Finset F} (hG : MulClosed G) {ζ : F} (hζ : ζ ≠ 0)
    (hζG : ζ ∈ G) : dilate ζ G = G :=
  Finset.eq_of_subset_of_card_le (dilate_subset_of_mem hG hζG) (by rw [card_dilate hζ])

/-- **ORBIT-INVARIANCE: `η_{ζ·b}(G) = η_b(G)` for `ζ ∈ G`.** Since multiplying the index by a
member `ζ` permutes `G`, the Gauss period is invariant under the dilation `b ↦ ζ·b`. This is the
foundation of I031: the period is constant on each coset `b·G`, so there are only `[F^* : G]`
distinct periods, indexed by the quotient `F^* / G`. -/
theorem eta_orbit_invariant {ψ : AddChar F ℂ} {G : Finset F} (hG : MulClosed G) {ζ : F}
    (hζ : ζ ≠ 0) (hζG : ζ ∈ G) (b : F) : eta ψ G (ζ * b) = eta ψ G b := by
  rw [← eta_dilate ψ G hζ b, dilate_eq_self_of_mem hG hζ hζG]

/-- **COSET-CONSTANCY (clean restatement of (3)).** The Gauss period `b ↦ η_b(G)` is constant on
each multiplicative coset `b·G`: for every `g ∈ G` (assumed `g ≠ 0`, automatic for `G ⊆ F^*`),
`η_{g·b}(G) = η_b(G)`. Hence `η` factors through the quotient `F / (mult-by-G)`. -/
theorem eta_const_on_coset {ψ : AddChar F ℂ} {G : Finset F} (hG : MulClosed G) {g : F}
    (hg : g ≠ 0) (hgG : g ∈ G) (b : F) : eta ψ G (g * b) = eta ψ G b :=
  eta_orbit_invariant hG hg hgG b

/-- **THE QUOTIENT FACTORING / period-count bound (3).** Let `T : Finset F` be **coset-covering**:
every frequency `b` has a member `g ∈ G` (`g ≠ 0`) with `g·b ∈ T` (i.e. `T` meets every coset
`b·G`). Then every Gauss-period value `η_b(G)` already occurs as some `η_t(G)` with `t ∈ T`:

> `Finset.univ.image (η · G) ⊆ T.image (η · G)`.

So the number of **distinct periods** is at most `|T|`. Taking `T` a transversal of the cosets
`F^* / G` (plus `0`) gives `|{distinct η_b}| ≤ [F^* : G] + 1 = (q-1)/n + 1`: the metric-entropy
collapse from `log q` to `log(q/n)` that I031 needs. (Stated for any covering `T`; the consumer
picks the transversal.) -/
theorem eta_image_subset_of_cosetCover {ψ : AddChar F ℂ} {G : Finset F} (hG : MulClosed G)
    {T : Finset F} (hT : ∀ b : F, ∃ g ∈ G, g ≠ 0 ∧ g * b ∈ T) :
    (Finset.univ.image (eta ψ G)) ⊆ (T.image (eta ψ G)) := by
  intro v hv
  rw [Finset.mem_image] at hv
  obtain ⟨b, _, rfl⟩ := hv
  obtain ⟨g, hgG, hg, hgbT⟩ := hT b
  rw [Finset.mem_image]
  exact ⟨g * b, hgbT, eta_const_on_coset hG hg hgG b⟩

/-- **Period-count corollary**: the number of distinct Gauss periods is at most the size of any
coset-covering set `T`. The clean cardinal form of (3): `|{distinct η_b : b ∈ F}| ≤ |T|`. -/
theorem card_distinct_eta_le {ψ : AddChar F ℂ} {G : Finset F} (hG : MulClosed G)
    {T : Finset F} (hT : ∀ b : F, ∃ g ∈ G, g ≠ 0 ∧ g * b ∈ T) :
    (Finset.univ.image (eta ψ G)).card ≤ T.card :=
  le_trans (Finset.card_le_card (eta_image_subset_of_cosetCover hG hT))
    (Finset.card_image_le)

end ArkLib.ProximityGap.SubgroupGaussSumOrbitReduction
