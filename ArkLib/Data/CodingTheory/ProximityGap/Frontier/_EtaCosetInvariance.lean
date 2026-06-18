/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._EtaFrequencyParity

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# Multiplicative coset-invariance of the Gauss period `η_{cb} = η_b` for `c ∈ G` (#444)

The FUNDAMENTAL structural symmetry of the generalized-Paley eigenvalue `η_b = Σ_{x∈G} ψ(b·x)` on a
multiplicatively-closed connection set `G = μ_n`: it is INVARIANT under dilating the frequency by any
`c ∈ G`.

> **`eta_dilate_eq`** : if `c ≠ 0` and `c·G = G` (i.e. `∀ x ∈ G, c·x ∈ G`, the subgroup closure) then
> `η_{c·b} = η_b`.

Proof (one reindex, no orthogonality, no Weil): `η_{cb} = Σ_{x∈G} ψ((cb)·x) = Σ_{x∈G} ψ(b·(c·x))`;
since `x ↦ c·x` is a bijection `G → G` (closure + `c ≠ 0`), reindexing `y = c·x` gives
`Σ_{y∈G} ψ(b·y) = η_b`.

## Why this is the structural keystone (it subsumes the b↔−b parity)

This is STRONGER than the antipodal `η_{−b} = η_b` of `_EtaFrequencyParity` (which is the special case
`c = −1`, valid only when `−1 ∈ G`): the WHOLE subgroup `μ_n` acts on the frequency line by dilation,
fixing `η`. So `η_b` is constant on each multiplicative coset `b·μ_n ∈ F_q*/μ_n`, and the `q−1`
non-principal frequencies collapse to at most **`(q−1)/n` distinct eigenvalues**, each of multiplicity a
multiple of `n` (probes show exactly `(q−1)/n` distinct values: e.g. `p=257, n=8 ⟹ 32 = 256/8` distinct;
`n=16 ⟹ 16`). The prize sup `M = max_{b≠0}‖η_b‖` is therefore a max over `(q−1)/n` coset-representatives,
not over all `q−1` frequencies — the exact reason the problem is governed by `n` (the THIN subgroup),
not `q`.

> **`norm_eta_dilate_eq`** : `‖η_{c·b}‖ = ‖η_b‖` for `c ∈ G`, `c ≠ 0` — the modulus form: `M` is attained
> on a full multiplicative `μ_n`-orbit of frequencies, never an isolated `b`.

## Honesty (project §6)

POSITIVE structural keystone, NOT a closure and NOT a refutation. Exact and axiom-clean (a single finite
reindex via subgroup closure; no orthogonality, no Weil). It bounds NOTHING from above: the prize
`M ≤ C√(n·log p)` (char-`p` energy/BGK wall) stays OPEN. Coset-invariance reduces the number of DISTINCT
non-principal eigenvalues to `(q−1)/n` and localises the problem to the thin subgroup `μ_n`, but bounds
no single eigenvalue. This is the keystone underneath the b↔−b parity (`_EtaFrequencyParity`, `c=−1`
case) and the antipodal/dilation files. Issue #444.

## References
- `Frontier/_EtaFrequencyParity.eta_neg_eq_of_symm` (the `c = −1` antipodal special case).
- `Frontier/DilationRealSignCocycle` / `_TowerSpikeBetaGate` (the `eta_union_dilate` recursion this
  invariance underlies).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ProximityGap.Frontier.EtaCosetInvariance

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **★ Multiplicative coset-invariance: `η_{c·b} = η_b` for `c ∈ G` (`c·G = G`, `c ≠ 0`).**

`η_{cb} = Σ_{x∈G} ψ((c·b)·x) = Σ_{x∈G} ψ(b·(c·x))`; reindex by the bijection `x ↦ c·x` of `G` (subgroup
closure `hcG : ∀ x ∈ G, c·x ∈ G` and injectivity from `c ≠ 0`) to get `Σ_{y∈G} ψ(b·y) = η_b`. Pure
finite reindex, no orthogonality, no Weil. The keystone symmetry: `η` is constant on multiplicative
`μ_n`-cosets of the frequency line. -/
theorem eta_dilate_eq {ψ : AddChar F ℂ} (G : Finset F) {c : F} (hc : c ≠ 0)
    (hcG : ∀ x ∈ G, c * x ∈ G) (b : F) :
    eta ψ G (c * b) = eta ψ G b := by
  classical
  unfold eta
  -- the map x ↦ c * x is injective and maps G into G, and G is finite, so G.image (c*·) = G
  have hinj : Set.InjOn (fun z => c * z) G := by
    intro a _ b _ hab; exact mul_left_cancel₀ hc hab
  have hsub : G.image (fun z => c * z) ⊆ G := by
    intro w hw; rw [Finset.mem_image] at hw
    obtain ⟨z, hz, rfl⟩ := hw; exact hcG z hz
  have heq : G.image (fun z => c * z) = G :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj])
  have himg : ∑ y ∈ G.image (fun z => c * z), ψ (b * y)
      = ∑ x ∈ G, ψ (b * (c * x)) :=
    Finset.sum_image (fun a _ d _ had => mul_left_cancel₀ hc had)
  -- η_b = Σ_{y∈G} ψ(b·y) = Σ_{y∈G.image(c·)} ψ(b·y) = Σ_{x∈G} ψ(b·(c·x)) = Σ_{x∈G} ψ((c·b)·x)
  calc ∑ x ∈ G, ψ ((c * b) * x)
      = ∑ x ∈ G, ψ (b * (c * x)) := by
        refine Finset.sum_congr rfl (fun x _ => ?_); congr 1; ring
    _ = ∑ y ∈ G.image (fun z => c * z), ψ (b * y) := himg.symm
    _ = ∑ y ∈ G, ψ (b * y) := by rw [heq]

/-- **`‖η_{c·b}‖ = ‖η_b‖` for `c ∈ G`** — the modulus form of coset-invariance: the prize sup `M` is
attained on a full multiplicative `μ_n`-orbit of frequencies. -/
theorem norm_eta_dilate_eq {ψ : AddChar F ℂ} (G : Finset F) {c : F} (hc : c ≠ 0)
    (hcG : ∀ x ∈ G, c * x ∈ G) (b : F) :
    ‖eta ψ G (c * b)‖ = ‖eta ψ G b‖ := by
  rw [eta_dilate_eq G hc hcG b]

end ProximityGap.Frontier.EtaCosetInvariance

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only). -/
#print axioms ProximityGap.Frontier.EtaCosetInvariance.eta_dilate_eq
#print axioms ProximityGap.Frontier.EtaCosetInvariance.norm_eta_dilate_eq
