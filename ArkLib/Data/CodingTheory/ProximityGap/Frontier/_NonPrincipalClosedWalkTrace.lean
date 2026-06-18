/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ClosedWalkPowerSum

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
# The non-principal closed-walk trace `Σ_{b≠0} η_b^k = q·W_k − n^k` (#444)

The DC-subtracted, un-conjugated companion to `Frontier/_ClosedWalkPowerSum`. With `η_b = Σ_{y∈G} ψ(b·y)`
the eigenvalues of `Cay(F_q, G)`, the principal (Perron/degree) eigenvalue is `η_0 = |G| = n`
(`eta_zero`). Subtracting it from the full closed-walk power-sum `Σ_b η_b^k = q·W_k`
(`spectral_pow_sum_eq`, `W_k = #{closed k-walks at 0}`):

> **`nonprincipal_pow_sum_eq`** : `Σ_{b≠0} η_b^k = q·W_k − n^k`.

This is `tr(A^k) − η_0^k` summed over the `m = q−1` non-principal eigenvalues — the **signed**, odd-aware
analogue of the even/conjugated `DCSubtractedMoment.sum_nonzero_moment` (`Σ_{b≠0}‖η_b‖^{2r} = tr(A^{2r})−n^{2r}`).

## Why this is genuinely new content (signed, not phase-blind)

The even DC-subtracted moments `Σ_{b≠0}‖η_b‖^{2r}` are sums of NONNEGATIVE magnitudes (phase-blind,
`specMoment_phase_blind`). The **odd-`k`** non-principal trace `Σ_{b≠0} η_b^k` is genuinely SIGNED: probes
over thin `μ_n` (`n = 2^a`) show it is NEGATIVE for several `(p,n,k)` (e.g. `k=3`, `n=8`: the value is
`-n^3` exactly, because the closed-3-walk count `W_3 = 0` when `μ_8` has no additive triples). So this is a
spectral invariant the entire even DC-subtracted ladder structurally cannot reach.

## The clean `W_k = 0` corollary (purely additive-combinatorial regime)

> **`nonprincipal_pow_sum_eq_neg_pow_of_noWalks`** : if `W_k = 0` (no closed `k`-walks: `G` has no
> `k`-tuple summing to `0`) then `Σ_{b≠0} η_b^k = −n^k`.

For odd `k` this forces a genuinely negative non-principal trace — an exact sign-forcing companion to
`exists_nonzero_eta_re_neg`, driven here by the COMBINATORIAL absence of additive `k`-relations in the
thin subgroup, not just the bare degree.

## Honesty (project §6)

POSITIVE structural brick, NOT a closure and NOT a refutation. Exact, axiom-clean (subtraction +
`spectral_pow_sum_eq`, orthogonality only). It bounds NOTHING from above: the prize
`M = max_{b≠0}‖η_b‖ ≤ C√(n·log p)` (char-`p` energy/BGK wall) stays OPEN. The non-principal trace
`q·W_k − n^k` is built from the unsigned closed-walk count `W_k` (the additive-energy face) and the
degree `n`; routing it to the signed sup-norm is exactly the unsigned→signed transfer that the in-tree
meta-theorem records as the wall. The odd-aware DC-subtracted companion of `DCSubtractedMoment` and
`_ClosedWalkPowerSum`. Issue #444 / #389.

## References
- `Frontier/_ClosedWalkPowerSum` (`Σ_b η_b^k = q·W_k`, the un-subtracted full trace).
- `Frontier/_SpectralTraceZeroSignForcing.eta_zero` (`η_0 = |G|`, the degree eigenvalue).
- `DCSubtractedMoment.sum_nonzero_moment` (even/conjugated `Σ_{b≠0}‖η_b‖^{2r} = tr(A^{2r}) − n^{2r}`).
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026. #444.
-/

open Finset AddChar
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment
open ProximityGap.Frontier.ClosedWalkPowerSum

namespace ProximityGap.Frontier.NonPrincipalClosedWalkTrace

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The DC (`b=0`) eigenvalue is the degree `η_0 = |G|`** (the Perron/principal eigenvalue). -/
theorem eta_zero (ψ : AddChar F ℂ) (G : Finset F) : eta ψ G 0 = (G.card : ℂ) := by
  unfold eta; simp

/-- **★ The non-principal closed-walk trace: `Σ_{b≠0} η_b^k = q·W_k − n^k`.**

Splitting the full closed-walk power-sum `Σ_b η_b^k = q·W_k` (`spectral_pow_sum_eq`) at the DC term
`η_0^k = n^k` (`eta_zero`): the `m = q−1` non-principal eigenvalues carry the remainder. This is
`tr(A^k) − η_0^k`, the signed, odd-aware DC-subtracted trace — the un-conjugated analogue of the even
`DCSubtractedMoment.sum_nonzero_moment`. -/
theorem nonprincipal_pow_sum_eq {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F) (k : ℕ) :
    ∑ b ∈ univ.erase (0 : F), eta ψ G b ^ k
      = (Fintype.card F : ℂ) * (closedWalks G k).card - (G.card : ℂ) ^ k := by
  classical
  have hsplit : ∑ b : F, eta ψ G b ^ k
      = eta ψ G 0 ^ k + ∑ b ∈ univ.erase (0 : F), eta ψ G b ^ k :=
    (Finset.add_sum_erase univ _ (Finset.mem_univ 0)).symm
  rw [spectral_pow_sum_eq hψ G k, eta_zero] at hsplit
  -- q·W_k = n^k + Σ_{b≠0} η_b^k  ⟹  Σ_{b≠0} η_b^k = q·W_k − n^k
  linear_combination -hsplit

/-- **No closed `k`-walks ⟹ `Σ_{b≠0} η_b^k = −n^k`.** When `G = μ_n` has no `k`-tuple summing to `0`
(`closedWalks G k = ∅`, e.g. `k` smaller than the additive girth of the thin subgroup), the entire
non-principal trace collapses to `−n^k`. For odd `k` this is a genuinely NEGATIVE non-principal trace,
forced by the COMBINATORIAL absence of additive `k`-relations — the exact sign-forcing companion to
`exists_nonzero_eta_re_neg`. -/
theorem nonprincipal_pow_sum_eq_neg_pow_of_noWalks {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive)
    (G : Finset F) (k : ℕ) (hW : closedWalks G k = ∅) :
    ∑ b ∈ univ.erase (0 : F), eta ψ G b ^ k = -((G.card : ℂ) ^ k) := by
  rw [nonprincipal_pow_sum_eq hψ G k, hW]
  simp

end ProximityGap.Frontier.NonPrincipalClosedWalkTrace

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only). -/
#print axioms ProximityGap.Frontier.NonPrincipalClosedWalkTrace.nonprincipal_pow_sum_eq
#print axioms ProximityGap.Frontier.NonPrincipalClosedWalkTrace.nonprincipal_pow_sum_eq_neg_pow_of_noWalks
