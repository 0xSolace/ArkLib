/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckBridge
import ArkLib.ProofSystem.Logup.Sumcheck.SumcheckPolynomial

/-!
# Batching-binding, step 1: a vanishing batched claim binds the helpers (issue #13)

Obligation 2 (first half) of the `hOuter@midLanguage` closing blueprint: if the batched LogUp
hypercube sum vanishes for **all** `(z, batchingScalars)` values, then the batching genuinely
binds the prover's helper oracles —

* `qsum_affine_in_batch` — the raw decomposition `∑_u q = A + ∑_k b_k · C_k(z)` (helper mass plus
  batch-weighted Lagrange-mixed domain-identity coefficients);
* `qsum_vanishing_forall` — evaluation at `b = 0` extracts `A = 0`; at `b = eₖ`,
  `z = signPoint u₀` the Lagrange delta (`lagrangeKernel_signPoint`) extracts
  `domainIdentityTerm k u₀ = 0` for every group `k` and row `u₀`.

The remaining half of the obligation is the partial-fraction clearing chain: `DIT ≡ 0` and
helper mass `0` force the grand-sum identity at `x` (inputs:
`helperValue_mul_denominatorProduct`, the `SoundnessConverse` count algebra), placing `x` in the
sharp Schwartz–Zippel locus — the round-2 monotonicity of the claim-based RBR state function.
Axiom-clean.
-/

open scoped BigOperators

namespace Logup

variable {F : Type} [Field F]
variable {n M K : ℕ}

/-- Raw affine-in-batch decomposition of the batched hypercube sum. -/
theorem qsum_affine_in_batch (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (multiplicity : MultilinearOracle F n)
    (helpers : HelperMessages F n K) (x : F) (z : Fin n → F) (b : Fin K → F) :
    ∑ u : Hypercube n, qOnHypercube groups oStmt multiplicity helpers x z b u
      = (∑ k : Fin K, ∑ u : Hypercube n, evalOnHypercube (helpers k) u)
        + ∑ k : Fin K, b k * (∑ u : Hypercube n,
            lagrangeKernel F u z * domainIdentityTerm groups oStmt multiplicity helpers x k u) := by
  unfold qOnHypercube
  rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  ring

/-- **Batching-binding, step 1 (coefficient extraction).** If the batched hypercube sum vanishes
for ALL `(z, batch)` values, then the helper mass vanishes and EVERY domain-identity term
vanishes at every row: the batching genuinely binds the helpers to the partial-fraction
identities. Evaluation at `batch = 0` extracts the helper mass; at `batch = eₖ`,
`z = signPoint u₀` the Lagrange delta extracts each `DIT k u₀`. -/
theorem qsum_vanishing_forall (hSigns : (-1 : F) ≠ 1)
    (groups : PartialSumGroups M K)
    (oStmt : ∀ i, OStmtIn F n M i) (multiplicity : MultilinearOracle F n)
    (helpers : HelperMessages F n K) (x : F)
    (h : ∀ (z : Fin n → F) (b : Fin K → F),
      ∑ u : Hypercube n, qOnHypercube groups oStmt multiplicity helpers x z b u = 0) :
    (∑ k : Fin K, ∑ u : Hypercube n, evalOnHypercube (helpers k) u) = 0 ∧
      ∀ (k : Fin K) (u₀ : Hypercube n),
        domainIdentityTerm groups oStmt multiplicity helpers x k u₀ = 0 := by
  classical
  -- helper mass: evaluate at batch = 0
  have hA : (∑ k : Fin K, ∑ u : Hypercube n, evalOnHypercube (helpers k) u) = 0 := by
    have h0 := h (fun _ => 0) 0
    rw [qsum_affine_in_batch] at h0
    simpa using h0
  refine ⟨hA, fun k u₀ => ?_⟩
  -- DIT k u₀: evaluate at z = signPoint u₀, batch = single k 1
  have hk := h (signPoint F u₀) (Pi.single k 1)
  rw [qsum_affine_in_batch, hA, zero_add] at hk
  rw [Finset.sum_eq_single k] at hk
  · rw [Pi.single_eq_same, one_mul] at hk
    have hdelta : (∑ u : Hypercube n,
        lagrangeKernel F u (signPoint F u₀) *
          domainIdentityTerm groups oStmt multiplicity helpers x k u)
        = domainIdentityTerm groups oStmt multiplicity helpers x k u₀ := by
      rw [Finset.sum_congr rfl (fun u _ => by
        rw [lagrangeKernel_signPoint (F := F) (n := n) hSigns u₀ u])]
      simp [Finset.sum_ite_eq']
    rwa [hdelta] at hk
  · intro b _ hbk
    rw [Pi.single_eq_of_ne hbk, zero_mul]
  · intro habs
    exact absurd (Finset.mem_univ k) habs

end Logup

#print axioms Logup.qsum_affine_in_batch
#print axioms Logup.qsum_vanishing_forall
