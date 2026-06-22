/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._ResonancePhaseSumConvolutionRecursion

/-!
# Fourier-side recursion for the resonance phase-sum (#444)

This is the spectral form of `phaseSum_succ`.  For any multiplicative additive character
`ψ : ZMod m → ℂ`, the Fourier coefficient of the depth-`r` phase-sum satisfies

`phaseSpectrum ψ u (r+1) = kernelSpectrum ψ u * phaseSpectrum ψ u r`.

Iterating this identity reduces all higher spectral rungs to the one-step kernel spectrum.

Honest scope: this is an exact algebraic identity only. It does not bound the one-step spectrum;
that spectrum is the open door-(iv) Gauss-period/BGK object.
-/

namespace ArkLib.ProximityGap.GaussPhaseResonance

open scoped BigOperators
open Finset

variable {m : ℕ} [NeZero m]

/-- The `ψ`-Fourier coefficient of the depth-`r` phase-sum. -/
noncomputable def phaseSpectrum (ψ : ZMod m → ℂ) (u : ZMod m → ℂ) (r : ℕ) : ℂ :=
  ∑ c : ZMod m, phaseSum u r c * ψ c

/-- The one-step nonzero kernel spectrum attached to `u`. -/
noncomputable def kernelSpectrum (ψ : ZMod m → ℂ) (u : ZMod m → ℂ) : ℂ :=
  ∑ a ∈ Finset.univ.filter (fun a : ZMod m => a ≠ 0), u a * ψ a

/-- **Spectral one-step recursion.**  If `ψ` is multiplicative for addition, then the
Fourier coefficient of `P_{r+1}` is the one-step spectrum times the Fourier coefficient of
`P_r`. This is the Fourier-side form of the exact convolution recursion. -/
theorem phaseSpectrum_succ (ψ : ZMod m → ℂ) (u : ZMod m → ℂ) (r : ℕ)
    (hmul : ∀ x y : ZMod m, ψ (x + y) = ψ x * ψ y) :
    phaseSpectrum ψ u (r + 1) = kernelSpectrum ψ u * phaseSpectrum ψ u r := by
  classical
  unfold phaseSpectrum kernelSpectrum
  simp_rw [phaseSum_succ]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro a ha
  calc
    (∑ c : ZMod m, u a * phaseSum u r (c - a) * ψ c)
        = u a * (∑ c : ZMod m, phaseSum u r (c - a) * ψ c) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl ?_
          intro c _
          ring
    _ = u a * (∑ d : ZMod m, phaseSum u r d * ψ (d + a)) := by
          congr 1
          exact Fintype.sum_equiv (Equiv.subRight a) _ _ (by
            intro d
            simp [sub_eq_add_neg, add_assoc])
    _ = u a * (∑ d : ZMod m, phaseSum u r d * (ψ d * ψ a)) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro d _
          rw [hmul]
    _ = u a * ((∑ d : ZMod m, phaseSum u r d * ψ d) * ψ a) := by
          congr 1
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro d _
          ring
    _ = u a * ψ a * ∑ d : ZMod m, phaseSum u r d * ψ d := by
          ring

end ArkLib.ProximityGap.GaussPhaseResonance

#print axioms ArkLib.ProximityGap.GaussPhaseResonance.phaseSpectrum_succ
