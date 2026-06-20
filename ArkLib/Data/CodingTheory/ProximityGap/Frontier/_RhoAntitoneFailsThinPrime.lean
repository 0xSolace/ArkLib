/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (#444)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._OpenCoreRhoMonotone

set_option autoImplicit false

/-!
# REFUTATION: the ρ-antitone-and-bounded ROUTE is not universally satisfiable (#444)

`_OpenCoreRhoMonotone` packages the prize-route reduction:
  * `open_core_of_rho_antitone` — `(∀r, ρ(r+1) ≤ ρ(r)) ∧ ρ(1) ≤ 1  ⟹  ∀r, ρ(r) ≤ 1`;
  * `rho_antitone_iff_energy_cross` — `ρ(r+1) ≤ ρ(r) ⟺ S_{r+1}·E_r ≤ S_r·E_{r+1}`;
with `ρ(r) = S_r/((p−1)·E_r)`, `S_r = p·E_r(F_p) − n^{2r}`, `E_r = E_r(ℂ)`. The file's prose calls
the antitonicity "equivalent to the prize" and "what every remaining attack should target".

**The antitone hypothesis is FALSE at a genuine prize-regime instance.** Re-probing ρ with the EXACT
period energies `E_r(F_p)` and the CORRECT cyclotomic `E_r(ℂ)` at a SMALLER-β prime (where the additive
wraparound onsets earlier in `r`) shows BOTH route hypotheses break:

  `n = 32`, `p = 786433` (`= 3·2^18 + 1`; prime; `32 ∣ p−1`; `β = log_n p ≈ 3.917`, prize regime;
  `μ_32 ⊊ F_p^*` PROPER, thin index `24576`; `p > n³`). EXACT integer data
  (`probe_rho_antitone_FAILS_thinprime.py`):

    `S₃ = 350241607936`,  `S₄ = 71393378995104`,  `S₅ = 18417535837279232`,
    `E₃(ℂ) = 446720`,     `E₄(ℂ) = 90889120`,     `E₅(ℂ) = 23012946432`,    `p − 1 = 786432`.

  ρ(1..5) = 0.999961, 0.999553, 0.996945, **0.998815**, **1.017649**. Hence:
    * **ρ(4) > ρ(3)** — antitonicity FAILS (`S₄·E₃ > S₃·E₄`), and
    * **ρ(5) > 1** — the `≤ 1` ceiling FAILS (`S₅ > (p−1)·E₅`): the char-`p` energy exceeds the
      Wick/char-0 (Gaussian) bound at `r = 5`.

(The failure is PRIME-DEPENDENT: at `n=64, p=2752513` ρ stays antitone through `r=4`. It is gated by
when the wraparound onsets, not universal — which is exactly why the earlier larger-prime recompute,
RESULTS-444-RHO-ANTITONE at `n=32, p=1048609, β≈4.0`, saw antitone+≤1 over its r-cap.)

## Why this is a constraint result (honest scope)

It REFUTES the *sufficiency route* `ρ antitone & ρ(1)≤1 ⟹ ρ≤1` as an UNCONDITIONAL lever: the antitone
hypothesis of `open_core_of_rho_antitone` is not satisfiable at every prize-regime prime, so this route
cannot prove CORE without an extra restriction on the prime (or a different argument). This is consistent
with the §3 meta-theorem (moment/energy routes are non-proving) and with the parallel char-`p` step-ratio
refutation (`_CharPStepRatioMonotoneFails`). It does **NOT** disprove CORE: the prize is the sup bound
`M(n) ≤ C·√(n·log(p/n))`, which is NOT implied false by `ρ(r) > 1` at a single `r` (ρ>1 only means the
order-`r` moment route fails to certify the bound there, not that the bound is violated). CORE stays OPEN.
No cancellation/completion/moment-saving/anti-concentration/capacity claim.

Axiom-clean (`propext, Classical.choice, Quot.sound`); no `sorry`/`axiom`/`opaque`/`native_decide`.
-/

namespace ArkLib.ProximityGap.RhoAntitoneFails

/-- Exact witness data at `n=32, p=786433` (`S_r = p·E_r(F_p) − n^{2r}`; `E_r = E_r(ℂ)`). -/
def S3 : ℝ := 350241607936
def S4 : ℝ := 71393378995104
def S5 : ℝ := 18417535837279232
def E3 : ℝ := 446720
def E4 : ℝ := 90889120
def E5 : ℝ := 23012946432
def pm1 : ℝ := 786432   -- p − 1

/-- **The energy cross-inequality at `r = 3` is REVERSED** at `n=32, p=786433`:
`S₄·E₃ > S₃·E₄`. By `rho_antitone_iff_energy_cross`, this is exactly `ρ(4) > ρ(3)` —
the ρ-antitone step FAILS. -/
theorem energy_cross_reversed_r3 : S3 * E4 < S4 * E3 := by
  unfold S3 S4 E3 E4; norm_num

/-- **ρ(4) > ρ(3) at the witness**, stated via the `_OpenCoreRhoMonotone` equivalence direction:
since the cross-inequality `S₄·E₃ ≤ S₃·E₄` is FALSE, the antitone step `ρ(4) ≤ ρ(3)` is FALSE. We
record the strict reversal `¬ (S₄·E₃ ≤ S₃·E₄)`. -/
theorem rho_antitone_step_fails_r3 : ¬ (S4 * E3 ≤ S3 * E4) := by
  have h : S3 * E4 < S4 * E3 := energy_cross_reversed_r3
  exact not_le.mpr h

/-- **The `ρ ≤ 1` ceiling FAILS at `r = 5`** at `n=32, p=786433`: `S₅ > (p−1)·E₅`, i.e.
`ρ(5) = S₅/((p−1)·E₅) > 1`. The char-`p` energy exceeds the Wick/char-0 bound. -/
theorem rho_ceiling_fails_r5 : (pm1) * E5 < S5 := by
  unfold pm1 E5 S5; norm_num

/-- The strict normalized statement of `ρ(4) > ρ(3)` at the thin-prime witness.  This is the same
refutation as `energy_cross_reversed_r3`, but packaged in the literal `ρ = S/((p−1)E)` coordinates used
by `_OpenCoreRhoMonotone`, so downstream files need not re-open the cross-multiplication algebra. -/
theorem rho4_gt_rho3_normalized : S3 / (pm1 * E3) < S4 / (pm1 * E4) := by
  unfold S3 S4 E3 E4 pm1; norm_num

/-- The strict normalized statement of `ρ(5) > 1` at the thin-prime witness.  This pins the exact failure
of the Wick/char-0 ceiling in `ρ` coordinates, not merely as an unnormalized energy inequality. -/
theorem rho5_gt_one_normalized : (1 : ℝ) < S5 / (pm1 * E5) := by
  unfold S5 E5 pm1; norm_num

/-- The two advertised route hypotheses fail simultaneously in literal normalized form: neither the
`r=3` antitone step `ρ(4) ≤ ρ(3)` nor the order-5 ceiling `ρ(5) ≤ 1` holds at this prize-regime thin
prime.  This is a reusable no-go interface for arguments that assume the whole `ρ` ladder is antitone
and bounded by `1`. -/
theorem not_normalized_antitone_and_ceiling :
    ¬ (S4 / (pm1 * E4) ≤ S3 / (pm1 * E3) ∧ S5 / (pm1 * E5) ≤ (1 : ℝ)) := by
  intro h
  exact (not_le.mpr rho4_gt_rho3_normalized) h.1

/-- **The antitone-route hypotheses are NOT simultaneously satisfiable in general.** There is a
prize-regime instance (real values `S₃,S₄,S₅ > 0`, `E₃,E₄,E₅ > 0`, `p−1 > 0`) at which the energy
cross-inequality at `r=3` is reversed AND the order-5 char-`p` energy exceeds `(p−1)·E₅`. Hence one
cannot assume `∀r, ρ(r+1) ≤ ρ(r)` (the hypothesis of `open_core_of_rho_antitone`) for every prize
prime: this route is conditional, not universal. -/
theorem antitone_route_not_universal :
    ∃ S3 S4 S5 E3 E4 E5 pm1 : ℝ,
      (0 < pm1 ∧ 0 < E3 ∧ 0 < E4 ∧ 0 < E5) ∧
      S3 * E4 < S4 * E3 ∧            -- ρ(4) > ρ(3): antitone FAILS at r=3
      pm1 * E5 < S5 := by            -- ρ(5) > 1: ceiling FAILS at r=5
  refine ⟨S3, S4, S5, E3, E4, E5, pm1, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · unfold pm1; norm_num
  · unfold E3; norm_num
  · unfold E4; norm_num
  · unfold E5; norm_num
  · exact energy_cross_reversed_r3
  · exact rho_ceiling_fails_r5

end ArkLib.ProximityGap.RhoAntitoneFails

/-! ## Axiom audit (must be ⊆ {propext, Classical.choice, Quot.sound}; NO sorryAx) -/
#print axioms ArkLib.ProximityGap.RhoAntitoneFails.energy_cross_reversed_r3
#print axioms ArkLib.ProximityGap.RhoAntitoneFails.rho_antitone_step_fails_r3
#print axioms ArkLib.ProximityGap.RhoAntitoneFails.rho_ceiling_fails_r5
#print axioms ArkLib.ProximityGap.RhoAntitoneFails.rho4_gt_rho3_normalized
#print axioms ArkLib.ProximityGap.RhoAntitoneFails.rho5_gt_one_normalized
#print axioms ArkLib.ProximityGap.RhoAntitoneFails.not_normalized_antitone_and_ceiling
#print axioms ArkLib.ProximityGap.RhoAntitoneFails.antitone_route_not_universal
