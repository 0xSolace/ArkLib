/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.MCAThresholdLedger

/-!
# di Benedetto edge exponent: the 2-power near-Sidon improvement (#444 — constant-factor lane)

**Result (conditional, axiom-clean).** di Benedetto–Garaev–Garcia–González-Sánchez–Shparlinski–Trujillo
(arXiv:2003.06165, JNT 2020) prove the explicit thin-subgroup character-sum bound
`M(H) ≤ H^{1−31/2880}` at the Burgess edge `|H|=p^{1/4}` (β=4). Their proof (§5) is a fixed three-fold
amplification whose edge power-saving, as a function of the two binding **additive-energy exponents**
`t₂` (of `E₂(H)=#{h₁+h₂=h₃+h₄}`, Lemma 4.2) and `t₃` (of `E₃(H)=#{Σ³h=Σ³h'}`, Lemma 4.3), is exactly

  `diBenedettoSaving t₂ t₃ = (10 − 2·t₃ − t₂/2) / 72`

(symbolically verified to reproduce `31/2880` at the general-subgroup inputs `t₂=49/20`, `t₃=4`).

**The lever.** `t₃` is the dominant input (sensitivity `−2/72`, four times `t₂`'s `−1/144`). di Benedetto's
`E₃ ≤ H⁴` (`t₃=4`) is the *pessimistic general-subgroup* bound — sharp only when the sumset is small.
The prize subgroup `μ_n` (`n=2^μ`) is additively **near-Sidon**: engine-exact `E₂ = 3n²−3n` (`t₂=2`) and
`E₃ ≈ 15n³` (`t₃=3`, the Lam–Leung/Wick value) for `n=16,32,64` at `p=n⁴`. Feeding `(t₂,t₃)=(2,3)`:

  `diBenedettoSaving 2 3 = 1/24 ≈ 0.0417`,  i.e.  **`M(μ_n) ≤ H^{1−1/24}` — a 3.9× larger power saving**.

This file formalizes the *exponent bookkeeping*: the saving formula's values (`1/24`, `31/2880`), the
strict improvement, the monotonicity (smaller energy exponents ⇒ larger saving), and the conditional
character-sum bound `charSum_le_of_nearSidon` that combines di Benedetto's edge bound (a named hypothesis
representing the cited theorem, parameterised by the energy exponents) with the near-Sidon energy bounds.

**HONESTY.** This is a *constant-factor* improvement (exponent `≈0.958`, NOT the prize `1/2`); it does
not pin `δ*`. It is CONDITIONAL on the near-Sidon energy bounds `E₂≤Cn²` (`t₂≤2`), `E₃≤Cn³` (`t₃≤3`) at
the prize scale `p=n⁴` — which are PROVEN only for `p>2^{0.896n}` (`SidonModNegImproved`,
`SumsetLowerBoundMuN`) and OPEN at `p=n⁴` (the char-p wraparound transfer at fixed `r=2,3`; empirically
exact at `n≤64`). That low-order energy bound is the (more-tractable-than-BCHKS) open input. Issue #444.
-/

open Real

namespace ProximityGap.Frontier.DiBenedettoNearSidon

/-- **The di Benedetto edge power-saving** as a function of the two binding additive-energy exponents
`t₂` (energy `E₂`) and `t₃` (energy `E₃`): `saving = (10 − 2·t₃ − t₂/2)/72`. At the general-subgroup
inputs `(49/20, 4)` it is `31/2880`; at the near-Sidon inputs `(2,3)` it is `1/24`. -/
noncomputable def diBenedettoSaving (t₂ t₃ : ℝ) : ℝ := (10 - 2 * t₃ - t₂ / 2) / 72

/-- **Baseline (di Benedetto Thm 3.1).** General-subgroup energy exponents `t₂=49/20`, `t₃=4` give the
published edge saving `31/2880`. -/
theorem diBenedettoSaving_baseline : diBenedettoSaving (49 / 20) 4 = 31 / 2880 := by
  unfold diBenedettoSaving; norm_num

/-- **The 2-power near-Sidon value.** Energy exponents `t₂=2`, `t₃=3` (the Lam–Leung/Wick energies of the
dyadic subgroup) give edge saving `1/24`. -/
theorem diBenedettoSaving_nearSidon : diBenedettoSaving 2 3 = 1 / 24 := by
  unfold diBenedettoSaving; norm_num

/-- **The improvement is real and strict:** `1/24 > 31/2880` (a factor `≈ 3.87`). -/
theorem nearSidon_improves : diBenedettoSaving 2 3 > diBenedettoSaving (49 / 20) 4 := by
  rw [diBenedettoSaving_nearSidon, diBenedettoSaving_baseline]; norm_num

/-- **Monotonicity (the lever).** Smaller additive-energy exponents give a larger edge saving: if
`t₂' ≤ t₂` and `t₃' ≤ t₃` then `diBenedettoSaving t₂ t₃ ≤ diBenedettoSaving t₂' t₃'`. -/
theorem diBenedettoSaving_antitone {t₂ t₂' t₃ t₃' : ℝ} (h₂ : t₂' ≤ t₂) (h₃ : t₃' ≤ t₃) :
    diBenedettoSaving t₂ t₃ ≤ diBenedettoSaving t₂' t₃' := by
  unfold diBenedettoSaving; linarith

/-- **At least the near-Sidon saving, from near-Sidon energy bounds.** If the energy exponents satisfy
`t₂ ≤ 2` and `t₃ ≤ 3`, the di Benedetto edge saving is at least `1/24`. -/
theorem diBenedettoSaving_ge_nearSidon {t₂ t₃ : ℝ} (h₂ : t₂ ≤ 2) (h₃ : t₃ ≤ 3) :
    (1 : ℝ) / 24 ≤ diBenedettoSaving t₂ t₃ := by
  have := diBenedettoSaving_antitone (t₂' := t₂) (t₃' := t₃) (t₂ := 2) (t₃ := 3) h₂ h₃
  rwa [diBenedettoSaving_nearSidon] at this

/-- **The conditional character-sum improvement.** Given (i) di Benedetto's edge bound at the realised
energy exponents `(t₂,t₃)` — `hDB : M ≤ H^{1 − diBenedettoSaving t₂ t₃}` (the cited Thm 3.1, parameterised
by the energies; a named hypothesis, NOT re-derived here), (ii) the near-Sidon energy bounds `t₂ ≤ 2`,
`t₃ ≤ 3` for the dyadic subgroup, and (iii) `H ≥ 1`: the character-sum bound improves to
`M ≤ H^{1 − 1/24}`. The improvement is driven purely by the monotonicity of the saving in the energy
exponents. Conditional on the (open, low-order) near-Sidon energy bounds at `p=n⁴`. -/
theorem charSum_le_of_nearSidon {M H t₂ t₃ : ℝ} (hH : 1 ≤ H)
    (hDB : M ≤ H ^ (1 - diBenedettoSaving t₂ t₃)) (h₂ : t₂ ≤ 2) (h₃ : t₃ ≤ 3) :
    M ≤ H ^ (1 - (1 : ℝ) / 24) := by
  have hsav : (1 : ℝ) / 24 ≤ diBenedettoSaving t₂ t₃ := diBenedettoSaving_ge_nearSidon h₂ h₃
  have hexp : 1 - diBenedettoSaving t₂ t₃ ≤ 1 - (1 : ℝ) / 24 := by linarith
  exact le_trans hDB (Real.rpow_le_rpow_of_exponent_le hH hexp)

end ProximityGap.Frontier.DiBenedettoNearSidon

/-! ## Axiom audit -/
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.diBenedettoSaving_baseline
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.diBenedettoSaving_nearSidon
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.nearSidon_improves
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.diBenedettoSaving_antitone
#print axioms ProximityGap.Frontier.DiBenedettoNearSidon.charSum_le_of_nearSidon
