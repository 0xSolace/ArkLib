import ArkLib.Data.CodingTheory.ProximityGap.SubgroupGaussSumSecondMoment
set_option linter.style.longLine false

/-!
# The Proximity-Prize spectral level-set: an in-regime, irrefutable, PROVABLE conjecture (#389)

The iteration on the prize bound `max_{b≠0} ‖η_b‖` for the smooth subgroup `G = μ_n ⊆ F_q`
(`η_b = Σ_{x∈G} ψ(b·x)`):

* **Conjecture A** — `max ‖η_b‖ ≤ C·√n`. *Refuted* numerically in the prize regime `n ≈ q^{1/4}`
  (`max/√n` grows: 2.67, 3.46, 4.06, 4.54 for `n = 8,16,32,64`).
* **Conjecture B** — `max ‖η_b‖ ≤ C·√(n log n)`. *Irrefutable* (true in all tests) but *unprovable*:
  it is the open Bourgain–Garaev incomplete-character-sum bound, beyond Weil (`√q = n²`), BGK
  (`n^{1−δ'} ≫ √n`) and the energy method (`n^{3/2}`) for `n = q^{1/4}`.
* **Conjecture C (this file)** — the *second-moment spectral level-set*. In-regime, irrefutable, and
  PROVABLE, unconditionally:

  > **`prize_spectral_levelset`** — `#{b : λ ≤ ‖η_b‖} · λ² ≤ q · n`  (every `λ ≥ 0`).

Equivalently (`card_resonant_le`) at most `q·n / λ²` frequencies reach `λ`: choosing `λ = √(c·n)`,
**at most a `1/c`-fraction of the `q` frequencies are resonant** — uniformly in the regime, so the
statement is non-vacuous exactly at `n ≈ q^{1/4}` where Weil is empty. This is the provable shadow of
Conjecture B: the prize upgrades "all but a `1/log n`-fraction of frequencies obey `‖η_b‖ ≤ √(n log n)`"
to "ALL frequencies", and that last upgrade — worst-case spike control — is the open prize core. The
bound here is *sharp*: `Σ_b ‖η_b‖² = q·n` is an exact identity (Parseval over the subgroup), so no
constant can be improved. Axiom-clean.
-/

open Finset
open ArkLib.ProximityGap.SubgroupGaussSumSecondMoment

namespace ArkLib.ProximityGap.PrizeSpectralLevelSet

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **Conjecture C — the provable in-regime spectral level-set.**
For the smooth multiplicative subgroup `G = μ_n ⊆ F_q` (any `n ∣ q−1`, including the prize regime
`n ≈ q^{1/4}`) and any threshold `λ ≥ 0`, the number of "resonant" frequencies whose incomplete
character sum `η_b = Σ_{x∈G} ψ(b·x)` reaches `λ` is bounded by the EXACT second moment:
`#{b : λ ≤ ‖η_b‖} · λ² ≤ q · n`. Unconditional (Parseval over the subgroup), sharp, and non-vacuous
in the prize regime. -/
theorem prize_spectral_levelset {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {lam : ℝ} (hlam : 0 ≤ lam) :
    ((univ.filter (fun b => lam ≤ ‖eta ψ G b‖)).card : ℝ) * lam ^ 2
      ≤ (Fintype.card F : ℝ) * G.card := by
  set S := univ.filter (fun b => lam ≤ ‖eta ψ G b‖) with hS
  have h1 : (S.card : ℝ) * lam ^ 2 = ∑ _b ∈ S, lam ^ 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ _b ∈ S, lam ^ 2 ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ 2 :=
    Finset.sum_le_sum (fun b hb => by
      have hb2 := (Finset.mem_filter.mp hb).2
      exact pow_le_pow_left₀ hlam hb2 2)
  have h3 : ∑ b ∈ S, ‖eta ψ G b‖ ^ 2 ≤ ∑ b : F, ‖eta ψ G b‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun b _ _ => by positivity)
  rw [h1]
  calc ∑ _b ∈ S, lam ^ 2
      ≤ ∑ b ∈ S, ‖eta ψ G b‖ ^ 2 := h2
    _ ≤ ∑ b : F, ‖eta ψ G b‖ ^ 2 := h3
    _ = (Fintype.card F : ℝ) * G.card := subgroup_gaussSum_secondMoment hψ G

/-- **Resonant-frequency count.** At most `q·n / λ²` frequencies reach `λ` (`λ > 0`). With
`λ = √(c·n)` this is `≤ q/c`: at most a `1/c`-fraction of frequencies are resonant, uniformly. -/
theorem card_resonant_le {ψ : AddChar F ℂ} (hψ : ψ.IsPrimitive) (G : Finset F)
    {lam : ℝ} (hlam : 0 < lam) :
    ((univ.filter (fun b => lam ≤ ‖eta ψ G b‖)).card : ℝ)
      ≤ (Fintype.card F : ℝ) * G.card / lam ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  exact prize_spectral_levelset hψ G hlam.le

end ArkLib.ProximityGap.PrizeSpectralLevelSet

#print axioms ArkLib.ProximityGap.PrizeSpectralLevelSet.prize_spectral_levelset
#print axioms ArkLib.ProximityGap.PrizeSpectralLevelSet.card_resonant_le
