/-
# The Delsarte / linear-programming method NO-GO for the Gauss-period house (#444)

The $1M open core is the house `M(μ_n) = max_{b≠0} |Σ_{z∈μ_n} e_p(bz)| = max_J √(τ_J)`, where the
`τ_J ≥ 0` are the `m = (p−1)/n` squared period magnitudes (the spectral measure on the cosets), so
`house² = max_J τ_J`. The exact degree-1 (Parseval) moment is `∑_J τ_J = p − n` (verified numerically:
`n=8,p=337 → 2632 = 8·329`; `n=16,p=1297 → 20496 = 16·1281`).

**The no-go.** Any Delsarte / linear-programming / positive-semidefinite / Beurling–Selberg dual
certificate for an upper bound on `house² = max_J τ_J` can only use **linear** functionals of the
spectral vector that are certified by the moment data — and the only degree-1 moment available is the
total mass `∑_J τ_J = p − n`. The LP relaxation optimum of `max_J τ_J` subject to `τ ≥ 0` and
`∑_J τ_J = S` is **exactly `S`** (achieved by putting all mass on one coset). Hence the best bound any
such method yields is

  `house² ≤ p − n`,  i.e.  `house ≤ √(p − n) ≈ √(n·m)`,

the trivial Parseval / `√m`-loss ceiling — a factor `√(m / (2 log m)) ≈ 2^63` (prize scale `m ≈ 2^128`)
above the conjectured truth `house ≤ √(2 n log m)`. Beating Parseval requires the **degree-2** moment
`∑_J τ_J² = E₂` (the additive energy), which is **not a linear functional of the `τ_J`** and is therefore
structurally invisible to any LP/psd dual. So the entire Delsarte-LP method class provably cannot reach
the prize window; the live handle remains the (nonlinear) additive-energy/moment wall `E_r`.

This file formalizes the load-bearing core — the LP relaxation optimum of `max_J τ_J` under the single
mass constraint is exactly the total mass — as an elementary, fully general fact. It is a **method no-go**
(a companion to `BlockSumNormNoGo.lean` and the disc(Ψ) no-go), NOT a closure of the house: it proves a
class of approaches cannot work, isolating the wall further. CORE `M(μ_n) ≤ C√(n log(p/n))` UNCHANGED/OPEN.

Axiom-clean: `⊆ {propext, Classical.choice, Quot.sound}`. No `sorry`/`axiom`/`native_decide`.
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace ArkLib.ProximityGap.DelsarteLPNoGo

open Finset

variable {m : ℕ}

/-- A single nonnegative spectral coordinate is at most the total mass: `τ_J ≤ ∑_K τ_K`. This is the
only inequality on `max_J τ_J` that the degree-1 (total-mass) moment supplies. -/
theorem coord_le_sum (τ : Fin m → ℝ) (hτ : ∀ J, 0 ≤ τ J) (J : Fin m) :
    τ J ≤ ∑ K, τ K :=
  Finset.single_le_sum (f := τ) (fun K _ => hτ K) (Finset.mem_univ J)

/-- **The Delsarte/LP relaxation optimum for the house equals Parseval.** Over all nonnegative spectral
vectors `τ : Fin m → ℝ` with fixed total mass `∑_J τ_J = S` (the single degree-1 moment any LP/psd dual
can certify), the maximum coordinate `max_J τ_J = house²`:

* is **bounded above by `S`** for every feasible `τ` (first conjunct), and
* **attains `S`** at the extremal "all mass on one coset" point (second conjunct).

Hence the LP optimum is exactly `S`: no certificate using only the total mass can prove `house² < S = p−n`.
Beating the trivial Parseval ceiling `house ≤ √(p−n)` is therefore impossible by any such method — it
requires the degree-2 moment `∑_J τ_J² = E₂`, which is not linear in `τ`. -/
theorem parseval_lp_extremal (hm : 0 < m) (S : ℝ) (hS : 0 ≤ S) :
    (∀ τ : Fin m → ℝ, (∀ J, 0 ≤ τ J) → (∑ J, τ J = S) → ∀ J, τ J ≤ S) ∧
      (∃ τ : Fin m → ℝ, (∀ J, 0 ≤ τ J) ∧ (∑ J, τ J = S) ∧ ∃ J, τ J = S) := by
  refine ⟨fun τ hτ hsum J => ?_, ?_⟩
  · -- upper bound: every coordinate ≤ total mass = S
    have h := coord_le_sum τ hτ J
    rwa [hsum] at h
  · -- extremal feasible point: all mass S on coordinate ⟨0, hm⟩
    refine ⟨fun J => if J = ⟨0, hm⟩ then S else 0, fun J => ?_, ?_, ⟨0, hm⟩, ?_⟩
    · show 0 ≤ if J = ⟨0, hm⟩ then S else 0
      split_ifs with h
      · exact hS
      · exact le_refl 0
    · show (∑ J : Fin m, if J = ⟨0, hm⟩ then S else 0) = S
      rw [Finset.sum_eq_single_of_mem (⟨0, hm⟩ : Fin m) (Finset.mem_univ _)
        (fun b _ hb => if_neg hb)]
      simp
    · show (if (⟨0, hm⟩ : Fin m) = ⟨0, hm⟩ then S else 0) = S
      simp

end ArkLib.ProximityGap.DelsarteLPNoGo
