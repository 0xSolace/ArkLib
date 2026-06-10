/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Stir.CheckingVerifier

/-!
# The tightness-fence counting core (#301, K4 part 1)

The quantitative heart of the switch-prover attack on the STIR checking verifier: the
challenge-counting facts behind the acceptance probability `≥ 1 − D/|F|`.  Protocol-free —
the night assembly welds these into the rbr-budget lower bound.

* `pass_count_ge` — for words `f g : ι → F` agreeing at every off-image query point, the
  set of challenges passing the binding check `f (queryPoint φ r) = g (queryPoint φ r)`
  has size `≥ |F| − |disagreement(f, g)|`: only the `φ`-image of the disagreement set can
  fail.
* `fail_subset_image` — the failing challenges embed into the disagreement set.

Why the off-image hypothesis is genuinely available to the ATTACKER: `queryPoint φ r` for
`r ∉ Set.range φ` is `Function.invFun`'s default, a single fixed junk point; the switch
prover picks its echoed codeword to agree with `f` there (or the fence's far-word
construction picks the disagreement support avoiding it), so all `|F| − |ι|` off-image
challenges pass.

Axiom-clean: `[propext, Classical.choice, Quot.sound]` (audited at end of file).
-/

set_option linter.unusedSectionVars false

namespace StirIOP

namespace MultiRound

namespace TightnessCore

open Finset

attribute [local instance] Classical.propDecidable

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- **The failing challenges embed into the disagreement set**: under off-image agreement,
a failing challenge must be the `φ`-image of a disagreement point. -/
lemma fail_subset_image (φ : ι ↪ F) (f g : ι → F)
    (hoff : ∀ r : F, r ∉ Set.range φ →
      f (queryPoint φ r) = g (queryPoint φ r)) :
    (univ.filter (fun r : F => ¬ f (queryPoint φ r) = g (queryPoint φ r)))
      ⊆ (univ.filter (fun x : ι => ¬ f x = g x)).image φ := by
  intro r hr
  rw [mem_filter] at hr
  obtain ⟨-, hfail⟩ := hr
  by_cases hrange : r ∈ Set.range φ
  · obtain ⟨x, hx⟩ := hrange
    have hqp : queryPoint φ r = x := by
      rw [← hx]
      exact Function.leftInverse_invFun φ.injective x
    rw [mem_image]
    refine ⟨x, ?_, hx⟩
    rw [mem_filter]
    exact ⟨mem_univ x, by rw [← hqp]; exact hfail⟩
  · exact absurd (hoff r hrange) hfail

/-- **The binding-check pass count**: under off-image agreement, at least
`|F| − |disagreement(f, g)|` challenges pass. -/
theorem pass_count_ge (φ : ι ↪ F) (f g : ι → F)
    (hoff : ∀ r : F, r ∉ Set.range φ →
      f (queryPoint φ r) = g (queryPoint φ r)) :
    Fintype.card F - (univ.filter (fun x : ι => ¬ f x = g x)).card
      ≤ (univ.filter (fun r : F => f (queryPoint φ r) = g (queryPoint φ r))).card := by
  classical
  have hfail : (univ.filter (fun r : F => ¬ f (queryPoint φ r) = g (queryPoint φ r))).card
      ≤ (univ.filter (fun x : ι => ¬ f x = g x)).card := by
    calc (univ.filter (fun r : F => ¬ f (queryPoint φ r) = g (queryPoint φ r))).card
        ≤ ((univ.filter (fun x : ι => ¬ f x = g x)).image φ).card :=
          card_le_card (fail_subset_image φ f g hoff)
      _ ≤ (univ.filter (fun x : ι => ¬ f x = g x)).card := card_image_le
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := (univ : Finset F)) (p := fun r : F => f (queryPoint φ r) = g (queryPoint φ r))
  have huniv : (univ : Finset F).card = Fintype.card F := Finset.card_univ
  omega

/-- The off-image agreement hypothesis is achievable: all off-image challenges share ONE
query point (`Function.invFun`'s default), so agreement there is a single-point condition. -/
lemma off_image_queryPoint_const (φ : ι ↪ F) {r r' : F}
    (hr : r ∉ Set.range φ) (hr' : r' ∉ Set.range φ) :
    queryPoint φ r = queryPoint φ r' := by
  unfold queryPoint Function.invFun
  rw [dif_neg (by simpa [Set.range] using hr), dif_neg (by simpa [Set.range] using hr')]

end TightnessCore

end MultiRound

end StirIOP

/-! ## Axiom audit — all kernel-clean. -/
#print axioms StirIOP.MultiRound.TightnessCore.pass_count_ge
#print axioms StirIOP.MultiRound.TightnessCore.fail_subset_image
#print axioms StirIOP.MultiRound.TightnessCore.off_image_queryPoint_const
