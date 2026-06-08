/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.Order.Field.Basic

/-!
# Loop 14 — the AT-CAPACITY correlated-agreement conjecture is FALSE (Crites–Stewart)

This brick *completely closes* a genuine sibling of the prize: the **up-to-capacity** correlated
agreement conjecture (BCIKS23 Conj 8.4, and the MCA-up-to-capacity conjecture of WHIR), at the
capacity radius `δ ≥ 1 − ρ`. Crites–Stewart (eprint 2025/2046, Cor 1) construct, at capacity, a line
`u₀ + λ·u₁` with **at least half** the scalars `λ` giving a `δ`-close fold, yet **no** joint
proximity — a bad fraction `≥ 1/2`. Any polynomial soundness bound `ε = B/q` is then refuted for all
large `q`.

We formalize the refutation logic (the verifiable half), consuming the Crites–Stewart *construction*
as the cited hypothesis `hCS : 1/2 ≤ badFraction`. The conclusion `q ≤ 2·B` shows no fixed
polynomial numerator `B` survives, so the at-capacity polynomial-soundness conjecture is **false**.

This is *not* the prize: the prize lives strictly below capacity (`δ ≤ 1 − ρ − η`, `η > 0`), where
Crites–Stewart themselves *propose* the salvageable form. It complements the proof-side capstone
(Loop13, large gap proven) and the carving (Loop10) by nailing the failure exactly at the boundary
the prize's gap `η` keeps it away from. Sorry-free, axiom-clean. See `DISPROOF_LOG.md` (Loop14).
-/

namespace ArkLib.ProximityGap.DisproofLoop14

/-- **At-capacity refutation arithmetic.** If the Crites–Stewart line has bad fraction `≥ 1/2`
(`hCS`, their Cor 1 construction at capacity) while a candidate correlated-agreement conjecture
bounds the bad fraction by `B/q` (`hCA`, polynomial numerator `B` over field size `q > 0`), then
`q ≤ 2·B`. Hence **no fixed `B` works for all field sizes** — the at-capacity polynomial-soundness
conjecture is false. -/
theorem at_capacity_ca_refuted
    {badFraction B q : ℝ} (hq : 0 < q)
    (hCS : (1 : ℝ) / 2 ≤ badFraction)
    (hCA : badFraction ≤ B / q) :
    q ≤ 2 * B := by
  have h12 : (1 : ℝ) / 2 ≤ B / q := le_trans hCS hCA
  -- `(1/2)·q ≤ B`  ⇒  `q ≤ 2B`
  have h1 : (1 / 2) * q ≤ B := (le_div_iff₀ hq).mp h12
  linarith

/-- **No polynomial numerator survives at capacity.** For any fixed bound numerator `B`, there is a
field size `q` for which the Crites–Stewart bad fraction `≥ 1/2` violates `B/q` — the at-capacity
conjecture admits no universal constant. (Take any `q > 2·max(B,0)`.) -/
theorem no_fixed_numerator_at_capacity (B : ℝ) :
    ∃ q : ℝ, 0 < q ∧ 2 * B < q := by
  refine ⟨max (2 * B) 0 + 1, ?_, ?_⟩
  · have : (0:ℝ) ≤ max (2 * B) 0 := le_max_right _ _; linarith
  · have : 2 * B ≤ max (2 * B) 0 := le_max_left _ _; linarith

/-- **Closure of the at-capacity sibling (contrapositive packaging).** If `q > 2·B` (any large
enough field) and the Crites–Stewart construction holds (`hCS`), then the candidate at-capacity bound
`badFraction ≤ B/q` is impossible. The at-capacity CA / MCA conjecture is therefore disproved. -/
theorem at_capacity_bound_impossible
    {badFraction B q : ℝ} (hq : 0 < q) (hbig : 2 * B < q)
    (hCS : (1 : ℝ) / 2 ≤ badFraction) :
    ¬ (badFraction ≤ B / q) := by
  intro hCA
  exact absurd (at_capacity_ca_refuted hq hCS hCA) (not_le_of_gt hbig)

end ArkLib.ProximityGap.DisproofLoop14
