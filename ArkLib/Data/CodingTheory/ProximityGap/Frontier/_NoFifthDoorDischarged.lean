/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NoFifthDoorTetrachotomy

/-!
# No-fifth-door, classical side DISCHARGED at the proven scales (#444, Lane 3 capstone)

`_NoFifthDoorTetrachotomy.forces_doorIV` is the no-fifth-door capstone, but it takes the
*abstract* hypothesis

  `hclassicalOvershoots : ∀ m', m'.door.isClassical → m'.OvershootsBGK n L`

— "*every* classical-door mechanism, *at any scale*, overshoots BGK".  That abstract quantifier is
genuinely STRONGER than what the campaign has proven: a classical mechanism with an artificially
tiny `certScale` does NOT overshoot, so `hclassicalOvershoots` is not literally a theorem.  What IS
proven is the overshoot of each classical door **at its concrete proven scale**:

* door (ii) at the √q-completion ceiling `completionScale q = √q`
  (`completionMechanism_overshootsBGK`, from the proven Polya–Vinogradov / Gauss-sum ceiling), and
* doors (i)/(iii) at the BGK SOTA value `C·n^{1−δ}`, `δ < 1/2`
  (`momentEVT_mechanism_overshootsBGK_eventually`, from the SOTA exponent wall).

This file closes the notational gap that `_NamedLeverRefutationCapstone`'s header explicitly flags
("it does **not** by itself discharge the *abstract* `hclassicalOvershoots` quantifier"): instead of
postulating the abstract hypothesis, it states the no-fifth-door conclusion DIRECTLY against the
concrete proven-scale mechanisms — a kernel-checked capstone with **no abstract postulate**.

The deliverable is the citable form a referee wants: *at the concrete proven door scales, in the
prize regime, the ONLY mechanism that can certify a prize-scale bound is door (iv)* — Shaw's
tetrachotomy with the classical side discharged from theorems, not assumed.

## Honesty
This is pure COMPOSITION of three already-proven facts
(`completionMechanism_overshootsBGK`, `momentEVT_mechanism_overshootsBGK_eventually`,
`not_certifies_prizeScale_of_overshoot`).  It is NOT a CORE / cancellation / completion /
moment-saving / anti-concentration / capacity claim, and it does NOT prove door (iv) is
*achievable*.  CORE `M(μ_n) ≤ C·√(n·log(p/n))` stays **OPEN**.  The contribution is removing the
last abstract hypothesis from the no-fifth-door capstone, so the tetrachotomy is backed end-to-end
by kernel-checked concrete-scale statements.
-/

namespace ArkLib.ProximityGap.Frontier.NoFifthDoorDischarged

open ArkLib.ProximityGap.Frontier.NoFifthDoorTetrachotomy

/-! ## The completion door, discharged: it cannot be a prize certificate -/

/-- **Completion door discharged.**  In the prize regime `L > 1`, `n·L ≤ q`, the completion
mechanism at its *proven* √q ceiling does not certify a prize-scale bound: the only way a completion
mechanism could certify `M ≤ √n` is impossible at the proven scale.  (Direct restatement of
`completion_not_certifies_prizeScale` in mechanism language.) -/
theorem completionMechanism_not_certifies_prize {n L q : ℝ}
    (hn : 0 < n) (hL : 1 < L) (hq : n * L ≤ q) :
    ¬ ((⟨DoorType.completion, completionScale q⟩ : Mechanism).certScale ≤ prizeScale n) :=
  not_certifies_prizeScale_of_overshoot hn hL (completionMechanism_overshootsBGK hq)

/-- A completion mechanism at the proven √q scale that *does* certify the prize is impossible: from
a prize certificate at that scale we derive `False`.  The contrapositive packaging of the above. -/
theorem completionMechanism_prize_cert_absurd {n L q : ℝ}
    (hn : 0 < n) (hL : 1 < L) (hq : n * L ≤ q)
    (hcert : (⟨DoorType.completion, completionScale q⟩ : Mechanism).certScale ≤ prizeScale n) :
    False :=
  completionMechanism_not_certifies_prize hn hL hq hcert

/-! ## The moment / extreme-value doors, discharged: no prize certificate at SOTA scale -/

/-- **Moment/EVT door discharged (concrete scale).**  For any SOTA constant `C > 0` and sub-prize
exponent `δ < 1/2`, there is a threshold `N₀` past which the moment mechanism at the SOTA value
`C·n^{1−δ}` does NOT certify a prize-scale bound: doors (i)/(iii) fail the prize certificate at
their proven scale for all large `n`, with no abstract hypothesis. -/
theorem momentMechanism_not_certifies_prize_eventually
    {C L δ : ℝ} (hC : 0 < C) (hL : 1 < L) (hLnn : 0 ≤ L) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ m : ℝ, N₀ ≤ m → 2 ≤ m →
      ¬ ((⟨DoorType.moment, C * m ^ (1 - δ)⟩ : Mechanism).certScale ≤ prizeScale m) := by
  obtain ⟨N₀, hN₀⟩ := momentEVT_mechanism_overshootsBGK_eventually hC hLnn hδ
  refine ⟨N₀, fun m hm hm2 => ?_⟩
  have hmpos : 0 < m := by linarith
  exact not_certifies_prizeScale_of_overshoot hmpos hL (hN₀ m hm)

/-! ## The DISCHARGED no-fifth-door capstone

The headline: at the concrete proven door scales, in the prize regime, any mechanism that certifies
a prize-scale bound must be door (iv).  This is `forces_doorIV` with the abstract
`hclassicalOvershoots` hypothesis REPLACED by the concrete proven-scale discharges — no abstract
postulate remains. -/

/-- A `Mechanism` *sits at its proven classical scale* (in the prize regime `n·L ≤ q`, with the
moment SOTA constant `C`, exponent `δ`) when:

* if it is the completion door, its `certScale` is the proven `√q` ceiling; and
* if it is the moment or extreme-value door, its `certScale` is the SOTA value `C·n^{1−δ}`.

Door (iv) (`newEvaluation`) is unconstrained — that is exactly the point: it is the only door whose
scale the campaign has NOT proven to overshoot. -/
def AtProvenScale (m : Mechanism) (n q C δ : ℝ) : Prop :=
  (m.door = DoorType.completion → m.certScale = completionScale q) ∧
  (m.door = DoorType.moment → m.certScale = C * n ^ (1 - δ)) ∧
  (m.door = DoorType.extremeValue → m.certScale = C * n ^ (1 - δ))

/-- **No-fifth-door, classical side DISCHARGED.**  Fix the prize regime `L > 1`, `n·L ≤ q`, a moment
SOTA constant `C > 0` with sub-prize exponent `δ < 1/2`, and suppose the moment/EVT SOTA value at
this `n` already exceeds the BGK scale (`bgkScale n L ≤ C·n^{1−δ}` — the proven eventual fact, here
as the concrete arithmetic hypothesis that holds for all `n ≥ N₀`).  Then ANY mechanism `m` that

* sits at its proven classical scale (`AtProvenScale`), and
* certifies a prize-scale bound (`m.certScale ≤ prizeScale n`),

is door (iv) (`newEvaluation`).  No abstract `hclassicalOvershoots` quantifier: each classical
door's overshoot is the *proven concrete-scale* fact (completion = √q ≥ √(nL); moment/EVT = SOTA ≥
√(nL)). -/
theorem forces_doorIV_atProvenScale {m : Mechanism} {n L q C δ : ℝ}
    (hn : 0 < n) (hL : 1 < L) (hq : n * L ≤ q)
    (hsota : bgkScale n L ≤ C * n ^ (1 - δ))
    (hscale : AtProvenScale m n q C δ)
    (hcert : m.certScale ≤ prizeScale n) :
    m.door = DoorType.newEvaluation := by
  obtain ⟨hcompl, hmom, hext⟩ := hscale
  -- The SOTA-scale moment/EVT mechanism overshoots BGK at this n (from `hsota`).
  have hmomOver : (⟨DoorType.moment, C * n ^ (1 - δ)⟩ : Mechanism).OvershootsBGK n L := hsota
  have hextOver : (⟨DoorType.extremeValue, C * n ^ (1 - δ)⟩ : Mechanism).OvershootsBGK n L := hsota
  cases hd : m.door with
  | completion =>
      exfalso
      have hms : m.certScale = completionScale q := hcompl hd
      have : completionScale q ≤ prizeScale n := hms ▸ hcert
      exact completion_not_certifies_prizeScale hn hL hq this
  | moment =>
      exfalso
      have hms : m.certScale = C * n ^ (1 - δ) := hmom hd
      have hle : C * n ^ (1 - δ) ≤ prizeScale n := hms ▸ hcert
      exact not_certifies_prizeScale_of_overshoot hn hL hmomOver hle
  | extremeValue =>
      exfalso
      have hms : m.certScale = C * n ^ (1 - δ) := hext hd
      have hle : C * n ^ (1 - δ) ≤ prizeScale n := hms ▸ hcert
      exact not_certifies_prizeScale_of_overshoot hn hL hextOver hle
  | newEvaluation => rfl

/-- **The discharged classical-overshoot certificate.**  At the proven scales, in the prize regime,
the abstract `hclassicalOvershoots` hypothesis of `forces_doorIV` IS supplied: every classical door,
*evaluated at its proven scale*, overshoots BGK.  This is the discharge witness, packaged as the
exact shape `forces_doorIV` consumes but only over the proven-scale classical mechanisms. -/
theorem classicalOvershoots_atProvenScale {n L q C δ : ℝ}
    (hq : n * L ≤ q) (hsota : bgkScale n L ≤ C * n ^ (1 - δ)) :
    ((⟨DoorType.completion, completionScale q⟩ : Mechanism).OvershootsBGK n L) ∧
    ((⟨DoorType.moment, C * n ^ (1 - δ)⟩ : Mechanism).OvershootsBGK n L) ∧
    ((⟨DoorType.extremeValue, C * n ^ (1 - δ)⟩ : Mechanism).OvershootsBGK n L) :=
  ⟨completionMechanism_overshootsBGK hq, hsota, hsota⟩

/-- **Headline (eventual form).**  Combining the SOTA eventual-domination theorem with the
discharge: for any SOTA constant `C > 0`, `δ < 1/2`, prize regime `L > 1`, `n·L ≤ q`, there is a
threshold `N₀` such that for every `n ≥ N₀` (and `n ≥ 2`), any proven-scale mechanism certifying a
prize-scale bound is door (iv).  The classical side is fully discharged from theorems; no abstract
hypothesis survives. -/
theorem forces_doorIV_eventually
    {L q C δ : ℝ} (hC : 0 < C) (hL : 1 < L) (hLnn : 0 ≤ L) (hδ : δ < 1 / 2) :
    ∃ N₀ : ℝ, ∀ n : ℝ, N₀ ≤ n → 2 ≤ n → n * L ≤ q →
      ∀ m : Mechanism, AtProvenScale m n q C δ → m.certScale ≤ prizeScale n →
        m.door = DoorType.newEvaluation := by
  obtain ⟨N₀, hN₀⟩ := momentEVT_scale_eventually_ge_bgkScale hC hLnn hδ
  refine ⟨N₀, fun n hn hn2 hq m hscale hcert => ?_⟩
  have hnpos : 0 < n := by linarith
  have hsota : bgkScale n L ≤ C * n ^ (1 - δ) := hN₀ n hn
  exact forces_doorIV_atProvenScale hnpos hL hq hsota hscale hcert

end ArkLib.ProximityGap.Frontier.NoFifthDoorDischarged
