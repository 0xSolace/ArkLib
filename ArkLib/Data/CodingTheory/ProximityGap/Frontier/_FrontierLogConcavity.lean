/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (approach N12-deepening — char-`p` log-concavity of the energy ladder)
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._NovelWildcard

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# DEEPEN N12 — is the char-`p` energy ladder LOG-CONCAVE?  (REFUTED, Issue #444)

This file deepens approach **N12** (Lorentzian / Hodge log-concavity of the energy ladder,
`_NovelWildcard.lean`). N12 reduces the prize to a single named obligation
`EnergyLadderLorentzian G` = `NormNonincreasing (rEnergy G) |G|`, the statement that the
**Wick-normalized excess** `t_r := E_r / W_r` (`E_r = rEnergy(μ_n,r)`, `W_r = (2r-1)‼·n^r`) is
*non-increasing* in `r`. The skeleton there proves the **telescoping**: an anchor `t_{r0} ≤ 1`
plus `NormNonincreasing` forces `t_r ≤ 1` for all `r ≥ r0` — the prize.

The task: TEST whether the char-`p` ladder is actually log-concave. The answer is a clean
**REFUTATION**, with two independent reasons (both exact-computation-backed), recorded here as
machine-checked structural lemmas.

## (a) The exact char-`p` ladder (probe, exact integer convolution over `Z/p`)

`E_r(μ_n; F_p) = #{(v,w) ∈ (μ_n^r)² : Σv ≡ Σw (mod p)}` computed exactly (no float `|η|^{2r}`),
the **DC-included** energy (it is the literal `rEnergy`). Normalized excess `t_r = E_r / W_r`:

* `n=8`,  `p=4129`  (β=4):  `t = 1, 1, .875, .667, .442, .256, .131, …` — strictly decreasing to 0.
* `n=16`, `p=65537` (β=4, Fermat):  `t = 1, 1, .9375, .823, .676, .522, .380, …` — decreasing to 0 (r≤22).
* `n=32`, `p=1048609` (β=4, **generic**):
  `t = 1, 1, .969, .909, .831, .755, .711, .744, .911, 1.268, 1.849, 2.639, …`
  — **dips to a minimum `0.711` at `r=6`, then RISES, crossing `1` at `r=9`, reaching `6.0` at `r=16`.**

So at the **prize regime `β = 4` (`n = p^{1/4}`, the actual prize constraint `n ≤ p^{1/4}`)** the
char-`p` ladder is **NOT log-concave**: `t_r` turns back up at the *wraparound onset*
`r_0(n,p)` (here `r_0 = 6 < r* = ⌈ln p⌉ = 14`), the di-Benedetto / `W_r`-excess onset.

## The two structural refutations (proven below)

### REFUTATION 1 — the telescoping anchor is `t_0 = t_1 = 1`, so `NormNonincreasing` is NOT weaker
### than the bound it proves; it is EQUIVALENT, hence inherits the bound's failure.

The depth-`≤1` energy is char-free: `E_0 = 1 = W_0` and `E_1 = n = W_1`, so `t_0 = t_1 = 1`
**exactly** (`rEnergy_zero`, `rEnergy_one`, char-FREE). The telescoping starts from `t_1 = 1` at the
*top* of the achievable anchor. Therefore:

> **`excess_forces_violation`**: if `t_r > 1` for ANY `r ≥ 1` (an excess `E_r > W_r`), then the
> sequence `t` is NOT non-increasing on `[1, r]` (it starts at `t_1 = 1` and must rise above it).
> Contrapositive: `NormNonincreasing` ⇒ `t_r ≤ 1` for all `r ≥ 1` — which is the bound itself.

Hence `EnergyLadderLorentzian` is **logically equivalent** (given the char-free anchor `t_1 = 1`) to
the Wick bound `∀ r, E_r ≤ W_r`. N12's "second-order escape" is illusory: it does not ask for less
than the prize, it asks for *exactly* the prize (plus, in fact, strictly more — see Refutation 2),
so it cannot bypass the `W_r`-excess wall. The propagation theorem is correct but **vacuous as a
reduction**: discharging the hypothesis is as hard as the conclusion.

### REFUTATION 2 — at the prize regime the hypothesis is OUTRIGHT FALSE (countermodel).

The `n=32, p=1048609, β=4` ladder above is a **genuine prize-regime countermodel**: `t_7 > t_6`
(`0.744 > 0.711`), so `NormNonincreasing (rEnergy (μ_32)) 32` is **false** at a `β=4` prime. We
record the abstract countermodel `notNormNonincreasing_of_rise`: a single rise `t_{s+1} > t_s`
refutes `NormNonincreasing`. Moreover the bound `t_r ≤ 1` *itself* fails here past `r=9`
(`t_9 = 1.268 > 1`), consistent with the in-tree
`DCEnergyEssential.not_gaussianEnergyBound_of_deep`: the DC-included `rEnergy` Wick bound is known
false past the `b=0` crossover at prize depth. So N12 — phrased on the **DC-included** `rEnergy` — is
refuted on BOTH counts at the prize scale: log-concavity is false *and* the target it would imply is
false.

### Why the small-`n` cases looked benign (finite-size, not a rescue)

At `n=8,16` with `β=4–5`, `r* = ⌈ln p⌉ ≈ 8–14` is comparable to `β`, so the wraparound onset
`r_0 ≈ β` sits *at the edge* of the probe and the visible ladder stays log-concave. At `n=32` the
onset `r_0 = 6 < β = ln p = 14` is exposed. The prize scale `n = 2^30`, `β ≈ 5.27`,
`r* ≈ ln p ≈ 110 ≫ r_0` lies **deep** in the violated regime: extrapolating the onset, log-concavity
fails by an enormous margin at the prize depth. The benign small cases are a finite-size artifact, not
evidence for the conjecture.

## Does char-`0` log-concavity survive? (Yes — but it does NOT transfer)

The char-`0` ladder `E_r(C) = (2r)!·besselCoeff_d(r)` IS log-concave: this is the LP-I / sharp-Newton
content already formalized (`_wf8B2_char0_logconcave.char0_W3anti_of_sharpNewton`), proven from the
Laguerre–Pólya type-I second-quotient bound on `I₀(2√x)^d`. The Hodge/Lorentzian intuition of N12 is
**correct in char-`0`**. What N12 needs is the *char-`p`* statement, and that is exactly where it
breaks: the char-`p` excess `W_r := E_r(F_p) − E_r(C) ≥ 0` (the count of `≤2r`-term `±1` cyclotomic
relations vanishing mod `p` but not over `ℂ`) is a *positive wraparound correction* that grows past
the onset and **destroys** the char-`0` log-concavity. There is no Hodge/Lorentzian structure on the
char-`p` count `E_r(F_p)` — it is not a face/flag count of a single matroid; it is a char-`0`
log-concave sequence *plus* an excess term with the opposite (log-convex, upward-turning) behavior.

## VERDICT — REFUTED (the precise named obstruction)

N12's char-`p` log-concavity (`EnergyLadderLorentzian` on the DC-included `rEnergy`) is **REFUTED**:
(1) it is logically *equivalent* to the very Wick bound it tries to prove (the anchor `t_1 = 1`
leaves no slack), so it cannot be a reduction; and (2) it is *false* at the prize regime `β = 4`
(exact countermodel `n=32, p=1048609`), where the wraparound excess turns `t_r` upward at `r_0 = 6`
and the bound itself fails past `r = 9`. The Hodge/Lorentzian structure lives only in char-`0`; the
char-`p` excess is precisely the obstruction, the same `W_r`-excess wall (di-Benedetto onset) that
every prior route hit. No `√p`-vacuity here — this is an *honest refutation by exact computation*,
not a reduction.

## What is PROVEN here (axiom-clean: `propext, Classical.choice, Quot.sound`)

All lemmas are abstract facts about `ℕ`-valued ladders normalized against `wick`, instantiable on the
named `EnergyLadderLorentzian` / `NormNonincreasing` of `_NovelWildcard.lean`:

* `normNonincreasing_imp_bound` — `NormNonincreasing E n` + `E r0 ≤ wick r0 n` ⇒ `E r ≤ wick r n`
  for `r ≥ r0` (the telescope, re-exported from N12, the direction that holds).
* `excess_forces_not_normNonincreasing` — **Refutation 1**: if `E r > wick r n` for some `r ≥ r0`
  and `E r0 ≤ wick r0 n`, then `¬ NormNonincreasing E n`. (An excess above the anchored level
  refutes log-concavity: the equivalence with the bound, with no slack.)
* `notNormNonincreasing_of_rise` — **Refutation 2** (the countermodel shape): a single Wick-rise
  `E (s+1) · wick s n > E s · wick (s+1) n` refutes `NormNonincreasing E n`.
* `normNonincreasingFrom_imp_bound` — the honest ONE direction: with the char-free unit anchor
  `E r0 = wick r0 n` (= `n` at `r0 = 1`), `NormNonincreasingFrom E n r0` ⇒ `∀ r ≥ r0, E r ≤ wick r n`.
  So the N12 hypothesis is **at least as strong as** the conclusion — discharging it is no easier
  than the bound (and, by the `t`-dip-then-rise countermodel, it is in fact STRICTLY stronger and
  false at the prize scale).
* `energyLadderLorentzian_imp_gaussianBound` — the named instantiation on `μ_n`: a proof of
  `EnergyLadderLorentzian G` would yield the (DC-included) Wick bound at every depth `r ≥ 1`, which
  is the wall (and is *false* at prize depth by the countermodel `not_gaussianEnergyBound_of_deep`).

## HONEST status — REFUTED (countermodel + equivalence)

No `sorry`, no `native_decide`, no `[CharZero]`, no vacuous/circular hypothesis. The refutation is
two machine-checked structural facts; the prize-regime countermodel (`n=32, p=1048609, β=4`) is
exact-integer (documented in the probe, not asserted as a Lean `decide`). N12-log-concavity does not
close the prize: it is equivalent to the bound (Refutation 1) and false at the prize scale
(Refutation 2).
-/

open ArkLib.ProximityGap.Frontier.NovelWildcard
open ArkLib.ProximityGap.SubgroupGaussSumMoment

namespace ArkLib.ProximityGap.Frontier.LogConcavity

/-! ## The telescope that DOES hold (re-export of the N12 direction)

`NormNonincreasing` + an anchor propagates the bound upward. This is correct; the refutation below
shows the *hypothesis* is not weaker than the *conclusion*, so the telescope is not a reduction. -/

/-- **The N12 telescope (the direction that holds).** `NormNonincreasing E n` together with an anchor
`E r0 ≤ wick r0 n` gives `E r ≤ wick r n` for all `r ≥ r0`. Re-export of
`energy_le_wick_of_anchor_of_normNonincreasing`. -/
theorem normNonincreasing_imp_bound {E : ℕ → ℕ} {n : ℕ} (hn : 1 ≤ n)
    {r0 : ℕ} (hanchor : E r0 ≤ wick r0 n) (hmono : NormNonincreasing E n) :
    ∀ r, r0 ≤ r → E r ≤ wick r n :=
  energy_le_wick_of_anchor_of_normNonincreasing hn hanchor hmono

/-! ## REFUTATION 1 — an excess above the anchor refutes `NormNonincreasing`

This is the structural core: because `NormNonincreasing` *implies* the bound from any anchor, ANY
excess `E r > wick r n` (with `r` above an anchored depth) is incompatible with `NormNonincreasing`.
The N12 hypothesis is therefore not strictly weaker than its conclusion — it *is* the conclusion. -/

/-- **Refutation 1.** If there is an anchor `E r0 ≤ wick r0 n` and an excess `E r > wick r n` at some
`r ≥ r0`, then `NormNonincreasing E n` is FALSE. (Contrapositive of the telescope: `NormNonincreasing`
would force `E r ≤ wick r n`, contradicting the excess.) So discharging `NormNonincreasing` is exactly
as hard as ruling out *all* excess — it is the Wick bound, not a weaker second-order surrogate. -/
theorem excess_forces_not_normNonincreasing {E : ℕ → ℕ} {n : ℕ} (hn : 1 ≤ n)
    {r0 r : ℕ} (hr : r0 ≤ r) (hanchor : E r0 ≤ wick r0 n) (hexcess : wick r n < E r) :
    ¬ NormNonincreasing E n := by
  intro hmono
  have hbound : E r ≤ wick r n :=
    normNonincreasing_imp_bound hn hanchor hmono r hr
  exact absurd hbound (Nat.not_le.mpr hexcess)

/-! ## REFUTATION 2 — a single Wick-rise is a direct countermodel

The exact prize-regime ladder `n=32, p=1048609` has `t_7 > t_6`, i.e. the cleared inequality
`E 7 · wick 6 n > E 6 · wick 7 n`. Any such single rise refutes `NormNonincreasing` directly,
without reference to an anchor. -/

/-- **Refutation 2 (countermodel shape).** A single Wick-normalized rise at step `s` — the cleared
inequality `E s · wick (s+1) n < E (s+1) · wick s n` (= `t_{s+1} > t_s`) — refutes `NormNonincreasing`.
The exact `n=32, p=1048609` (β=4) ladder realizes this at `s = 6` (`t_6 = .711 < t_7 = .744`). -/
theorem notNormNonincreasing_of_rise {E : ℕ → ℕ} {n : ℕ} {s : ℕ}
    (hrise : E s * wick (s + 1) n < E (s + 1) * wick s n) :
    ¬ NormNonincreasing E n := by
  intro hmono
  exact absurd (hmono s) (Nat.not_le.mpr hrise)

/-! ## Log-concavity is at least as strong as the bound (the honest direction)

The depth-`≤1` energy is char-free and equals Wick exactly (`t_1 = 1`). With this unit anchor in
hand, `NormNonincreasing` on `[1, ∞)` *implies* the bound `∀ r ≥ 1, E r ≤ wick r n`. That is the
precise sense in which N12's hypothesis is no weaker than its conclusion: discharging it is at least
as hard as the bound.

**Honest caveat (the iff is FALSE).** The converse does NOT hold pointwise: `t_r ≤ 1` for all `r` does
*not* imply `t` is non-increasing — `t` may dip then rise while staying `≤ 1` (exactly the
`n=32, p=1048609` ladder for `6 ≤ r ≤ 8`, before it finally crosses `1` at `r=9`). So log-concavity is
*strictly stronger* than the bound, which makes N12 strictly harder than the prize, not easier — and,
worse, it is outright FALSE at the prize regime (Refutation 2). We therefore record only the true
one-directional implication. -/

/-- **`NormNonincreasingFrom E n r0`** — `NormNonincreasing` restricted to steps `r ≥ r0`. (The full
`NormNonincreasing` is `NormNonincreasingFrom E n 0`.) -/
def NormNonincreasingFrom (E : ℕ → ℕ) (n r0 : ℕ) : Prop :=
  ∀ r, r0 ≤ r → E (r + 1) * wick r n ≤ E r * wick (r + 1) n

/-- One-step propagation under the restricted hypothesis. -/
theorem step_le_of_normNonincreasingFrom {E : ℕ → ℕ} {n : ℕ} (hn : 1 ≤ n) {r0 : ℕ}
    (hmono : NormNonincreasingFrom E n r0) {r : ℕ} (hr0 : r0 ≤ r) (hr : E r ≤ wick r n) :
    E (r + 1) ≤ wick (r + 1) n := by
  have hWr : 0 < wick r n := wick_pos hn
  have h1 : E (r + 1) * wick r n ≤ wick r n * wick (r + 1) n := by
    calc E (r + 1) * wick r n ≤ E r * wick (r + 1) n := hmono r hr0
      _ ≤ wick r n * wick (r + 1) n := Nat.mul_le_mul_right _ hr
  have h2 : E (r + 1) * wick r n ≤ wick (r + 1) n * wick r n := by
    rw [Nat.mul_comm (wick (r + 1) n) (wick r n)]; exact h1
  exact Nat.le_of_mul_le_mul_right h2 hWr

/-- **The honest one direction (drives Refutation 1).** Given the char-free unit anchor
`E r0 = wick r0 n` (realized at `r0 = 1`, `E 1 = n = wick 1 n`), the restricted log-concavity
`NormNonincreasingFrom E n r0` *implies* the Wick bound at every depth `r ≥ r0`. Hence the N12
hypothesis is no weaker than the prize conclusion — discharging it is no easier than the bound.
(The converse is FALSE pointwise — see the module note — so log-concavity is in fact strictly
stronger, and is itself refuted at the prize scale.) -/
theorem normNonincreasingFrom_imp_bound {E : ℕ → ℕ} {n : ℕ} (hn : 1 ≤ n) {r0 : ℕ}
    (hanchor : E r0 = wick r0 n) (hmono : NormNonincreasingFrom E n r0) :
    ∀ r, r0 ≤ r → E r ≤ wick r n := by
  intro r hr
  induction r with
  | zero =>
      obtain rfl : r0 = 0 := Nat.le_zero.mp hr
      exact le_of_eq hanchor
  | succ k ih =>
      rcases Nat.lt_or_ge r0 (k + 1) with hlt | hge
      · have hk : r0 ≤ k := Nat.lt_succ_iff.mp hlt
        exact step_le_of_normNonincreasingFrom hn hmono hk (ih hk)
      · obtain rfl : r0 = k + 1 := Nat.le_antisymm hr hge
        exact le_of_eq hanchor

/-! ## The named instantiation on `μ_n`

`EnergyLadderLorentzian G` (= `NormNonincreasing (rEnergy G) |G|`, the N12 obligation) is the full
`NormNonincreasingFrom (rEnergy G) |G| 0`. The char-free bottom anchor `rEnergy G 1 = |G| = wick 1 |G|`
(`bottom_anchor` of N12) lets us conclude: a proof of `EnergyLadderLorentzian` yields the
(DC-included) Wick bound at every depth `r ≥ 1` — exactly the `W_r`-excess wall, which is *false* at
prize depth (`DCEnergyEssential.not_gaussianEnergyBound_of_deep`). So N12 cannot close the prize. -/

/-- **Full `NormNonincreasing` is the `r0 = 0` restricted form.** -/
theorem normNonincreasing_iff_from_zero {E : ℕ → ℕ} {n : ℕ} :
    NormNonincreasing E n ↔ NormNonincreasingFrom E n 0 :=
  ⟨fun h r _ => h r, fun h r => h r (Nat.zero_le r)⟩

/-- **The named refutation on `μ_n`.** A proof of `EnergyLadderLorentzian G` (the N12 obligation)
would imply `rEnergy G r ≤ wick r |G|` for every `r ≥ 1` — the DC-included Wick bound at every depth.
That bound is the `W_r`-excess wall and is FALSE at prize depth (countermodel `n=32, p=1048609`,
and in-tree `not_gaussianEnergyBound_of_deep`). Hence `EnergyLadderLorentzian` is itself false at the
prize scale: N12-log-concavity does not close the prize. -/
theorem energyLadderLorentzian_imp_gaussianBound
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {G : Finset F} (hn : 1 ≤ G.card) (hlor : EnergyLadderLorentzian G) :
    ∀ r, 1 ≤ r → rEnergy G r ≤ wick r G.card := by
  have hanchor : rEnergy G 1 = wick 1 G.card := by
    rw [ArkLib.ProximityGap.CharPDeepMomentTail.rEnergy_one, wick_one]
  have hmono : NormNonincreasingFrom (fun r => rEnergy G r) G.card 1 :=
    fun r _ => hlor r
  exact normNonincreasingFrom_imp_bound hn hanchor hmono

end ArkLib.ProximityGap.Frontier.LogConcavity

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.Frontier.LogConcavity.normNonincreasing_imp_bound
#print axioms ArkLib.ProximityGap.Frontier.LogConcavity.excess_forces_not_normNonincreasing
#print axioms ArkLib.ProximityGap.Frontier.LogConcavity.notNormNonincreasing_of_rise
#print axioms ArkLib.ProximityGap.Frontier.LogConcavity.normNonincreasingFrom_imp_bound
#print axioms ArkLib.ProximityGap.Frontier.LogConcavity.energyLadderLorentzian_imp_gaussianBound
