/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.CandidateDisproofLoop6

/-!
# Loop 7 (O4 + O5) — the conditional disproof, and Frobenius-robustness across the chain

Loop 6 (O3) showed: with prime-field inputs and a Frobenius-stable code, the MCA bad-γ set is
closed under `φ : x ↦ x^p`, so a constant bad-count bound forces every bad scalar into a
bounded-degree subfield. This file closes the two follow-up angles from `DISPROOF_LOG.md`.

## O4 — the conditional disproof (what realizing the obstruction would buy)

`realizing_high_degree_bad_scalar_disproves`: if one can *realize* a Frobenius-closed bad set
containing a scalar of degree `d > C` at prize radius — where `C = (2^m)^{c₁}/(ρ^{c₂}η^{c₃})` is the
conjecture's constant — then the conjecture is **false** (we derive `False` from the bound). This is
the exact, machine-checked statement of "the only thing between us and a disproof is a high-degree
bad scalar in the live band." It is a *conditional* disproof: its hypotheses include the
realizability that O3 left open.

**Disproof of the disproof (O4):** the antecedent is precisely the unestablished beyond-Johnson
case. Below the Johnson radius BCIKS20 forbids a lone high-degree orbit (bad set is small or all of
`F`); in the band `[1−√ρ, 1−ρ−η]` no construction is known. So the conditional does not fire — no
disproof, only a sharpened target.

## O5 — Frobenius-robustness: the GS-row restriction is not an escape

One hope was that `epsMCAgs`'s GS-row event (strictly rarer than the raw line-close event, via
`epsMCAgs ≤ epsCA ≤ line-close`) might cap the bad count *below* the Frobenius lower bound, refuting
O3-style growth. It cannot: **every** level of the dominance chain is defined by closeness to the
same Frobenius-stable code with `φ`-fixed inputs, hence each bad-event predicate is `φ`-invariant,
hence each satisfying set is `φ`-closed and inherits the *same* orbit lower bound. We prove this for
an arbitrary `φ`-invariant predicate (`frobenius_invariant_card_ge`): the constraint is robust, so
O5 provides no refutation of O3 — it strengthens it (the bounded-subfield condition binds `epsCA`
and the line-close error too, not just `mcaEvent`).

All results are sorry-free and axiom-clean. See `DISPROOF_LOG.md` (O4, O5).
-/

namespace ArkLib.ProximityGap.DisproofLoop7

open ArkLib.ProximityGap.DisproofLoop6

variable {F : Type*} [Field F] [DecidableEq F]

/-- **O4 — conditional disproof.** If a Frobenius-closed bad set `S` (the O3 setup: prime-field
inputs, `φ`-stable code) has cardinality bounded by the conjecture's constant `C`
(`epsMCA = #S/q ≤ C/q`), yet contains a scalar `y` of degree `d > C` over `F_p` (its first `d`
Frobenius iterates distinct), then `False`: realizing such a scalar disproves the conjecture. The
hypotheses isolate exactly the open realizability question. -/
theorem realizing_high_degree_bad_scalar_disproves
    {p : ℕ} {S : Finset F} {C : ℝ}
    (hclosed : ∀ x ∈ S, x ^ p ∈ S)
    (hbound : (S.card : ℝ) ≤ C)
    {y : F} (hy : y ∈ S) (d : ℕ)
    (hinj : Set.InjOn (fun k => y ^ (p ^ k)) (Finset.range d))
    (hdeg : C < (d : ℝ)) : False := by
  have hle : (d : ℝ) ≤ C := const_badcount_forbids_high_degree hclosed hbound hy d hinj
  linarith

section Robustness
variable [Fintype F]

/-- A `φ`-invariant predicate's satisfying set is closed under `φ : x ↦ x^p`. The bad-event
predicates of the whole dominance chain (`mcaEvent`, CA, line-close) are `φ`-invariant when the code
is `φ`-stable and the inputs are `φ`-fixed, since closeness to a `φ`-stable code is `φ`-invariant. -/
theorem frobenius_invariant_filter_closed
    {p : ℕ} (P : F → Prop) [DecidablePred P]
    (hinv : ∀ x, P x → P (x ^ p)) :
    ∀ x ∈ Finset.univ.filter P, x ^ p ∈ Finset.univ.filter P := by
  intro x hx
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨Finset.mem_univ _, hinv x hx.2⟩

/-- **O5 — robustness of the Frobenius lower bound.** For *any* `φ`-invariant bad-event predicate
`P`, if some satisfying scalar `y` has degree `d` over `F_p`, then the satisfying set has cardinality
`≥ d`. Applying this to the line-close / CA / mcaEvent predicates shows the GS-row restriction does
not escape the Frobenius lower bound: the bounded-subfield constraint binds every level of
`epsMCAgs ≤ epsCA ≤ line-close`. -/
theorem frobenius_invariant_card_ge
    {p : ℕ} (P : F → Prop) [DecidablePred P]
    (hinv : ∀ x, P x → P (x ^ p))
    {y : F} (hy : P y) (d : ℕ)
    (hinj : Set.InjOn (fun k => y ^ (p ^ k)) (Finset.range d)) :
    d ≤ (Finset.univ.filter P).card := by
  refine frobenius_orbit_card_le (frobenius_invariant_filter_closed P hinv) ?_ d hinj
  rw [Finset.mem_filter]
  exact ⟨Finset.mem_univ _, hy⟩

end Robustness

end ArkLib.ProximityGap.DisproofLoop7
