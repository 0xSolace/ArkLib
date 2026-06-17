/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._EtaRealNegClosed

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
# The sign `s_b` of the real period `η_b` carries NO character structure (#444, N13 sign-law wall)

**Frontier refutation brick (NON-MOMENT, EXTEND-proven, rule-4 cartography).**

The `_EtaRealNegClosed` brick proved that on the negation-closed prize subgroup `μ_n` (`n` even)
the incomplete Gauss period `η_b = Σ_{x∈μ_n} ψ(b·x)` is REAL, hence

> `η_b = s_b · ‖η_b‖`  with a SIGN `s_b ∈ {+1, −1}`  (`eta_eq_ofReal_re` ⟹ `arg η_b ∈ {0, π}`).

The strongest surviving "third route" (census §1.3 N13: the phase-aware contractive transfer
operator) was sharpened by `_EtaRealNegClosed` to a *discrete* object: the N13 "phase" is the sign
`s_b`. The companion `DilationRealSignCocycle` then reformulated the open core as a **real ±1 sign
cocycle**: a frequency stays on the non-cancelling doubling trajectory iff its descent signs are all
`+`, and the residual open content is the sign-cocycle large-deviation statement (no all-`+` descent
path survives). The natural hope for cracking THAT statement is that the sign pattern `b ↦ s_b` is
itself **multiplicatively structured**: a quadratic character, a Legendre symbol, or at least a
group homomorphism `F_p^* ⧸ μ_n → {±1}`. IF it were, the relative dilation sign `s_{ζb} / s_b`
(`ζ` of order `2n`) would be a CONSTANT independent of `b`, the sign cocycle would be a coboundary,
and the descent could be telescoped by a character argument.

This file REFUTES that hope (rule-4 cartography for the `DilationRealSignCocycle` residual): the
absolute sign `b ↦ s_b` is NOT a homomorphism, so the sign cocycle is NOT a coboundary and no
character/homomorphism descent on the sign can isolate the worst frequency or exclude the all-`+`
descent word.

## The probe verdict (rule 2, `scripts/probes/probe_eta_sign_qr_structure.py`)

Over the prize regime (proper thin `μ_n = 2^a`, `p ≫ n^3`, `p ≡ 1 (mod n)`, multiple primes incl.
Fermat-type, NEVER `n = q−1`):
* **H1** `s_b` is coset-constant on `F_p^* ⧸ μ_n`: TRUE (the object is well-defined).
* **H2** `s_b = Legendre(b ∣ p)`: ~45 to 63% agreement = pure NOISE. NOT the quadratic character.
* **H3** `s_b` multiplicative (`s_{b₁b₂} = s_{b₁}·s_{b₂}`): 36 to 69 failures / 120 pairs. MASSIVELY
  non-multiplicative. `b ↦ s_b` is NOT a homomorphism.
* **H4** relative dilation sign `s_{ζb}/s_b` constant in `b`: `{−1, +1}` (NOT constant) generically.

Explicit decidable witness (`probe_eta_sign_witness.py`): at `p = 89`, `μ_4 = {1,34,55,88}`,
`s_2 = +1` and `s_{4} = s_{2·2} = −1`, so `s_{2·2} ≠ s_2 · s_2`. The sign fails multiplicativity at
the smallest dilation `b₁ = b₂ = 2`.

## What this file proves (the abstract obstruction, axiom-clean)

The numeric facts above are real-analytic (transcendental cosine sums, not Lean-decidable). What IS
cleanly formalizable is the **mechanism**: a `{±1}` sign that fails multiplicativity at even one
single witness is NOT a `MonoidHom`, and consequently the relative-dilation sign `s(ζb)·s(b)` is NOT
independent of `b`, exactly the H4 obstruction. So no character/homomorphism descent on the sign
can isolate the worst frequency.

This is a CONSTRAINT on the open N13 lever (rule 4 cartography), NOT a bound on `M`. The
`√(n log(p/n))` core is untouched and OPEN: the sign carries no usable cancellation structure, which
is precisely why the magnitude side (wf-A1: children perfectly phase-aligned at `b*`,
`θ@b* = 0` exactly) cannot be saved by a sign argument, and the `DilationRealSignCocycle`
sign-cocycle large-deviation residual cannot be discharged by a character/coboundary argument.
NON-MOMENT (pure sign/character algebra, not an additive-energy route).

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`. Issue #444.
-/

namespace ProximityGap.Frontier.EtaSignNonMultiplicative

/-- A `{±1}`-valued sign function on a monoid `M`. We model `s_b ∈ {+1,-1} ⊆ ℤ`. -/
abbrev Sign (M : Type*) := M → ℤ

/-- The sign of a real period: `+1` if `0 ≤ (η_b).re`, else `-1`. This is the multiplier `s_b` in
`η_b = s_b · ‖η_b‖` (well-defined since `η_b` is real on a negation-closed `G`). -/
noncomputable def etaSign {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F) (b : F) : ℤ :=
  if 0 ≤ (ProximityGap.Frontier.PaleyCayleyEigenvalue.eta ψ G b).re then 1 else -1

/-- `etaSign` is always `±1`. -/
theorem etaSign_eq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F) (b : F) :
    etaSign ψ G b = 1 ∨ etaSign ψ G b = -1 := by
  unfold etaSign
  by_cases h : 0 ≤ (ProximityGap.Frontier.PaleyCayleyEigenvalue.eta ψ G b).re
  · left; simp [h]
  · right; simp [h]

/-- `etaSign` squares to `1` (it is a genuine sign). -/
theorem etaSign_sq {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F) (b : F) :
    etaSign ψ G b * etaSign ψ G b = 1 := by
  rcases etaSign_eq ψ G b with h | h <;> rw [h] <;> ring

/-- **The abstract obstruction.** If a `{±1}`-valued sign `s` fails multiplicativity at even a
single witness pair `(b₁, b₂)`, i.e. `s(b₁·b₂) ≠ s(b₁)·s(b₂)`, then `s` is NOT a monoid
homomorphism `M → ℤ`. (The probe gives such a witness for `etaSign` at `p=89, b₁=b₂=2`.) -/
theorem not_monoidHom_of_witness {M : Type*} [Monoid M] (s : Sign M)
    {b₁ b₂ : M} (hw : s (b₁ * b₂) ≠ s b₁ * s b₂) :
    ¬ ∃ φ : M →* ℤ, ∀ b, φ b = s b := by
  rintro ⟨φ, hφ⟩
  apply hw
  rw [← hφ, ← hφ, ← hφ, map_mul]

/-- **The relative-dilation sign is not constant (the H4 obstruction).** If `s` is multiplicative at
a dilation `ζ` (i.e. the relative sign `s(ζ·b)·s(b)` would be the constant `s(ζ)` for every `b`),
then `s` cannot also fail multiplicativity at any pair involving that constant. Formalized: a
sign with a NON-constant relative-dilation factor `b ↦ s(ζ·b)·s(b)` is not multiplicative-by-`ζ`.
We state the contrapositive cleanly: if the relative-dilation factor takes two different values at
`b` and `b'`, then there is NO constant `c` with `s(ζ·b) = c·s(b)` for all `b` (so no homomorphism
descent on the dilation tower). -/
theorem no_constant_relative_sign {M : Type*} [Monoid M] (s : Sign M) (ζ : M)
    {b b' : M} (hne : s (ζ * b) * s b ≠ s (ζ * b') * s b')
    (hb : s b * s b = 1) (hb' : s b' * s b' = 1) :
    ¬ ∃ c : ℤ, ∀ x, s (ζ * x) = c * s x := by
  rintro ⟨c, hc⟩
  apply hne
  -- s(ζb)·s(b) = c·s(b)·s(b) = c = c·s(b')·s(b') = s(ζb')·s(b')
  have e1 : s (ζ * b) * s b = c := by rw [hc]; rw [mul_assoc, hb, mul_one]
  have e2 : s (ζ * b') * s b' = c := by rw [hc]; rw [mul_assoc, hb', mul_one]
  rw [e1, e2]

/-- **Specialization to `etaSign` (rule-4 cartography).** For the real Gauss period on a
negation-closed `G`, IF `etaSign` were a monoid homomorphism on `F^*` (the structure a character
descent needs), THEN it would be multiplicative everywhere; the probe's witness `s_{b₁b₂} ≠ s_{b₁}
s_{b₂}` refutes that. We package: any concrete failure of multiplicativity rules out the
homomorphism structure for `etaSign`. -/
theorem etaSign_not_monoidHom_of_witness {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (ψ : AddChar F ℂ) (G : Finset F) {b₁ b₂ : F}
    (hw : etaSign ψ G (b₁ * b₂) ≠ etaSign ψ G b₁ * etaSign ψ G b₂) :
    ¬ ∃ φ : F →* ℤ, ∀ b, φ b = etaSign ψ G b :=
  not_monoidHom_of_witness (etaSign ψ G) hw

/-- The **relative-dilation factor** of a sign `s` at a dilation `ζ`: `r_ζ(b) = s(ζ·b)·s(b)`. This
is the `DilationRealSignCocycle` cocycle value (same-sign vs opposite-sign of the two children),
viewed as a function of `b`. The sign cocycle is a **coboundary** iff `r_ζ` is constant. -/
def relDilationSign {M : Type*} [Monoid M] (s : Sign M) (ζ : M) (b : M) : ℤ := s (ζ * b) * s b

/-- **Coboundary characterization (the precise iff for the `DilationRealSignCocycle` residual).**
For a `±1`-valued sign `s` (`s_x² = 1` everywhere), the relative-dilation factor `r_ζ` is the
CONSTANT `c` iff `s` telescopes through `ζ` by that constant: `s(ζ·x) = c·s(x)` for all `x`. The
right side is exactly the "coboundary / character-telescopable" structure a descent argument needs;
the left side is the measurable cocycle value. So the cocycle telescopes iff `r_ζ` is constant. -/
theorem relDilationSign_const_iff_coboundary {M : Type*} [Monoid M] (s : Sign M) (ζ : M) (c : ℤ)
    (hs : ∀ x, s x * s x = 1) :
    (∀ x, relDilationSign s ζ x = c) ↔ (∀ x, s (ζ * x) = c * s x) := by
  constructor
  · intro h x
    -- s(ζx) = s(ζx)·(s x·s x) = (s(ζx)·s x)·s x = r_ζ(x)·s x = c·s x
    have hx := hs x
    calc s (ζ * x) = s (ζ * x) * (s x * s x) := by rw [hx, mul_one]
      _ = relDilationSign s ζ x * s x := by unfold relDilationSign; ring
      _ = c * s x := by rw [h x]
  · intro h x
    -- r_ζ(x) = s(ζx)·s x = (c·s x)·s x = c·(s x·s x) = c
    have hx := hs x
    unfold relDilationSign
    rw [h x, mul_assoc, hx, mul_one]

/-- **The cocycle is NOT a coboundary at a non-constancy witness (rule-4, the precise wall).**
If the relative-dilation factor `r_ζ` takes two different values (`r_ζ(b) ≠ r_ζ(b')`) then for NO
constant `c` does `s` telescope through `ζ` by `c`. So a single measured non-constancy of the sign
cocycle (which the probe exhibits, H4) rules out EVERY character/coboundary descent on the tower. -/
theorem not_coboundary_of_relDilation_witness {M : Type*} [Monoid M] (s : Sign M) (ζ : M)
    (hs : ∀ x, s x * s x = 1) {b b' : M}
    (hne : relDilationSign s ζ b ≠ relDilationSign s ζ b') :
    ¬ ∃ c : ℤ, ∀ x, s (ζ * x) = c * s x := by
  rintro ⟨c, hc⟩
  have hconst : ∀ x, relDilationSign s ζ x = c :=
    (relDilationSign_const_iff_coboundary s ζ c hs).mpr hc
  exact hne ((hconst b).trans (hconst b').symm)

end ProximityGap.Frontier.EtaSignNonMultiplicative
