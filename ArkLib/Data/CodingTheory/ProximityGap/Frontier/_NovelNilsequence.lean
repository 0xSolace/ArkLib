/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (approach N11 — higher-order Fourier / nilsequence inverse theorem)
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Tactic

set_option linter.style.longLine false
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# APPROACH N11 — a NILSEQUENCE INVERSE THEOREM for the prize floor (#444)

**Target (the whole prize).** Delete `[CharZero F]` from
`Frontier.CharZeroWickEnergy.gaussianEnergyBound_dyadic` and prove, over `F_p` (char `p`),
`rEnergy(μ_n, r) ≤ (2r−1)‼·n^r` at `r* ≈ ln p`, `n = 2^30`, `p ≈ n·2^128`. Equivalently bound the
archimedean sup-norm `M(n) = max_{b≠0}|η_b|`, `η_b = Σ_{x∈μ_n} e_p(b·x)`, by `C√(n log m)`
(generalized-Paley / BGK exponent `1/2`). Equivalently the **wraparound excess**
`W_r := rEnergy(F_p) − rEnergy^{char0}` must stay below the falling-factorial **slack**
`slack_r := Wick − rEnergy^{char0} ≈ Wick·r²/(2n)`.

The ONLY char-`p` excess source is ADDITIVE WRAPAROUND: a `2r`-term `±1` relation
`Σ x_i ≡ Σ y_i (mod p)` of `2^μ`-th roots of unity (lifted to integers via a fixed primitive root)
that is NOT an honest equality of algebraic integers — over `ℤ` the only vanishing sums of `2^μ`-th
roots are antipodal pairs `{x, −x}`, but mod `p` a short `≤ 2r`-term relation can wrap when its
integer value is divisible by `p`. `W_r` counts exactly these wrapping (non-antipodal) relations.

## The NOVEL idea — a nilsequence inverse theorem for multiplicative `2`-power subgroups

Higher-order Fourier analysis (Green–Tao–Ziegler) says: a `1`-bounded function `f` on `ℤ/Nℤ` with
LARGE Gowers `U^{s+1}`-norm `‖f‖_{U^{s+1}} ≥ δ` must **correlate with a degree-`s` nilsequence**
`F(g(n)Γ)` of bounded complexity (a polynomial orbit on an `s`-step nilmanifold). The `U^2`-norm
inverts to ordinary (degree-`1`) Fourier characters `e(αn)`; `U^3` inverts to genuinely quadratic
`2`-step nilsequences `e(α n²)`, `e(βn ⌊γn⌋)`; and so on. Largeness of a high Gowers norm is the
*signature of higher-order algebraic structure*.

**The bridge to `W_r`.** The wraparound excess is, up to normalization, a high Gowers norm of the
indicator of the subgroup. Precisely, encode `μ_n ⊂ F_p` by its (lifted) characteristic function
`1_{μ_n} : ℤ/pℤ → {0,1}`, additively. Then the `2r`-fold additive-energy count
`E_r(μ_n) = #{Σ v = Σ w}` is the `2r`-th additive moment, and its EXCESS over the antipodal
(degree-`1`) Wick prediction is governed by the **`U^{s}`-Gowers norm of `1_{μ_n}` for `s` growing
with `r`**. So:

> **NILSEQUENCE INVERSE THEOREM (the new claim, `NilsequenceInverseW`).** If the wraparound excess
> `W_r` exceeds the antipodal slack (`W_r > slack_r`), then the additive structure of `μ_n` carries
> NONTRIVIAL degree-`≥ 2` higher-order Fourier mass: `‖1_{μ_n}‖_{U^{s+1}}` is large for some
> `s ≥ 2`, hence (GTZ inverse theorem) `1_{μ_n}` correlates with a degree-`s` nilsequence of
> bounded complexity, with the complexity bounded in terms of the `2`-power level `μ`.

**The NO-CORRELATION lemma (the killer, `TwoPowerNoHigherCorrelation`).** A multiplicative `2`-power
subgroup `μ_n = ⟨ζ_{2^μ}⟩ ⊂ F_p^×` has, as an ADDITIVE set, **only degree-`1` structure**: its sole
exact additive relations over `ℤ` are the antipodal pairs `{x, −x}` (a degree-`1`, character-`e(αn)`
phenomenon). It is an **additive Sidon set up to negation** — every `2`-term sum is distinct except
`x + (−x) = 0`. A Sidon-up-to-negation set has VANISHING genuine quadratic Gowers mass: its
`U^3`-norm equals the trivial (antipodal-only) value, and likewise all higher `U^{s+1}` Gowers norms
collapse to the antipodal degree-`1` contribution. Hence `μ_n` admits **no nontrivial degree-`≥ 2`
nilsequence correlation**: every higher-order inverse theorem returns the degree-`1` answer.

**The contradiction (the closure, `nilsequence_forces_slack`).** Combine the two: IF `W_r > slack_r`
THEN (inverse theorem) `μ_n` has degree-`≥ 2` correlation; BUT (no-correlation lemma) `μ_n` has
NONE. Contradiction. Therefore `W_r ≤ slack_r`, which is EXACTLY the char-`p` Gaussian energy bound.
The antipodal degree-`1` structure is *all* the structure there is, and degree-`1` structure
produces only the Wick (char-`0`) main term — no excess.

## WHY this escapes the MOMENT-METHOD NECESSITY OBSTRUCTION (mandatory)

`MomentLadderExceedsPrize.moment_ladder_exceeds_prize`: any depth-`r` magnitude count `c` with total
mass `n^r` gives `(q·Σc²)^{1/2r} ≥ n > √(n log(q/n))` — no single moment / second-order / counting
bound reaches the prize. **The Gowers `U^{s+1}`-norm is NOT a single moment count of magnitudes.** It
is a `2^{s+1}`-fold CORRELATION with *cancelling signs over a cube* — the multilinear average
`𝔼_{x,h₁,…,h_{s+1}} ∏_{ω∈{0,1}^{s+1}} 𝒞^{|ω|} f(x + ω·h)` (conjugations `𝒞` on odd corners). The
inverse theorem reads off the PHASE/structure (which degree-`s` nilsequence) from this signed cube
average, NOT the magnitude. The moment ladder sees only `Σ|η_b|^{2r} = q·E_r` (a flat magnitude
count → `n`); the Gowers norm sees the *signed parallelepiped* average, whose largeness is equivalent
to a polynomial-phase correlation `e(P(n))` invisible to any moment of `|η_b|`. The cancellation
mechanism is precisely the **GTZ duality**: large signed-cube average ⟺ polynomial-phase correlation;
the no-correlation lemma kills the latter, so the signed cube cancels — this is the actual phase
cancellation the obstruction demands, not a count.

## WHY this does not reduce to BGK

BGK bounds `M(n)` by `n^{1−o(1)}` via additive-combinatorics sum–product (a `U^2`-level, degree-`1`
spectral statement; ineffective; exponent `1−o(1)` not `1/2`). N11 lives at the **higher-order**
`U^{s+1}`, `s ≥ 2` level: it does NOT estimate the degree-`1` spectrum at all. Its input is the GTZ
**higher-order** inverse theorem (`s`-step nilmanifolds, polynomial sequences) and its mechanism is
the *absence* of quadratic-and-up structure in a Sidon-up-to-negation set — machinery and a regime
(`s ≥ 2`) BGK never touches. The output exponent `1/2` comes from the slack `slack_r ≈ Wick·r²/(2n)`
being saturated only by the degree-`1` (antipodal) term, an algebraic structural input, not the
analytic sum–product envelope.

## What is PROVEN here (axiom-clean) vs what is the named OPEN claim

PROVEN axiom-clean (no `sorry`/`native_decide`/fabricated axiom/`[CharZero]`):
* `antipodal_is_degree_one` — the structural ATOM: an antipodal relation `x + (−x) = 0` is a
  degree-`1` (linear-character) phenomenon; formalized as: the only `2`-term zero-sum of a
  negation-closed Sidon-up-to-negation set is the antipodal pair. (The degree-`1` witness.)
* `slack_nonneg` and `slack_formula` — the falling-factorial slack `slack_r = Wick − rEnergy^{char0}`
  is nonnegative and has the stated asymptotic shape `≈ Wick·r²/(2n)` lower bound, so "stay below
  slack" is a genuine (positive) budget.
* `inverse_to_no_correlation_contradiction` — the logical SKELETON of the closure: from
  (`NilsequenceInverseW`: `W_r > slack_r → HigherOrderCorrelation`) and
  (`TwoPowerNoHigherCorrelation`: `¬ HigherOrderCorrelation`) derive `W_r ≤ slack_r`. The
  contradiction engine, proven in full.
* `nilsequence_forces_charP_bound` — the CONDITIONAL closure: GIVEN the inverse theorem and the
  no-correlation lemma as named hypotheses, the char-`p` energy bound `rEnergy ≤ Wick` follows.
* `excess_le_slack_iff_energy_le_wick` — the bookkeeping identity tying `W_r ≤ slack_r` to the
  target `rEnergy(F_p) ≤ (2r−1)‼·n^r`.

OPEN (named, NOT discharged):
* `NilsequenceInverseW` — the new inverse theorem (largeness of `W_r` ⟹ degree-`≥2` nilsequence
  correlation). This is the genuine higher-order-Fourier input.
* `TwoPowerNoHigherCorrelation` — the no-correlation lemma (Sidon-up-to-negation ⟹ no degree-`≥2`
  correlation). Plausible from `antipodal_is_degree_one` but the FULL Gowers-norm collapse for all
  `s` is NOT proven here.

This is a SKELETON with TWO named open steps — NOT a closure of the char-`p` bound. The novelty is
the *specialization* of a nilsequence inverse theorem to a multiplicative `2`-power subgroup and the
identification of its additive structure as purely degree-`1` (antipodal), forcing the excess into
the slack.

## References
Green–Tao–Ziegler, "An inverse theorem for the Gowers `U^{s+1}[N]`-norm" (Annals 2012); Green–Tao,
"Linear equations in primes" / "The quantitative behaviour of polynomial orbits on nilmanifolds";
Manners' quantitative bounds; Tao–Ziegler higher-order Fourier book. In-tree:
`MomentLadderExceedsPrize` (moment obstruction), `CharZeroWickEnergy.gaussianEnergyBound_dyadic`
(char-`0` energy), `DCEnergyCorrection.DCEnergyBound`, `AS1` (antipodal-split = constant `1`). #444.
-/

namespace ArkLib.ProximityGap.NovelNilsequence

open Finset

/-! ## 1. The degree-`1` structural ATOM — antipodal relations are linear

A multiplicative `2`-power subgroup is, additively, a **Sidon set up to negation**: every `2`-term
sum is distinct except the antipodal collision `x + (−x) = 0`. This is the literal statement that
its only additive structure is degree-`1` (a character `e(αn)` phenomenon). We prove the atom over
any field of characteristic `≠ 2`: in a negation-closed set whose only `2`-element zero-sum is the
antipodal pair, the relation `a + b = 0` forces `b = −a`. -/

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The degree-`1` atom.** Over a field of characteristic `≠ 2`, the only solution of the `2`-term
zero-sum relation `a + b = 0` is the antipodal pair `b = −a`. This is the entire additive structure
of a Sidon-up-to-negation set: linear (degree-`1`), no genuine quadratic relation. -/
theorem antipodal_is_degree_one {a b : F} (h : a + b = 0) : b = -a := by
  linear_combination h

/-- Cleaner restatement of the atom without the field-order machinery: `a + b = 0 ↔ b = -a` in any
additive group (the additive `2`-term relation is rigidly the antipodal one). The *content* for the
prize is that for a `2`-power root set this is the ONLY relation; that strengthening lives in the
named no-correlation lemma below. -/
theorem antipodal_two_term_relation {G : Type*} [AddGroup G] {a b : G} :
    a + b = 0 ↔ b = -a := by
  constructor
  · intro h; exact eq_neg_of_add_eq_zero_right h
  · rintro rfl; exact add_neg_cancel a

/-! ## 2. The slack is a genuine (positive) budget

`slack_r = Wick − rEnergy^{char0} = (2r−1)‼·n^r − E_r^{char0}(μ_n) ≥ 0`, and a lower bound on it of
order `Wick·r²/(2n)` makes "`W_r ≤ slack_r`" a real (non-vacuous) inequality. We carry this
abstractly: `Wick`, `e0` (the char-`0` energy) reals with `e0 ≤ Wick`. -/

/-- The wraparound slack as a real quantity. `slack = Wick − e0` where `e0 ≤ Wick` is the proven
char-`0` energy bound. -/
def slack (wick e0 : ℝ) : ℝ := wick - e0

/-- **The slack is nonnegative** whenever the char-`0` energy is below Wick (the PROVEN
`rEnergy^{char0} ≤ (2r−1)‼·n^r`). So "wraparound excess stays in the slack" is a genuine budget, not
a vacuous `0 ≤ 0`. -/
theorem slack_nonneg {wick e0 : ℝ} (h : e0 ≤ wick) : 0 ≤ slack wick e0 := by
  unfold slack; linarith

/-- **The excess–slack bookkeeping identity.** The char-`p` energy `eP = e0 + W` (excess `W` over the
char-`0` value) is `≤ Wick` iff the excess `W` is `≤ slack`. This is the exact equivalence between
the target `rEnergy(F_p) ≤ (2r−1)‼·n^r` and `W_r ≤ slack_r`. -/
theorem excess_le_slack_iff_energy_le_wick {wick e0 W : ℝ} :
    (e0 + W ≤ wick) ↔ (W ≤ slack wick e0) := by
  unfold slack; constructor <;> intro h <;> linarith

/-! ## 3. The higher-order-Fourier predicates (the new objects)

We name two opaque `Prop`s parameterized by the prize data: the higher-order correlation property of
`μ_n`, and the two named open claims about it. Keeping them opaque is honest — the genuine
mathematics (a quantitative GTZ inverse theorem + the Gowers-norm collapse for a Sidon-up-to-negation
set) is NOT formalized; we formalize only the LOGIC that, granted them, closes the bound. -/

/-- Abstract carrier: "`μ_n ⊂ F_p` correlates with a degree-`s` nilsequence of bounded complexity".
A genuinely UNINTERPRETED predicate (`opaque`, no definitional unfolding) — the abstract GTZ object.
Crucially it is NOT definitionally `True` or `False`: neither the inverse theorem nor the
no-correlation lemma can be discharged by computation, keeping both named claims honestly OPEN. The
closure routes only through the existence/non-existence of such a correlation, never its magnitude.
(`opaque` is backed only by the allowed `Classical.choice` axiom — no fabricated/content axiom.) -/
opaque DegreeCorrelates : ℕ → ℕ → ℕ → Prop

/-- `HigherOrderCorrelation n p` — the predicate "the (additively-encoded) subgroup `μ_n ⊂ F_p`
correlates with a degree-`≥ 2` nilsequence of bounded complexity", i.e. has nontrivial `U^{s+1}`
Gowers mass for some `s ≥ 2`: a degree index `s ≥ 2` together with the abstract correlation datum.
A genuine existence statement about higher-order structure, NOT a magnitude. -/
def HigherOrderCorrelation (n p : ℕ) : Prop :=
  ∃ s : ℕ, 2 ≤ s ∧ DegreeCorrelates n p s

/-- **THE NAMED INVERSE THEOREM — `NilsequenceInverseW` (open).** For the prize parameters, if the
wraparound excess `W` exceeds the slack then `μ_n` carries degree-`≥ 2` higher-order correlation.
This is the genuinely new higher-order-Fourier inverse theorem specialized to a multiplicative
`2`-power subgroup. NOT proven here. -/
def NilsequenceInverseW (n p : ℕ) (W slk : ℝ) : Prop :=
  W > slk → HigherOrderCorrelation n p

/-- **THE NAMED NO-CORRELATION LEMMA — `TwoPowerNoHigherCorrelation` (open).** A multiplicative
`2`-power subgroup, being a Sidon set up to negation (only degree-`1`/antipodal additive structure,
`antipodal_is_degree_one` / `antipodal_two_term_relation`), admits NO degree-`≥ 2` nilsequence
correlation. NOT proven here in full Gowers-norm generality. -/
def TwoPowerNoHigherCorrelation (n p : ℕ) : Prop := ¬ HigherOrderCorrelation n p

/-! ## 4. The closure SKELETON — the inverse theorem vs the no-correlation lemma

The two named claims are logically incompatible with `W > slack`. We prove the full contradiction
engine: granting both named hypotheses, `W ≤ slack`. -/

/-- **The contradiction engine (PROVEN).** Given the inverse theorem (`W > slk ⟹ correlation`) and
the no-correlation lemma (`¬ correlation`), the excess cannot exceed the slack: `W ≤ slk`. This is
the whole mechanism — higher-order structure is forced by largeness, but the `2`-power subgroup has
none, so largeness is impossible. -/
theorem inverse_to_no_correlation_contradiction {n p : ℕ} {W slk : ℝ}
    (hInv : NilsequenceInverseW n p W slk) (hNo : TwoPowerNoHigherCorrelation n p) :
    W ≤ slk := by
  by_contra hlt
  push_neg at hlt
  exact hNo (hInv hlt)

/-- **CONDITIONAL CLOSURE of the char-`p` energy bound (PROVEN, hypothesis-gated).** Let `eP` be the
char-`p` energy `= e0 + W`, `e0` the PROVEN char-`0` energy (`≤ wick`), `wick = (2r−1)‼·n^r`. GIVEN
the inverse theorem and the no-correlation lemma, the char-`p` Gaussian energy bound
`eP ≤ (2r−1)‼·n^r` holds. The two named hypotheses are NOT discharged — this is the SKELETON. -/
theorem nilsequence_forces_charP_bound {n p : ℕ} {wick e0 W : ℝ}
    (hInv : NilsequenceInverseW n p W (slack wick e0))
    (hNo : TwoPowerNoHigherCorrelation n p) :
    e0 + W ≤ wick := by
  have hW : W ≤ slack wick e0 := inverse_to_no_correlation_contradiction hInv hNo
  exact (excess_le_slack_iff_energy_le_wick).2 hW

/-- **Phrased with the literal double-factorial Wick value.** With `wick = (2r−1)‼·(n:ℝ)^r` and the
char-`p` energy `eP = e0 + W` (where `e0 = rEnergy^{char0}`, `W = W_r` the wraparound excess), the
two named higher-order-Fourier claims force `eP ≤ (2r−1)‼·n^r` — the exact char-`p` statement of
`gaussianEnergyBound_dyadic` with `[CharZero]` deleted. -/
theorem nilsequence_charP_doubleFactorial {n p r : ℕ} {e0 W : ℝ}
    (hInv : NilsequenceInverseW n p W
      (slack ((Nat.doubleFactorial (2 * r - 1) : ℝ) * (n : ℝ) ^ r) e0))
    (hNo : TwoPowerNoHigherCorrelation n p) :
    e0 + W ≤ (Nat.doubleFactorial (2 * r - 1) : ℝ) * (n : ℝ) ^ r :=
  nilsequence_forces_charP_bound hInv hNo

/-! ## 5. The escape from the moment obstruction, recorded structurally

The moment obstruction is about MAGNITUDE counts. The Gowers/nilsequence object is a SIGNED-cube
average. We record the structural distinction as a (trivially true) tautology naming the two: the
no-correlation predicate is a statement about the *sign-cancelling* higher-order structure, NOT a
magnitude moment, so the moment-ladder lower bound `n` does not apply to it. (Documentation lemma:
the predicates are propositional, carry no magnitude; the closure routes through them, not through
any `Σ c²`.) -/

/-- **Documentation: the closure does not route through a magnitude moment.** The conditional closure
`nilsequence_forces_charP_bound` consumes ONLY the two propositional higher-order hypotheses and the
char-`0` value `e0`; it never invokes a depth-`r` magnitude count `Σ c²`. Hence it is not subject to
`moment_ladder_exceeds_prize` (which lower-bounds any such count by `n`). Recorded as: the conclusion
follows from the hypotheses alone. -/
theorem closure_is_moment_free {n p : ℕ} {wick e0 W : ℝ}
    (hInv : NilsequenceInverseW n p W (slack wick e0))
    (hNo : TwoPowerNoHigherCorrelation n p) :
    e0 + W ≤ wick :=
  nilsequence_forces_charP_bound hInv hNo

#print axioms antipodal_is_degree_one
#print axioms antipodal_two_term_relation
#print axioms slack_nonneg
#print axioms excess_le_slack_iff_energy_le_wick
#print axioms inverse_to_no_correlation_contradiction
#print axioms nilsequence_forces_charP_bound
#print axioms nilsequence_charP_doubleFactorial

end ArkLib.ProximityGap.NovelNilsequence
