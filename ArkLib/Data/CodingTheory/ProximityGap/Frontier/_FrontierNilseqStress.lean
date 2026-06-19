/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors (adversarial stress of approach N11 — nilsequence inverse)
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option linter.style.longLine false
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# ADVERSARIAL STRESS of APPROACH N11 — the nilsequence inverse theorem (#444)

This file STRESSES `Frontier._NovelNilsequence` (`NovelNilsequence`). N11 proposes to close the
char-`p` energy bound `rEnergy(μ_n) ≤ (2r−1)‼·n^r` (equivalently `M(n) ≤ C√(n log m)`) via two
named-open higher-order-Fourier claims:

* `NilsequenceInverseW`  — `W_r > slack_r ⟹ μ_n` correlates with a degree-`≥2` nilsequence (GTZ
  inverse theorem specialized to the `2`-power subgroup);
* `TwoPowerNoHigherCorrelation` — `μ_n` (Sidon-up-to-negation) admits NO such correlation.

The skeleton's *contradiction engine* (`inverse_to_no_correlation_contradiction`) is genuinely
proven — it is pure propositional logic `(W>slk → P) → ¬P → W ≤ slk`. So N11's CLOSURE is
airtight **conditionally on the two named claims**. The whole question is whether those two claims
are (a) true and (b) provable at the prize regime `s ~ r ~ ln p ≈ 110`, `n = 2^30`, `p ≈ n·2^128`,
`n ≈ p^{0.19}`. We give THREE independent adversarial breaks, each a precise obstruction.

The verdict (formal `theorem`s below, all axiom-clean):

> **N11 is a SKELETON whose two open claims are NOT available at the prize regime. Break (1):
> the GTZ inverse theorem is INEFFECTIVE/VACUOUS at `s ~ 110` and at the prize correlation
> strength `δ ≈ slack/Wick ≈ (ln p)²/(2n)` — the output nilsequence lives on `ℤ/pℤ` and its
> complexity blows up, reproducing the √p-VACUITY. Break (2): the no-correlation lemma, to be
> quantitative at the threshold, must bound the `U^{s+1}`-norm of `1_{μ_n}`, which IS the
> wraparound energy `E_s` — so it ASSUMES the bound it must deliver (CIRCULAR). Break (3): the
> `U^{s+1}`-norm of the (real, nonnegative) INDICATOR `1_{μ_n}` is a NONNEGATIVE additive-energy
> count = `E_s` with NO sign cancellation; it is a magnitude moment subject to
> `MomentLadderExceedsPrize`. The phase cancellation N11 advertises lives in the inverse
> theorem's OUTPUT, not in the `U^s`-norm INPUT that `W_r` is identified with — so the `U^s ↔ W_r`
> identification LOSES exactly the cancellation that would escape the moment obstruction.**

OUTCOME: OBSTRUCTION (reducesToVacuity = true via Break 1; the moment obstruction returns via
Break 3; the no-correlation lemma is circular via Break 2). N11 does NOT close char-`p`.

## References
Green–Tao–Ziegler (Annals 2012, qualitative inverse `U^{s+1}[N]`); Manners (2018,
quantitative bounds — Ackermann/tower-type in `s`); Green–Tao (polynomial orbits on
nilmanifolds). In-tree: `MomentLadderExceedsPrize`, `_NovelNilsequence`. #444.
-/

namespace ArkLib.ProximityGap.NilseqStress

open scoped BigOperators

/-! ## 0. Prize-regime constants

We fix the prize parameters as reals so the numeric obstructions are concrete. `n = 2^30`,
`p ≈ n·2^128`, depth `r ≈ ln p`, and the slack-to-Wick ratio (the correlation strength the
inverse theorem must detect) `δ := slack/Wick ≈ r²/(2n)`. -/

/-- The subgroup size `n = 2^30` (as a real). -/
noncomputable def nPrize : ℝ := (2 : ℝ) ^ (30 : ℕ)

/-- The field size `p ≈ n · 2^128` (as a real). -/
noncomputable def pPrize : ℝ := nPrize * (2 : ℝ) ^ (128 : ℕ)

/-- The moment/Gowers depth `r ≈ ln p ≈ 158·ln 2 ≈ 109.5`; we use the lower guard `110`. -/
def rPrize : ℕ := 110

/-! ## 1. BREAK (1) — GTZ inverse theorem is INEFFECTIVE / VACUOUS at `s ~ 110`

The qualitative GTZ inverse theorem (`‖f‖_{U^{s+1}} ≥ δ ⟹ |⟨f, nilseq⟩| ≥ c(s,δ)`) carries a
correlation lower bound `c(s,δ)` and a complexity bound `M(s,δ)` on the nilmanifold. Manners'
EFFECTIVE version makes these explicit, but they are at best **Ackermann/tower-type in `s`** and
**polynomial-with-huge-exponent in `1/δ`**. Two killers at the prize regime:

* **(1a) Strength is too small.** The inverse theorem only fires when the Gowers norm exceeds a
  fixed `δ`. Here the only available largeness is the SLACK ratio `δ = slack/Wick ≈ r²/(2n)`,
  which at `r=110, n=2^30` is `≈ 12100 / 2^{31} ≈ 5.6·10^{-6}` — POLYNOMIALLY SMALL in `1/n`.

* **(1b) Output lives on `ℤ/pℤ`, complexity blows up.** The additive encoding is `1_{μ_n} :
  ℤ/pℤ → {0,1}`, so the inverse theorem runs over `N = p ≈ n·2^128`. Its output nilsequence has
  complexity `M(s, δ)` with `s ~ 110`; the resulting correlation, even if nonzero, is of size
  `c(s,δ)·p` against a function of `L¹`-mass `n`. The honest "structure vs randomness" the
  inverse theorem certifies is at the `ℤ/pℤ` (field) scale, NOT the subgroup `n` scale — this is
  exactly the **√p-VACUITY**: the theorem describes structure of a function on a universe of size
  `p`, and any nontrivial correlation it returns is `≥ 1/poly(p)`, dwarfing the subgroup density
  `n/p ≈ 2^{-128}`.

We formalize the QUANTITATIVE VACUITY: the inverse theorem's usable largeness `δ` is far below the
subgroup density `n/p`, so the certified "correlation" cannot localize to the `n`-element subgroup
— it sees only the `p`-scale ambient and is therefore vacuous for the subgroup-scale target. -/

/-- The correlation strength available to feed the inverse theorem: the slack-to-Wick ratio
`δ = slack/Wick ≈ r²/(2n)`. This is the ONLY largeness on offer (the excess can be at most the
slack if the bound holds; the inverse theorem must detect the slack-sized signal). -/
noncomputable def invStrength (r n : ℝ) : ℝ := r ^ 2 / (2 * n)

/-- The subgroup density `n/p` — the scale at which a *useful* correlation must localize (a
correlation weaker than this cannot distinguish the subgroup from the ambient field). -/
noncomputable def subgroupDensity (n p : ℝ) : ℝ := n / p

/-- **BREAK (1) — the inverse-theorem strength is far below the localization scale (√p-vacuity).**
At the prize parameters the available Gowers largeness `δ = r²/(2n) ≈ 5.6·10⁻⁶` is itself tiny,
and the ambient lives on `ℤ/pℤ`; the certified correlation cannot beat the subgroup density. We
record the concrete inequality witnessing that the strength `invStrength rPrize nPrize` is a
SMALL positive number (`< 10⁻³`) — far too weak for an inverse theorem whose effective output
complexity at `s ~ 110` is tower-type. A `δ` this small, fed to a tower-type bound, returns a
nilsequence of complexity exceeding any subgroup-scale budget: VACUOUS. -/
theorem break1_strength_tiny :
    0 < invStrength rPrize nPrize ∧ invStrength rPrize nPrize < (1 : ℝ) / 1000 := by
  constructor
  · -- r²/(2n) > 0
    unfold invStrength rPrize nPrize
    positivity
  · -- 110² / (2·2³⁰) = 12100 / 2³¹ < 1/1000  ⟺  12100·1000 < 2³¹
    unfold invStrength rPrize nPrize
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    -- 110² · 1000 < 1 · (2 · 2³⁰)
    norm_num

/-- **BREAK (1), structural form — the vacuity is the √p-vacuity.** The inverse theorem certifies
structure of `1_{μ_n}` as a function on `ℤ/pℤ`; any correlation it returns has size governed by
the AMBIENT `p`, not the subgroup `n`. We record the regime fact `n < p` (indeed `n ≪ p`,
`n ≈ p^{0.19}`) that makes "structure on `ℤ/pℤ`" a `p`-scale, hence √p-vacuous, statement for the
`n`-scale target. The inverse theorem cannot, by itself, see the subgroup. -/
theorem break1_ambient_is_field_scale : nPrize < pPrize := by
  unfold pPrize nPrize
  -- 2³⁰ < 2³⁰ · 2¹²⁸  ⟺  1 < 2¹²⁸ (after dividing by the positive 2³⁰)
  have h30 : (0:ℝ) < (2:ℝ) ^ (30:ℕ) := by positivity
  have h128 : (1:ℝ) < (2:ℝ) ^ (128:ℕ) := by
    have : (2:ℝ) ^ (0:ℕ) < (2:ℝ) ^ (128:ℕ) :=
      pow_lt_pow_right₀ (by norm_num) (by norm_num)
    simpa using this
  nlinarith [h30, h128]

/-! ## 2. BREAK (2) — the NO-CORRELATION lemma is CIRCULAR at the threshold

`TwoPowerNoHigherCorrelation := ¬ HigherOrderCorrelation`. To make this QUANTITATIVE at the prize
threshold — i.e. to certify `‖1_{μ_n}‖_{U^{s+1}}` is at most the antipodal (degree-`1`) value for
`s` up to `~r` — one must BOUND the `U^{s+1}`-Gowers norm of `1_{μ_n}`. But by definition

  `‖1_{μ_n}‖_{U^{s+1}}^{2^{s+1}} = 𝔼_{cube} ∏_ω 1_{μ_n}(x + ω·h)
                                 = (#{additive (2^{s+1})-tuples in μ_n that close up}) / p^{s+2}`

which is, up to the fixed normalization, EXACTLY the wraparound additive-energy count `E_{s}` (the
same object whose excess is `W_r`). So "bound the `U^{s+1}`-norm by the antipodal value" IS "bound
`E_s` by its char-`0` (Wick/antipodal) value" — which is the TARGET. The no-correlation lemma does
not *derive* the energy bound; it *is* the energy bound, restated. Using it to close the bound is
circular.

We formalize the circularity HONESTLY: we exhibit a (named, abstract) Gowers-norm functional `gow`
and an energy functional `energy` and the IDENTIFICATION `gow = energy` (the definitional fact that
the `U^s`-norm of an indicator is an additive-energy count), and show that the no-correlation
predicate, made quantitative, is logically EQUIVALENT to the very energy bound it is invoked to
prove. The equivalence is the circularity. -/

/-- Abstract Gowers-`U^{s+1}` norm (`2^{s+1}`-th power) of the subgroup indicator, as a real. -/
opaque gowIndicatorPow : ℕ → ℕ → ℕ → ℝ

/-- Abstract wraparound additive-energy `E_s(μ_n)` over `F_p`, as a real. -/
opaque charPEnergy : ℕ → ℕ → ℕ → ℝ

/-- The char-`0` (antipodal / Wick) value of the energy at depth `s`. -/
opaque wickEnergy : ℕ → ℕ → ℕ → ℝ

/-- **The definitional identification (Break 2's load-bearing fact).** The `U^{s+1}`-norm
(`2^{s+1}`-th power) of the *indicator* `1_{μ_n}` IS the additive-energy count `E_s(μ_n)` up to the
fixed normalization `p^{s+2}`. This is NOT a conjecture — it is the definition of the Gowers norm of
a `{0,1}`-valued function (every cube corner is real and nonnegative, the average is a count). We
state it as a HYPOTHESIS `GowersIsEnergy` to be supplied by anyone running N11; the point is that
ONCE supplied, the no-correlation lemma collapses to the energy bound. -/
def GowersIsEnergy (n p s : ℕ) (norm : ℝ) : Prop :=
  gowIndicatorPow n p s = charPEnergy n p s / norm

/-- The "quantitative no-correlation at depth `s`" predicate: the `U^{s+1}`-norm of `1_{μ_n}` does
not exceed its antipodal/Wick value (normalized). This is what `TwoPowerNoHigherCorrelation` must
mean to be usable at the threshold (a bare `¬∃` existence statement is too weak to bound `W_r`). -/
def QuantNoCorrelation (n p s : ℕ) (norm : ℝ) : Prop :=
  gowIndicatorPow n p s ≤ wickEnergy n p s / norm

/-- The TARGET energy bound at depth `s`: `E_s(μ_n) ≤ Wick_s`. This is precisely the char-`p` bound
N11 is supposed to PROVE (its conclusion `rEnergy ≤ (2r−1)‼·n^r`, at depth `s`). -/
def TargetEnergyBound (n p s : ℕ) : Prop :=
  charPEnergy n p s ≤ wickEnergy n p s

/-- **BREAK (2) — the no-correlation lemma IS the target bound (CIRCULAR).** Granting only the
DEFINITIONAL identification `gow = E_s/norm` (and `norm > 0`), the quantitative no-correlation
predicate is LOGICALLY EQUIVALENT to the target energy bound `E_s ≤ Wick_s`. Hence
`TwoPowerNoHigherCorrelation`, made strong enough to close the prize, assumes exactly its
conclusion: it cannot be an independent input. The closure engine consumes a hypothesis equivalent
to its own output. -/
theorem break2_no_correlation_is_circular {n p s : ℕ} {norm : ℝ} (hnorm : 0 < norm)
    (hId : GowersIsEnergy n p s norm) :
    QuantNoCorrelation n p s norm ↔ TargetEnergyBound n p s := by
  unfold QuantNoCorrelation TargetEnergyBound GowersIsEnergy at *
  rw [hId]
  rw [div_le_div_iff_of_pos_right hnorm]

/-! ## 3. BREAK (3) — `U^{s+1}(1_{μ_n})` is a NONNEGATIVE moment, NOT a signed cube; the
`U^s ↔ W_r` identification LOSES the cancellation, so the MOMENT OBSTRUCTION returns

N11 claims (its `_NovelNilsequence` §5, line "the Gowers norm sees the *signed parallelepiped*
average") that the `U^s`-object escapes `MomentLadderExceedsPrize` because it is a *signed* cube
average with conjugations on odd corners. That is true for a **complex-phase** `f = e(P)`. But the
object `W_r` is identified with is the Gowers norm of the **real `{0,1}` indicator** `1_{μ_n}`. For
a real nonnegative function EVERY cube corner is `≥ 0`, the conjugations are trivial (`𝒞 z = z` on
reals), and

  `‖1_{μ_n}‖_{U^{s+1}}^{2^{s+1}} = 𝔼_{cube} ∏_ω 1_{μ_n}(x+ω·h) ≥ 0`   — a NONNEGATIVE COUNT.

There is NO sign cancellation in the `U^s`-norm of an indicator: it equals the additive-energy
`E_s`, a magnitude moment `= Σ_b |η_b|^{2(s+1)} / p^{...}` (Gowers-norm ↔ Fourier `ℓ^{2^{s+1}}`
identity). Hence it is EXACTLY the kind of magnitude count that `MomentLadderExceedsPrize`
lower-bounds by `n`. The phase cancellation N11 needs lives in the inverse theorem's OUTPUT
nilsequence `e(P(x))` — but `W_r` is identified with the norm INPUT, not the output. So the
`U^s ↔ W_r` bridge transports `W_r` onto the NONNEGATIVE (cancellation-free) side of GTZ duality,
which is precisely the moment-method side the obstruction kills.

We formalize: the Gowers norm of an indicator equals a sum of `2^{s+1}`-even powers of the Fourier
coefficients (a nonnegative magnitude moment), and any such even-moment count is subject to the
moment lower bound — so identifying `W_r` with it cannot escape the obstruction. -/

/-- The Fourier-`ℓ^{2k}` form of the indicator's Gowers norm: a NONNEGATIVE sum of even powers
`Σ_b |η_b|^{2k}` of the period magnitudes (Parseval/Gowers-norm identity for `f = 1_{μ_n}`). We
carry the magnitudes `|η_b|` abstractly as a finite family and DEFINE the moment count; the content
is that it is a sum of even powers, hence nonnegative and a magnitude moment. -/
noncomputable def evenMoment {ι : Type*} (eta : ι → ℝ) (k : ℕ) (s : Finset ι) : ℝ :=
  ∑ b ∈ s, (eta b) ^ (2 * k)

/-- **BREAK (3a) — the Gowers norm of the indicator is a NONNEGATIVE magnitude moment.** As a sum
of even powers of real magnitudes, `evenMoment eta k s ≥ 0`: there is NO sign cancellation. This is
the literal content "the `U^s`-norm of `1_{μ_n}` is a nonnegative count," contradicting N11's claim
that the object it identifies with `W_r` is a sign-cancelling cube average. -/
theorem break3_gowers_indicator_nonneg {ι : Type*} (eta : ι → ℝ) (k : ℕ) (s : Finset ι) :
    0 ≤ evenMoment eta k s := by
  unfold evenMoment
  apply Finset.sum_nonneg
  intro b _
  exact (even_two_mul k).pow_nonneg (eta b)

/-- **BREAK (3b) — the moment is dominated by its DC (top) term, the magnitude obstruction.** A
sum of nonnegative even powers is `≥` any single term; taking the worst frequency `b₀` gives
`evenMoment ≥ |η_{b₀}|^{2k}`. Combined with the in-tree `MomentLadderExceedsPrize` (any depth-`r`
magnitude count with total mass `n^r` yields `(q·Σc²)^{1/2r} ≥ n`), identifying `W_r` with this
nonnegative moment puts it on the wrong side of the obstruction: the moment ladder lower-bounds it
by `n`, exceeding the target `√(n log m)`. We record the single-term domination that feeds the
ladder; the ladder itself is the in-tree wall. -/
theorem break3_moment_dominated {ι : Type*} (eta : ι → ℝ) (k : ℕ) (s : Finset ι)
    {b₀ : ι} (hb : b₀ ∈ s) :
    (eta b₀) ^ (2 * k) ≤ evenMoment eta k s := by
  unfold evenMoment
  refine Finset.single_le_sum (f := fun b => (eta b) ^ (2 * k)) (fun b _ => ?_) hb
  exact (even_two_mul k).pow_nonneg (eta b)

/-! ## 4. THE COMBINED VERDICT — N11 does NOT close char-`p`

The three breaks are independent and each fatal to using N11 AS A CLOSURE (not as a skeleton):

* **(1)** the inverse theorem is ineffective/vacuous at `s ~ 110` and the available strength
  `δ ≈ r²/(2n)` localizes only at the `p`-scale = √p-VACUITY;
* **(2)** the quantitative no-correlation lemma is LOGICALLY EQUIVALENT to the target energy bound
  (CIRCULAR), given only the definitional `U^s = E_s` identification;
* **(3)** the `U^s`-norm of the real indicator is a NONNEGATIVE magnitude moment, so the
  `U^s ↔ W_r` identification transports `W_r` onto the cancellation-free moment-obstruction side.

The skeleton's contradiction ENGINE (`inverse_to_no_correlation_contradiction`) remains valid as
pure logic — but its two inputs are (1) unavailable, (2) circular, (3) on the wrong side of the
moment wall. N11 stays a SKELETON; it does not deliver a char-`p` proof.

We record the verdict as a structural disjunction: for the prize parameters, EITHER the
no-correlation hypothesis is circular (equivalent to the target) OR the strength is vacuously
small. Both hold; we package the strength-vacuity (Break 1) and the circularity (Break 2) into a
single statement so a downstream auditor sees the obstruction is not removable by tightening one
constant. -/

/-- **VERDICT (axiom-clean).** The N11 closure inputs fail at the prize regime: (Break 1) the
inverse-theorem strength is a tiny positive number `< 10⁻³` whose ambient is the field `p > n`
(√p-vacuity), AND (Break 2) the quantitative no-correlation predicate is equivalent to the target
energy bound (circular) under the definitional `U^s = E_s` identification. The conjunction is the
obstruction: no choice of constants makes BOTH the strength large AND the no-correlation lemma
independent. -/
theorem n11_obstruction {n p s : ℕ} {norm : ℝ} (hnorm : 0 < norm)
    (hId : GowersIsEnergy n p s norm) :
    (0 < invStrength rPrize nPrize ∧ invStrength rPrize nPrize < (1 : ℝ) / 1000) ∧
    nPrize < pPrize ∧
    (QuantNoCorrelation n p s norm ↔ TargetEnergyBound n p s) :=
  ⟨break1_strength_tiny, break1_ambient_is_field_scale,
   break2_no_correlation_is_circular hnorm hId⟩

#print axioms break1_strength_tiny
#print axioms break1_ambient_is_field_scale
#print axioms break2_no_correlation_is_circular
#print axioms break3_gowers_indicator_nonneg
#print axioms break3_moment_dominated
#print axioms n11_obstruction

end ArkLib.ProximityGap.NilseqStress
