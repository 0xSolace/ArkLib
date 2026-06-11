/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
<<<<<<< HEAD
import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic

/-!
# Fold transport of the KKH26 bad line (#357 R2): the trichotomy

The KKH26 near-capacity bad family for smooth-domain RS codes
(`KKH26BadLineConstruction.lean`) is the monomial stack `(u₀, u₁) = (X^{rm}, X^{(r−1)m})` on
`H = ⟨g⟩`, `|H| = s·m`, `s = 2^μ`, with bad scalars `λ_S = −∑_{a∈S} a` over `r`-subsets `S` of
the inner group `G = ⟨g^m⟩`. The FRI fold maps words on `H` to words on `H² = ⟨g²⟩` via
`f ↦ f_e + β·f_o` (even/odd split, folding challenge `β`). **R2 of the #357 campaign asked
whether the family is fold-covariant.** The answer, probe-verified at p = 97 and proven here,
is a sharp trichotomy:

1. **`m` even (m-tower steps): exact covariance, `β`-free.**
   `fold_β(X^{rm}) = Y^{r(m/2)}` and `fold_β(X^{(r−1)m}) = Y^{(r−1)(m/2)}`
   (`kkh26_fold_m_even`) — the folded stack *is* the KKH26 stack at `(s, m/2, r)`; and the
   inner group is *literally unchanged*: `(g²)^{m/2} = g^m` (`sq_pow_half`), so the
   bad-scalar census is the same set of field elements. The fold does **not** shrink the
   census along m-steps; the census-extremality direction survives (the mutually-falsifying
   pairing of the campaign dossier).

2. **`m = 1`, `r` even (s-steps): structural halving.**
   `fold_β(X^r, X^{r−1}) = (Z^{r/2}, β·Z^{r/2−1})` (`kkh26_fold_s_step_r_even`) — a β-scaled
   KKH26 stack at `(s/2, 1, r/2)` (the scaling is census-neutral by
   `MCAEquivariance.prob_mcaEvent_smul_right`). The construction-class supply drops
   `2^r·C(s/2,r) → 2^{r/2}·C(s/4,r/2)` per s-step.

3. **`m = 1`, `r` odd (s-steps): total collapse.**
   Both rows fold to multiples of *one* monomial, and the whole folded line is the pencil
   `(β + λ)·Z^{(r−1)/2}` (`kkh26_fold_line_collapse`): the census collapses to a single
   scalar (probe: 40 → 1 at every β).

**Consequence.** The KKH26 ceiling is μ-uniform along the m-half of the smooth tower with an
*identical* census, and the entire decay of this construction class concentrates at the
s-steps (exact halving for even `r`, instant death for odd `r`). Any fold-based protocol
argument crossing one s-step strictly escapes the KKH26 construction class.

The fold is formalized pointwise: `foldAt f β x` is the value of the folded word at `y = x²`,
defined for `x ≠ 0` over any field of characteristic `≠ 2` (both hypotheses explicit).

Everything is axiom-clean (`propext`, `Classical.choice`, `Quot.sound`); no `sorry`.

## References

- [KKH26] ePrint 2026/782 (the bad-line construction; `KKH26BadLineConstruction.lean`).
- Issue #357 (R2 in the campaign dossier); probe `p = 97` data in the R2 verdict comment.
-/

set_option linter.unusedSectionVars false

namespace ProximityGap.KKH26FoldTransport

variable {F : Type*} [Field F]

/-- The FRI fold of a word `f`, evaluated at the point lying over `y = x²`: the even part
plus `β` times the odd part, `f_e(x²) + β·f_o(x²)`. -/
noncomputable def foldAt (f : F → F) (β x : F) : F :=
  (f x + f (-x)) / 2 + β * ((f x - f (-x)) / (2 * x))

/-- The fold is additive in the word. -/
theorem foldAt_add (f g : F → F) (β x : F) :
    foldAt (fun t => f t + g t) β x = foldAt f β x + foldAt g β x := by
  unfold foldAt
  ring

/-- The fold is homogeneous in the word. -/
theorem foldAt_smul (c : F) (f : F → F) (β x : F) :
    foldAt (fun t => c * f t) β x = c * foldAt f β x := by
  unfold foldAt
  ring

/-- **Even monomials fold β-freely:** `fold_β(X^d) = Y^{d/2}` at `y = x²` for `2 ∣ d`. -/
theorem foldAt_monomial_even {d : ℕ} (hd : 2 ∣ d) (h2 : (2 : F) ≠ 0) (β : F) {x : F}
    (hx : x ≠ 0) : foldAt (fun t => t ^ d) β x = (x ^ 2) ^ (d / 2) := by
  obtain ⟨e, rfl⟩ := hd
  have hneg : (-x) ^ (2 * e) = (x ^ 2) ^ e := by
    rw [pow_mul, neg_sq]
  have hpos : x ^ (2 * e) = (x ^ 2) ^ e := by
    rw [pow_mul]
  have hdiv : 2 * e / 2 = e := Nat.mul_div_cancel_left e (by norm_num)
  simp only [foldAt]
  rw [hneg, hpos, hdiv]
  field_simp
  ring

/-- **Odd monomials fold to β times the half monomial:** `fold_β(X^d) = β·Y^{d/2}` at
`y = x²` for odd `d` (`d/2 = (d−1)/2` in ℕ). -/
theorem foldAt_monomial_odd {d : ℕ} (hd : ¬ 2 ∣ d) (h2 : (2 : F) ≠ 0) (β : F) {x : F}
    (hx : x ≠ 0) : foldAt (fun t => t ^ d) β x = β * (x ^ 2) ^ (d / 2) := by
  obtain ⟨e, rfl⟩ : ∃ e, d = 2 * e + 1 := ⟨d / 2, by omega⟩
  have hneg : (-x) ^ (2 * e + 1) = -((x ^ 2) ^ e * x) := by
    rw [pow_succ, pow_mul, neg_sq, neg_mul_eq_mul_neg]
  have hpos : x ^ (2 * e + 1) = (x ^ 2) ^ e * x := by
    rw [pow_succ, pow_mul]
  have hdiv : (2 * e + 1) / 2 = e := by omega
  simp only [foldAt]
  rw [hneg, hpos, hdiv]
  field_simp
  ring

/-! ## Regime 1 — `m` even: exact covariance, identical census -/

/-- **The m-step covariance (word level).** For even `m`, the KKH26 stack folds, at every
challenge `β`, to *exactly* the KKH26 stack of the next tower level `(s, m/2, r)`:
`fold_β(X^{rm}) = Y^{r·(m/2)}` and `fold_β(X^{(r−1)m}) = Y^{(r−1)·(m/2)}`. -/
theorem kkh26_fold_m_even {r m : ℕ} (hm : 2 ∣ m) (h2 : (2 : F) ≠ 0) (β : F) {x : F}
    (hx : x ≠ 0) :
    foldAt (fun t => t ^ (r * m)) β x = (x ^ 2) ^ (r * (m / 2)) ∧
      foldAt (fun t => t ^ ((r - 1) * m)) β x = (x ^ 2) ^ ((r - 1) * (m / 2)) := by
  obtain ⟨e, rfl⟩ := hm
  constructor
  · rw [foldAt_monomial_even ⟨r * e, by ring⟩ h2 β hx]
    congr 1
    rw [show r * (2 * e) = 2 * (r * e) by ring,
      Nat.mul_div_cancel_left (r * e) (by norm_num : 0 < 2),
      Nat.mul_div_cancel_left e (by norm_num : 0 < 2)]
  · rw [foldAt_monomial_even ⟨(r - 1) * e, by ring⟩ h2 β hx]
    congr 1
    rw [show (r - 1) * (2 * e) = 2 * ((r - 1) * e) by ring,
      Nat.mul_div_cancel_left ((r - 1) * e) (by norm_num : 0 < 2),
      Nat.mul_div_cancel_left e (by norm_num : 0 < 2)]

/-- **The m-step census invariance (group level).** The inner group generator is literally
unchanged by the fold: `(g²)^{m/2} = g^m` for even `m`. Hence `G = ⟨g^m⟩` — and with it the
entire KKH26 bad-scalar supply `{−∑_{a∈S} a : S ⊆ G, |S| = r}` — is the *same set of field
elements* at the folded level `(⟨g²⟩, m/2)` as at `(⟨g⟩, m)`. -/
theorem sq_pow_half {M : Type*} [Monoid M] (g : M) {m : ℕ} (hm : 2 ∣ m) :
    (g ^ 2) ^ (m / 2) = g ^ m := by
  rw [← pow_mul, Nat.mul_div_cancel' hm]

/-- The census-supply transport, in the explicit `Finset` form used by
`kkh26_badline_closePoints`: the inner-group enumeration at the folded level coincides
verbatim. -/
theorem kkh26_inner_group_fold_invariant [DecidableEq F] {s m : ℕ} (g : F) (hm : 2 ∣ m) :
    (Finset.range s).image (fun i => ((g ^ 2) ^ (m / 2)) ^ i)
      = (Finset.range s).image (fun i => (g ^ m) ^ i) := by
  rw [sq_pow_half g hm]

/-! ## Regime 2 — `m = 1`, `r` even: structural halving -/

/-- **The s-step halving (word level).** At the bottom of the m-tower (`m = 1`) with even
`r`, the KKH26 stack folds to the **β-scaled** KKH26 stack of `(s/2, 1, r/2)`:
`fold_β(X^r) = Z^{r/2}` and `fold_β(X^{r−1}) = β·Z^{r/2−1}`. (The β-scaling of the direction
row is census-neutral by `MCAEquivariance.prob_mcaEvent_smul_right`.) -/
theorem kkh26_fold_s_step_r_even {r : ℕ} (hr : 2 ∣ r) (hr2 : 2 ≤ r) (h2 : (2 : F) ≠ 0)
    (β : F) {x : F} (hx : x ≠ 0) :
    foldAt (fun t => t ^ r) β x = (x ^ 2) ^ (r / 2) ∧
      foldAt (fun t => t ^ (r - 1)) β x = β * (x ^ 2) ^ (r / 2 - 1) := by
  constructor
  · exact foldAt_monomial_even hr h2 β hx
  · rw [foldAt_monomial_odd (by omega) h2 β hx]
    congr 2
    omega

/-! ## Regime 3 — `m = 1`, `r` odd: total collapse -/

/-- **The s-step collapse (word level).** At `m = 1` with odd `r`, both rows fold to
multiples of the *same* monomial: `fold_β(X^r) = β·Z^{(r−1)/2}` and
`fold_β(X^{r−1}) = Z^{(r−1)/2}`. -/
theorem kkh26_fold_s_step_r_odd {r : ℕ} (hr : ¬ 2 ∣ r) (hr1 : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    (β : F) {x : F} (hx : x ≠ 0) :
    foldAt (fun t => t ^ r) β x = β * (x ^ 2) ^ (r / 2) ∧
      foldAt (fun t => t ^ (r - 1)) β x = (x ^ 2) ^ (r / 2) := by
  constructor
  · exact foldAt_monomial_odd hr h2 β hx
  · rw [foldAt_monomial_even (by omega) h2 β hx]
    congr 1
    omega

/-- **The pencil collapse.** At `m = 1`, odd `r`, the *entire folded KKH26 line* degenerates
to the one-monomial pencil: `fold_β(X^r + λ·X^{r−1}) = (β + λ)·Z^{(r−1)/2}` — so at most one
folded line point (namely `λ = −β`, the zero word) can be better than the single monomial
allows, and the bad-scalar census collapses (probe: 40 → 1 at every β). -/
theorem kkh26_fold_line_collapse {r : ℕ} (hr : ¬ 2 ∣ r) (hr1 : 1 ≤ r) (h2 : (2 : F) ≠ 0)
    (β lam : F) {x : F} (hx : x ≠ 0) :
    foldAt (fun t => t ^ r + lam * t ^ (r - 1)) β x = (β + lam) * (x ^ 2) ^ (r / 2) := by
  rw [foldAt_add (fun t => t ^ r) (fun t => lam * t ^ (r - 1)) β x,
    foldAt_smul lam (fun t => t ^ (r - 1)) β x,
    (kkh26_fold_s_step_r_odd hr hr1 h2 β hx).1,
    (kkh26_fold_s_step_r_odd hr hr1 h2 β hx).2]
  ring

/-- The fold of the full KKH26 line commutes with the line structure: folding
`u₀ + λ·u₁` equals `fold(u₀) + λ·fold(u₁)` — the bad-scalar parameter survives the fold
untouched in *every* regime (linearity; the regime trichotomy then identifies the shape). -/
theorem foldAt_line (u₀ u₁ : F → F) (lam β x : F) :
    foldAt (fun t => u₀ t + lam * u₁ t) β x = foldAt u₀ β x + lam * foldAt u₁ β x := by
  rw [foldAt_add u₀ (fun t => lam * u₁ t) β x, foldAt_smul lam u₁ β x]

/-! ## Source audit -/

#print axioms foldAt_add
#print axioms foldAt_smul
#print axioms foldAt_monomial_even
#print axioms foldAt_monomial_odd
#print axioms kkh26_fold_m_even
#print axioms sq_pow_half
#print axioms kkh26_inner_group_fold_invariant
#print axioms kkh26_fold_s_step_r_even
#print axioms kkh26_fold_s_step_r_odd
#print axioms kkh26_fold_line_collapse
#print axioms foldAt_line

end ProximityGap.KKH26FoldTransport
=======
import Mathlib.FieldTheory.Finite.Basic

/-!
# Fold transport of the KKH26 bad line (#357, hypothesis R2 — verdicts formalized)

Probe `probe_kkh26_fold_transport.py` (commit `65901c199`) found that the KKH26
ceiling construction is a **fold fixed point**, and that the terminal fold has a
unique kill-challenge.  This file is the Lean side of both verdicts, as pure field
algebra (no code/probability machinery needed — the geometric content is pointwise).

The FRI fold at challenge `β` evaluates, at `y = x²`,

    Fold_β(f)(x²) = (f(x) + f(−x))/2 + β · (f(x) − f(−x))/(2x).

The KKH26 stack at parameters `(r, m, w)` is `u₀ = x^{rm}/(x^m − w)`,
`u₁ = 1/(x^m − w)`.

**Fixed-point half (even `m`, refuting K1's strict-shrink).**  For even `m` both
components are *fiber-even* (`f(−x) = f(x)`), so the fold is β-independent and equals
the value itself — which is literally the `(r, m/2, w)` instance evaluated at `x²`:

  * `foldAt_of_even` — fiber-even functions fold to themselves, every `β`;
  * `kkhU0_neg`/`kkhU1_neg` — the stack is fiber-even for even `m` (no hypotheses);
  * `foldAt_kkhU0_even`/`foldAt_kkhU1_even` — `Fold_β(u₀^{(r,2m')})(x) = u₀^{(r,m')}(x²)`,
    same `w`, every `β`.  The ceiling construction transports down the smooth tower
    *unchanged*: it neither improves (K1 refuted) nor degrades.

**Terminal half (`m = 1`, the kill-challenge).**  At `m = 1` fiber-evenness fails and
the fold genuinely depends on `β`:

  * `foldAt_kkhU1_one` — `Fold_β(1/(x − w))(x²) = (w + β)/(x² − w²)`;
  * `foldAt_kkhU1_one_eq_zero_iff` — the fold vanishes **iff `β = −w`**.

So a uniformly random terminal challenge destroys the second row of the bad line with
probability exactly `1/|F|` — the bad family is fold-robust until the last level, and
survives even that except for one challenge.  (This is the precise sense in which
fold-based protocols escape the KKH26 family: a `1/q` lottery, not attrition.)
-/

namespace ProximityGap.Issue357.FoldTransport

variable {F : Type*} [Field F]

/-- The FRI fold of `f` at challenge `β`, evaluated at the fiber `{x, −x}` (the value
assigned to `y = x²`). -/
def foldAt (f : F → F) (β x : F) : F :=
  (f x + f (-x)) / 2 + β * ((f x - f (-x)) / (2 * x))

/-- **Fiber-even functions are fold fixed points, β-independently.**  If
`f(−x) = f(x)` then `Fold_β(f)` at that fiber is `f(x)`, for every challenge `β`
(characteristic ≠ 2). -/
theorem foldAt_of_even {f : F → F} {x : F} (hev : f (-x) = f x)
    (h2 : (2 : F) ≠ 0) (β : F) : foldAt f β x = f x := by
  unfold foldAt
  rw [hev]
  field_simp
  ring

/-- The KKH26 numerator row: `u₀ = x^{rm} / (x^m − w)`. -/
def kkhU0 (w : F) (r m : ℕ) (x : F) : F := x ^ (r * m) / (x ^ m - w)

/-- The KKH26 denominator row: `u₁ = 1 / (x^m − w)`. -/
def kkhU1 (w : F) (m : ℕ) (x : F) : F := 1 / (x ^ m - w)

/-- For even exponent parameter the numerator row is fiber-even (no hypotheses:
`(−x)^{2k} = x^{2k}`). -/
theorem kkhU0_neg (w : F) (r m' : ℕ) (x : F) :
    kkhU0 w r (2 * m') (-x) = kkhU0 w r (2 * m') x := by
  unfold kkhU0
  rw [((even_two_mul m').mul_left r).neg_pow, (even_two_mul m').neg_pow]

/-- For even exponent parameter the denominator row is fiber-even. -/
theorem kkhU1_neg (w : F) (m' : ℕ) (x : F) :
    kkhU1 w (2 * m') (-x) = kkhU1 w (2 * m') x := by
  unfold kkhU1
  rw [(even_two_mul m').neg_pow]

/-- **Fold fixed-point, numerator row.**  For even `m = 2m'`, the fold of the KKH26
numerator row at ANY challenge `β` equals the `(r, m')` instance evaluated at `x²` —
the construction is self-similar down the tower, β-independently. -/
theorem foldAt_kkhU0_even (w : F) (r m' : ℕ) (x β : F) (h2 : (2 : F) ≠ 0) :
    foldAt (kkhU0 w r (2 * m')) β x = kkhU0 w r m' (x ^ 2) := by
  rw [foldAt_of_even (kkhU0_neg w r m' x) h2]
  unfold kkhU0
  rw [show r * (2 * m') = (r * m') * 2 by ring, pow_mul', ← pow_mul x 2 m']

/-- **Fold fixed-point, denominator row.** -/
theorem foldAt_kkhU1_even (w : F) (m' : ℕ) (x β : F) (h2 : (2 : F) ≠ 0) :
    foldAt (kkhU1 w (2 * m')) β x = kkhU1 w m' (x ^ 2) := by
  rw [foldAt_of_even (kkhU1_neg w m' x) h2]
  unfold kkhU1
  rw [← pow_mul x 2 m', mul_comm 2 m', mul_comm m' 2]

/-- **β-independence packaged:** the fold of the even-`m` stack does not see the
challenge at all. -/
theorem foldAt_kkh_even_beta_independent (w : F) (r m' : ℕ) (x β β' : F)
    (h2 : (2 : F) ≠ 0) :
    foldAt (kkhU0 w r (2 * m')) β x = foldAt (kkhU0 w r (2 * m')) β' x ∧
    foldAt (kkhU1 w (2 * m')) β x = foldAt (kkhU1 w (2 * m')) β' x := by
  constructor
  · rw [foldAt_kkhU0_even w r m' x β h2, foldAt_kkhU0_even w r m' x β' h2]
  · rw [foldAt_kkhU1_even w m' x β h2, foldAt_kkhU1_even w m' x β' h2]

/-- **Terminal fold of the denominator row (`m = 1`).**  The fold genuinely mixes:
`Fold_β(1/(x − w))(x²) = (w + β)/(x² − w²)` (denominators nonzero). -/
theorem foldAt_kkhU1_one (w x β : F) (h2 : (2 : F) ≠ 0) (hx : x ≠ 0)
    (hxw : x - w ≠ 0) (hxw' : x + w ≠ 0) :
    foldAt (kkhU1 w 1) β x = (w + β) / (x ^ 2 - w ^ 2) := by
  unfold foldAt kkhU1
  have hx2w2 : x ^ 2 - w ^ 2 ≠ 0 := by
    have : x ^ 2 - w ^ 2 = (x - w) * (x + w) := by ring
    rw [this]
    exact mul_ne_zero hxw hxw'
  have hneg : -x - w ≠ 0 := by
    intro h
    apply hxw'
    linear_combination -h
  field_simp
  ring

/-- **The kill-challenge.**  The terminal fold of the KKH26 denominator row vanishes
**iff** `β = −w`.  Hence a uniformly random terminal fold challenge destroys the bad
line's second row with probability exactly `1/|F|`; for every other challenge the
folded stack keeps the `1/(y − w²)`-type shape and the construction survives. -/
theorem foldAt_kkhU1_one_eq_zero_iff (w x β : F) (h2 : (2 : F) ≠ 0) (hx : x ≠ 0)
    (hxw : x - w ≠ 0) (hxw' : x + w ≠ 0) :
    foldAt (kkhU1 w 1) β x = 0 ↔ β = -w := by
  rw [foldAt_kkhU1_one w x β h2 hx hxw hxw']
  have hx2w2 : x ^ 2 - w ^ 2 ≠ 0 := by
    have : x ^ 2 - w ^ 2 = (x - w) * (x + w) := by ring
    rw [this]
    exact mul_ne_zero hxw hxw'
  rw [div_eq_zero_iff]
  constructor
  · rintro (h | h)
    · linear_combination h
    · exact absurd h hx2w2
  · intro h
    left
    rw [h]
    ring

end ProximityGap.Issue357.FoldTransport

-- Axiom audit (expected: propext, Classical.choice, Quot.sound only)
#print axioms ProximityGap.Issue357.FoldTransport.foldAt_kkhU0_even
#print axioms ProximityGap.Issue357.FoldTransport.foldAt_kkhU1_even
#print axioms ProximityGap.Issue357.FoldTransport.foldAt_kkhU1_one_eq_zero_iff
>>>>>>> ee9dcadd2 (feat(#357): R2 FORMALIZED — KKH26FoldTransport.lean: the bad line is a fold FIXED POINT at even m (β-independent, maps to (n/2,m/2) instance verbatim) + the terminal kill-challenge (fold of u₁ vanishes iff β=−w ⟹ 1/q survival lottery), axiom-clean)
