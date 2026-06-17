/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib

set_option linter.style.longLine false
set_option autoImplicit false

/-!
# wf-A02 (#444): the MULTIPLICATIVE / dilation-action large sieve collapses (OBSTRUCTION)

**Angle A02 [MILDER target, OBSTRUCTION verdict].** Alternative route to the S2 equidistribution
constant `κ` (`_wfS2_equidist_to_M.lean`): the per-coset values `η_b` (`b` over the `m=(p-1)/n`
cosets of `μ_n`) are the *dilation orbit* of `η_1`, so a **multiplicative large sieve /
almost-orthogonality** on that orbit might bound the worst coset-mass `max_j w_j` (`w_j=|η_{g^j}|²`)
by a bounded multiple of the average `W(0)=mean(w)` — giving `κ=O(1)` for free, a milder win than
the BGK additive-energy wall.

## What the route actually delivers (the obstruction)

The per-coset mass `w` is a function on the cyclic quotient `Q=F_p^*/μ_n ≅ ℤ/m`; dilation by the
generator-coset is the `+1` shift on `ℤ/m`. Expand `w` in the *multiplicative characters of `Q`*
(= the DFT of `ℤ/m`): `w_j = ∑_k W(k) e(jk/m)`, `W(0)=mean(w)`. There are exactly **two** sieve
ceilings on the worst coset-mass available from this spectrum:

* **`ℓ¹` (the multiplicative large sieve, triangle inequality):**
  `max_j w_j ≤ ∑_k |W(k)| =: L¹`, hence `κ := max_j w_j / W(0) ≤ L¹/W(0)`.
* **`ℓ²` (Cauchy–Schwarz / Plancherel):** `(max_j w_j)² ≤ ∑_j w_j² = m·∑_k|W(k)|² =: m·(L²)²`.

**The measured fact (`probe_wfA02_multiplicative_largesieve.rs`, exact, β=4, n=8..128):** the
dilation spectrum is **Ramanujan-flat** — `max_{k≠0}|W(k)| ≈ W(0)/√m` and
`L¹/W(0) = (1.17–1.23)·√m` (flat ratio to `√m` across five `n`), while `L²/W(0) ≈ 1.62–1.70`
(flat, bounded; `(L²/W(0))² ≈ 2.6–2.9` is exactly the fourth-moment PAPR `E₂/(mean)²`). So:

* The `ℓ¹` ceiling is `L¹/W(0) = Θ(√m) = Θ(√p/n)` — **vacuous** (it is `≫` any polylog target
  `√(log(p/n))`; at the prize point `m≈2^90`, `√m≈2^45 ≫ √(90)≈9.5`). The multiplicative large
  sieve via the dilation spectrum gives **no** sub-trivial bound on `κ`.
* The only *bounded* sieve content is `L²` — but that is exactly the **second/fourth Parseval
  moment** already in the substrate (`subgroup_gaussSum_fourthMoment`), and the `ℓ²` ceiling
  `max_j w_j ≤ √m·L²` is **also** `Θ(√m)` (the bounded `L²/W(0)` still loses a `√m`). Per the
  conservation-law meta-theorem, the second moment caps at Johnson `n^{1/2}` and cannot reach the
  log-saving prize form. **No closure.**

This is the EXACT analogue, for the *multiplicative/dilation* action, of the recorded collapse of
the *additive* large sieve (`LargeSieveParsevalCollapse.lean`, where the full-residue separation
`δ⁻¹=q` makes the sieve `=2×` Parseval). Both packagings are second-order and cannot beat the
diagonal they are built from.

## What is proven here (axiom-clean, abstract ℝ-arithmetic)

Three guardrails, each a self-contained inequality with the measured law as the only (named)
input:

1. `largeSieve_l1_ceiling` — the `ℓ¹` sieve bound `κ ≤ L¹/W₀` (triangle inequality, abstract).
2. `ramanujan_flat_l1_vacuous` — Ramanujan flatness `L¹ ≥ a·√m·W₀` makes the `ℓ¹` ceiling
   `≥ a·√m`, which **exceeds** any polylog target `T` once `m > (T/a)²`. The sieve route is
   vacuous at prize scale.
3. `l2_ceiling_also_loses_sqrt_m` — the `ℓ²`/Plancherel ceiling `max_j w_j ≤ √m·L²` likewise
   carries a `√m` loss, so the bounded `L²` does **not** rescue the route: it reproduces only the
   second-moment Parseval bound (`Θ(√m)`), already known to cap at Johnson.

No Weil / characteristic-`p` input; pure `ℝ`-arithmetic on the dilation spectrum. The verdict is
**OBSTRUCTION**: the multiplicative large sieve is the wrong tool — it is `ℓ²`-blind exactly like
the additive one, and the dilation spectrum's Ramanujan flatness blocks any `ℓ¹` gain.

Issue #444, angle A02.
-/

namespace ArkLib.ProximityGap.Frontier.A02MultiplicativeLargeSieve

/-- The `ℓ¹`-mass of the dilation spectrum: `L¹ = ∑_k |W(k)|` (here as an abstract nonneg real). -/
noncomputable def L1mass (L1 : ℝ) : ℝ := L1

/-- The `ℓ²`-mass of the dilation spectrum: `L² = √(∑_k |W(k)|²)` (Plancherel `= √(mean w²)`). -/
noncomputable def L2mass (L2 : ℝ) : ℝ := L2

/--
**(1) The `ℓ¹` (multiplicative large sieve) ceiling.** The worst coset-mass divided by the average
is at most the `ℓ¹`-mass of the dilation spectrum divided by the average: `κ ≤ L¹/W₀`. This is the
triangle inequality `max_j w_j ≤ ∑_k|W(k)|` applied to `w_j = ∑_k W(k)e(jk/m)`, then normalized by
`W₀ = W(0) = mean(w)`. Stated abstractly with `maxW = max_j w_j`, `W0 = mean`, `L1 = ∑|W(k)|` and
the triangle hypothesis `maxW ≤ L1`.
-/
theorem largeSieve_l1_ceiling
    {maxW W0 L1 : ℝ} (hW0 : 0 < W0)
    (htriangle : maxW ≤ L1) :
    maxW / W0 ≤ L1 / W0 :=
  (div_le_div_iff_of_pos_right hW0).mpr htriangle

/--
**(2) Ramanujan flatness makes the `ℓ¹` route VACUOUS.** The measured law (β=4, n=8..128) is
`L¹ ≥ a·√m·W₀` with `a ≈ 1.17` — the dilation spectrum is Ramanujan-flat, so its `ℓ¹`-mass scales
like `√m·W₀`, not `O(W₀)`. Then the `ℓ¹` sieve ceiling on `κ` is at least `a·√m`, which exceeds any
fixed polylog target `T` as soon as `m > (T/a)²`. At the prize point `m ≈ 2^90` and `T ≈ √(log(p/n))
≈ 9.5`, this is overwhelmingly satisfied (`√m ≈ 2^45`). Hence the multiplicative large sieve gives
**no** bound below the trivial `√m`: it is vacuous at prize scale.

Stated abstractly: from the flatness lower bound `a·√m·W₀ ≤ L¹` (`a>0`, `W₀>0`), the `ℓ¹` ceiling
`L¹/W₀ ≥ a·√m`, and if the target `T` satisfies `T < a·√m` (the prize regime) then the ceiling
strictly exceeds the target — the sieve cannot certify `κ ≤ T`. -/
theorem ramanujan_flat_l1_vacuous
    {W0 L1 a m T : ℝ} (hW0 : 0 < W0) (ha : 0 < a) (hm : 0 ≤ m)
    (hflat : a * Real.sqrt m * W0 ≤ L1)
    (hbig : T < a * Real.sqrt m) :
    T < L1 / W0 := by
  have hge : a * Real.sqrt m ≤ L1 / W0 := by
    rw [le_div_iff₀ hW0]
    exact hflat
  exact lt_of_lt_of_le hbig hge

/--
**The threshold form.** The `ℓ¹` sieve ceiling exceeds any polylog target `T` once
`m > (T/a)²`. So at the prize scale `m = (p-1)/n ≈ 2^90` (with `T ≈ √log(p/n) ≈ 9.5`, `a ≈ 1.17`),
the route is vacuous by a margin of `√m / T ≈ 2^45/9.5`. -/
theorem ramanujan_flat_l1_threshold
    {W0 L1 a m T : ℝ} (hW0 : 0 < W0) (ha : 0 < a) (hT : 0 ≤ T)
    (hflat : a * Real.sqrt m * W0 ≤ L1)
    (hthresh : (T / a) ^ 2 < m) :
    T < L1 / W0 := by
  have hm : 0 ≤ m := le_of_lt (lt_of_le_of_lt (by positivity) hthresh)
  -- T < a·√m  ⟺  (T/a)² < m  (for a>0, T≥0)
  have hbig : T < a * Real.sqrt m := by
    rw [show a * Real.sqrt m = a * Real.sqrt m from rfl]
    -- compare squares: (T)² < (a√m)² = a²·m, and both sides ≥ 0
    have hsq : T ^ 2 < (a * Real.sqrt m) ^ 2 := by
      have hrw : (a * Real.sqrt m) ^ 2 = a ^ 2 * m := by
        rw [mul_pow, Real.sq_sqrt hm]
      rw [hrw]
      have : T ^ 2 = a ^ 2 * (T / a) ^ 2 := by
        field_simp
      rw [this]
      have ha2 : 0 < a ^ 2 := by positivity
      nlinarith [hthresh, ha2]
    have hpos : 0 ≤ a * Real.sqrt m := by positivity
    nlinarith [hsq, hT, hpos]
  exact ramanujan_flat_l1_vacuous hW0 ha hm hflat hbig

/--
**(3) The `ℓ²`/Plancherel ceiling ALSO loses `√m`.** The Cauchy–Schwarz route gives
`(max_j w_j)² ≤ ∑_j w_j² = m·(L²)²`, i.e. `max_j w_j ≤ √m·L²`. Since the measured `L²/W₀` is
*bounded* (`≈1.66`), one might hope this rescues the route — but it still carries the `√m` factor:
`κ = max/W₀ ≤ √m·(L²/W₀) = Θ(√m)`, just as vacuous as `ℓ¹`. The bounded `L²` is exactly the
proven second/fourth Parseval moment, which the conservation-law meta-theorem caps at Johnson
`n^{1/2}`; it cannot produce the log-saving prize form. Stated abstractly: from the Plancherel
ceiling `maxW ≤ √m · L2` (`L2 ≥ 0`, `m ≥ 0`), normalizing by `W₀ > 0` gives
`κ ≤ √m · (L²/W₀)`. -/
theorem l2_ceiling_also_loses_sqrt_m
    {maxW W0 L2 m : ℝ} (hW0 : 0 < W0) (_hm : 0 ≤ m) (_hL2 : 0 ≤ L2)
    (hplancherel : maxW ≤ Real.sqrt m * L2) :
    maxW / W0 ≤ Real.sqrt m * (L2 / W0) := by
  rw [div_le_iff₀ hW0]
  calc maxW ≤ Real.sqrt m * L2 := hplancherel
    _ = Real.sqrt m * (L2 / W0) * W0 := by field_simp

/--
**The two-ceiling collapse (the A02 verdict, exact form).** With the *measured* dilation spectrum
(`L¹ = a·√m·W₀` Ramanujan-flat, `L² = b·W₀` bounded), BOTH sieve ceilings on `κ` are
`Θ(√m)`: the `ℓ¹` ceiling is `a·√m` and the `ℓ²` ceiling is `b·√m`. Neither beats the trivial
`√m`, and the multiplicative large sieve supplies no sub-trivial control on the equidistribution
constant. (`ℓ¹` flat, `ℓ²` bounded — yet both `√m`-lossy: the sieve is the wrong side of the
diagonal, exactly like the additive collapse `LargeSieveParsevalCollapse.lean`.) -/
theorem both_ceilings_theta_sqrt_m
    {W0 a b m : ℝ} (hW0 : 0 < W0) (_hm : 0 ≤ m) :
    (a * Real.sqrt m * W0) / W0 = a * Real.sqrt m ∧
    (Real.sqrt m * (b * W0)) / W0 = Real.sqrt m * b := by
  constructor
  · field_simp
  · field_simp

end ArkLib.ProximityGap.Frontier.A02MultiplicativeLargeSieve

#print axioms ArkLib.ProximityGap.Frontier.A02MultiplicativeLargeSieve.largeSieve_l1_ceiling
#print axioms ArkLib.ProximityGap.Frontier.A02MultiplicativeLargeSieve.ramanujan_flat_l1_vacuous
#print axioms ArkLib.ProximityGap.Frontier.A02MultiplicativeLargeSieve.ramanujan_flat_l1_threshold
#print axioms ArkLib.ProximityGap.Frontier.A02MultiplicativeLargeSieve.l2_ceiling_also_loses_sqrt_m
#print axioms ArkLib.ProximityGap.Frontier.A02MultiplicativeLargeSieve.both_ceilings_theta_sqrt_m
