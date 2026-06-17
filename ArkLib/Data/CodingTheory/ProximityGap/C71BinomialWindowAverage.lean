/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import ArkLib.Data.CodingTheory.ProximityGap.C71BinomialIncidence

/-!
# Conjecture 7.1 residual: the binomial strata **dilation-window total/average** incidence (#444)

## Context (extends `C71BinomialIncidence` / `C71BinomialIncidenceGcd`)
`C71BinomialIncidenceGcd.binomial_incidence_card_le_gcd` (`c71binom`) gave the SHARP *per-direction*
bound on the thin-subgroup incidence of one binomial direction `X^i - c X^j` (`c ∈ μ_n` fixed):
`#{x ∈ μ_n : x ≠ 0, x^i = c·x^j} ≤ gcd(i-j, n)`. That is a **worst-case-`c`** bound, and for the
worst `c` it can be as large as `gcd(i-j,n) ~ n/2` (the cyclic-kernel order; the `C71-RESIDUAL`
`DISPROOF_LOG` entry: term-sparsity does NOT cap incidence — the cyclotomic gcd governs it). So the
per-direction gcd bound, taken at the worst dilation scalar, does **not** by itself give an `O(1)`
incidence. The open residual named there is exactly an *amortized* control across the dilation
window.

## The window-total fact (this file)
Fix the exponent gap `d = i - j`. The dilation scalar `c` ranges over the window `μ_n` (the
dilation orbit of a normalized direction). The map `x ↦ x^d` sends `μ_n → μ_n` (a subgroup is
closed under powers), so summing the per-`c` incidence over the whole window simply re-counts each
domain point once:

> `Σ_{c ∈ μ_n} #{x ∈ μ_n : x ≠ 0, x^d = c}  =  #{x ∈ μ_n : x ≠ 0}  =  n`.

Hence the **dilation-window AVERAGE incidence is exactly `1`** — even though the worst single-`c`
incidence is `gcd(d,n)`. This is the soundness-relevant amortized cap the per-direction worst-case
gcd bound misses: across a full dilation orbit the binomial strata contribute, on average, a SINGLE
incidence per scalar; the `gcd(d,n)` mass at the worst `c` is exactly compensated by the empty
fibers at the non-`d`-th-power scalars.

Probe `scripts/probes/probe_binomial_window_avg_incidence.py` (EXACT, thin `μ_n` `n = 2^a`
(`a = 2,3,4`), `p ≡ 1 mod n`, `(p-1)/n ≥ 2`, multi-prime incl `p > n^3` and Fermat `257`, NEVER
`n = q-1`): `Σ_{c∈μ_n} inc = n` in **every** row, with `worst_c = gcd(d,n)`. The window-total `= n`
law held 100%.

## The argument
`Finset.card_eq_sum_card_fiberwise` with `f = (· ^ d)`, source `S₀ = {x ∈ S : x ≠ 0}` and target
window `W`: if `x ↦ x^d` maps `S₀` into `W` then `#S₀ = Σ_{c ∈ W} #{x ∈ S₀ : x^d = c}`. The fiber
predicate `x^d = c` is `C71BinomialIncidence.binomial_root_iff_pow_eq`-equivalent (on the punctured
domain `x ≠ 0`) to the binomial-direction vanishing `x^i - c·x^j = 0`, so the summand is the genuine
incidence count. For `S = μ_n` the `MapsTo` hypothesis is automatic (`μ_n` is closed under `·^d`)
and `#S₀ = n` (since `0 ∉ μ_n`), giving the window total `= n`.

## Theorems
* `windowSum_pow_fiber_eq_card`  : the abstract fiberwise identity — if `(· ^ d)` maps the nonzero
  points of `S` into `W`, then `Σ_{c ∈ W} #{x ∈ S : x ≠ 0, x^d = c} = #{x ∈ S : x ≠ 0}`.
* `windowSum_binomial_incidence_eq_card`  : the same with the fiber written in the genuine
  binomial-direction vocabulary `x^i - c·x^j = 0` (via `binomial_root_iff_pow_eq`).
* `windowSum_binomial_incidence_eq_card_of_subgroup` (HEADLINE) : when `S` is `(· ^ d)`-closed and
  `0 ∉ S` (the `μ_n` case), the dilation-window total incidence equals `#S` exactly — so the window
  average is `(#S)/(#W) = 1` when `W = S`. The amortized `O(1)` cap.

These EXTEND the `C71BinomialIncidence(Gcd)` per-direction counts with the **amortized** window
identity; pure `Finset` fiber combinatorics, no character-sum / BGK content. NON-MOMENT,
field-universal, EXTEND-proven. The `3`-term strata window total, and the reduction of this
window-average to a soundness bound, remain OPEN and are NOT claimed here.

Axiom-clean (`propext, Classical.choice, Quot.sound`).
-/

open Finset

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

namespace ArkLib.ProximityGap.C71BinomialWindowAverage

variable {F : Type*} [Field F] [DecidableEq F]

/-- **The abstract dilation-window fiberwise identity.** If `x ↦ x^d` maps the nonzero points of
`S` into the window `W`, then summing the fiber `{x ∈ S : x ≠ 0, x^d = c}` over `c ∈ W` re-counts
each nonzero point of `S` once: `Σ_{c ∈ W} #(fiber c) = #{x ∈ S : x ≠ 0}`. -/
theorem windowSum_pow_fiber_eq_card (S W : Finset F) (d : ℕ)
    (hmap : ∀ x ∈ S, x ≠ 0 → x ^ d ∈ W) :
    (∑ c ∈ W, (S.filter (fun x => x ≠ 0 ∧ x ^ d = c)).card)
      = (S.filter (fun x => x ≠ 0)).card := by
  set S₀ := S.filter (fun x => x ≠ 0) with hS₀
  -- the map (· ^ d) sends S₀ into W
  have hmaps : (S₀ : Set F).MapsTo (fun x => x ^ d) W := by
    intro x hx
    rw [hS₀, mem_coe, mem_filter] at hx
    exact hmap x hx.1 hx.2
  -- card_eq_sum_card_fiberwise on S₀
  have hcard : S₀.card = ∑ c ∈ W, (S₀.filter (fun x => x ^ d = c)).card :=
    card_eq_sum_card_fiberwise hmaps
  -- rewrite each fiber over S₀ as a fiber over S (the x ≠ 0 condition is shared)
  have hfib : ∀ c : F,
      (S₀.filter (fun x => x ^ d = c)).card
        = (S.filter (fun x => x ≠ 0 ∧ x ^ d = c)).card := by
    intro c
    rw [hS₀, filter_filter]
  rw [hcard]
  exact (Finset.sum_congr rfl (fun c _ => hfib c)).symm

/-- **The window total in genuine binomial-direction vocabulary.** Same identity with the fiber
predicate written as the binomial-direction vanishing `x^i - c·x^j = 0` (equivalent, on the
punctured domain, to `x^(i-j) = c` via `binomial_root_iff_pow_eq`). Requires `j ≤ i` and that
`x ↦ x^(i-j)` maps the nonzero points of `S` into the window `W`. -/
theorem windowSum_binomial_incidence_eq_card (S W : Finset F)
    {i j : ℕ} (hij : j ≤ i)
    (hmap : ∀ x ∈ S, x ≠ 0 → x ^ (i - j) ∈ W) :
    (∑ c ∈ W, (S.filter (fun x => x ≠ 0 ∧ x ^ i - c * x ^ j = 0)).card)
      = (S.filter (fun x => x ≠ 0)).card := by
  rw [← windowSum_pow_fiber_eq_card S W (i - j) hmap]
  apply Finset.sum_congr rfl
  intro c _
  congr 1
  apply filter_congr
  intro x _
  constructor
  · rintro ⟨hxne, hroot⟩
    refine ⟨hxne, ?_⟩
    exact (ArkLib.ProximityGap.C71BinomialIncidence.binomial_root_iff_pow_eq c x hxne hij).mp hroot
  · rintro ⟨hxne, hpow⟩
    refine ⟨hxne, ?_⟩
    exact (ArkLib.ProximityGap.C71BinomialIncidence.binomial_root_iff_pow_eq c x hxne hij).mpr hpow

/-- **The dilation-window total incidence equals `#S` (HEADLINE).** When the window `W = S` is the
domain itself, `S` is closed under `x ↦ x^(i-j)` (the `μ_n` subgroup property), and `0 ∉ S`
(`μ_n` has no zero), the dilation-window total of the binomial-direction incidence equals `#S`
exactly. For `S = μ_n` this is `n` — so the dilation-window AVERAGE incidence is `#S / #S = 1`,
the amortized `O(1)` cap that the per-direction worst-case `gcd(i-j, n)` bound does not give. -/
theorem windowSum_binomial_incidence_eq_card_of_subgroup (S : Finset F)
    {i j : ℕ} (hij : j ≤ i)
    (hclosed : ∀ x ∈ S, x ^ (i - j) ∈ S) (hzero : (0 : F) ∉ S) :
    (∑ c ∈ S, (S.filter (fun x => x ≠ 0 ∧ x ^ i - c * x ^ j = 0)).card) = S.card := by
  have hmap : ∀ x ∈ S, x ≠ 0 → x ^ (i - j) ∈ S := fun x hx _ => hclosed x hx
  rw [windowSum_binomial_incidence_eq_card S S hij hmap]
  -- 0 ∉ S ⟹ filter (· ≠ 0) is everything
  congr 1
  apply Finset.filter_true_of_mem
  intro x hx
  rintro rfl
  exact hzero hx

end ArkLib.ProximityGap.C71BinomialWindowAverage

/-! ## Axiom audit -/
#print axioms ArkLib.ProximityGap.C71BinomialWindowAverage.windowSum_pow_fiber_eq_card
#print axioms ArkLib.ProximityGap.C71BinomialWindowAverage.windowSum_binomial_incidence_eq_card
#print axioms ArkLib.ProximityGap.C71BinomialWindowAverage.windowSum_binomial_incidence_eq_card_of_subgroup
