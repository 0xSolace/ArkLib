/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.Frontier._PrimeCapacityUncertainty
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Reducing Tao's additive uncertainty to Chebotarev's minor-nonvanishing theorem (#407)

The prime side of the #407 [349] DFT-uncertainty dichotomy
(`_PrimeCapacityUncertainty.lean`) is conditional on a single NAMED OPEN input,
`TaoUncertainty p` (Tao 2005, MRL 12(1):121–127):

> `∀ f : ZMod p → ℂ, f ≠ 0 → |supp f| + |supp 𝓕f| ≥ p + 1`.

Tao's own proof of this principle has exactly one non-elementary ingredient: a classical
theorem of **Chebotarev (1926)** that *every minor of the prime-order DFT matrix is nonzero*
(equivalently: every square submatrix of the Vandermonde-in-`p`-th-roots-of-unity matrix is
invertible). Chebotarev's theorem is itself a deep Galois / cyclotomic-irreducibility fact —
genuinely *false* for composite order, which is the structural reason Tao's additive bound holds
only for primes — and it is **not in Mathlib**.

This file performs the *standard Tao reduction*, isolating Chebotarev as the sole open input:

* **`ChebotarevMinorNonvanishing p` is a NAMED `Prop` (not proven in general).** It is
  Chebotarev's theorem, phrased on the DFT matrix entries `stdAddChar (-(j * k))` actually used by
  `ZMod.dft`: for any `n` and any two *injective* index selections `ri ci : Fin n → ZMod p`
  (distinct rows and distinct columns), the `n × n` submatrix `M i j = stdAddChar (-(ci j * ri i))`
  has nonzero determinant.

* **`tao_of_chebotarev : ChebotarevMinorNonvanishing p → TaoUncertainty p` IS PROVEN here**
  (axiom-clean). The argument: given `f ≠ 0` with `|supp f| + |supp (𝓕 f)| ≤ p`, take `A = supp f`,
  `B = supp (𝓕 f)`, so `|A| ≤ p − |B| = |Bᶜ|`; pick `R ⊆ Bᶜ` with `|R| = |A|`; on `R` the transform
  `𝓕 f` vanishes (`R ⊆ Bᶜ`). Enumerating `R` and `A` by injections `ri, ci : Fin |A| → ZMod p`, the
  restriction of `𝓕 f` to `R` *is* the matrix–vector product `M *ᵥ (f ∘ ci) = 0` with `M` the
  Chebotarev submatrix; `M.det ≠ 0` forces `f ∘ ci = 0`, i.e. `f` vanishes on `A` too, so `f = 0`,
  contradiction.

* **`chebotarev_one : ChebotarevMinorNonvanishing` at `n = 1` IS PROVEN** (trivial: a `1 × 1`
  minor is a single root of unity `stdAddChar (-(ci 0 * ri 0)) ≠ 0`). This de-names the smallest
  case; the general `n` case stays the named open input `ChebotarevMinorNonvanishing`.

## Honesty contract (per #407)

`ChebotarevMinorNonvanishing` is a `def … : Prop` (a named classical hypothesis), so it carries no
axioms; we never `sorry` it and never claim the general case proven. What is PROVEN here is the
*reduction* `tao_of_chebotarev` (plus the `1 × 1` Chebotarev case `chebotarev_one`). This sharpens
`_PrimeCapacityUncertainty`: the prime-capacity dichotomy is now conditional on the *canonical
classical theorem of Chebotarev*, not on the looser folklore statement `TaoUncertainty`.

Reference for the reduction and for Chebotarev's theorem: T. Tao, *An uncertainty principle for
cyclic groups of prime order*, Math. Res. Lett. 12 (2005), 121–127; P. Stevenhagen & H. W. Lenstra,
*Chebotarëv and his density theorem*, Math. Intelligencer 18 (1996) (exposition of Chebotarev's
minor theorem); Tao's blog post of the same title (2005).

Axiom-clean (`propext, Classical.choice, Quot.sound`; no `sorryAx`). Issue #407.
-/

open Finset ZMod Matrix
open ProximityGap.Frontier.ZModDonohoStark
open ProximityGap.Frontier.PrimeCapacityUncertainty

namespace ProximityGap.Frontier.TaoFromChebotarev

variable {p : ℕ} [Fact p.Prime]

/-- **Chebotarev's minor-nonvanishing theorem for the prime DFT matrix (NAMED OPEN INPUT — only the
`n = 1` case is proven, as `chebotarev_one`).**

> For `p` prime, *every minor of the `p × p` DFT matrix is nonzero*.

Phrased on the DFT entries `stdAddChar (-(j * k))` that `ZMod.dft` actually uses: for any `n` and
any pair of *injective* selections `ri ci : Fin n → ZMod p` (so distinct rows and distinct columns),
the `n × n` submatrix `M i j = stdAddChar (-(ci j * ri i))` has nonzero determinant.

This is the classical theorem of **Chebotarev (1926)** — equivalently, every square submatrix of the
Vandermonde matrix in the `p`-th roots of unity is invertible. It is a deep
Galois/cyclotomic-irreducibility fact, **not present in Mathlib**, and *false* for composite order
(which is exactly why Tao's additive uncertainty principle is prime-only). Per the #407 honesty
contract it is a named `Prop` (carries no axioms); we never prove the general case nor `sorry` it.
The smallest case (`n = 1`) IS discharged below (`chebotarev_one`). -/
def ChebotarevMinorNonvanishing (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (n : ℕ) (ri ci : Fin n → ZMod p), Function.Injective ri → Function.Injective ci →
    (Matrix.of fun (i j : Fin n) => (stdAddChar (-(ci j * ri i)) : ℂ)).det ≠ 0

/-- **The `1 × 1` case of Chebotarev's theorem (PROVEN).** A single DFT entry
`stdAddChar (-(ci 0 * ri 0))` is a root of unity, hence nonzero, so the `1 × 1` minor has nonzero
determinant. This de-names the smallest instance of `ChebotarevMinorNonvanishing`; the general `n`
case remains the named open input. -/
theorem chebotarev_one (ri ci : Fin 1 → ZMod p) :
    (Matrix.of fun (i j : Fin 1) => (stdAddChar (-(ci j * ri i)) : ℂ)).det ≠ 0 := by
  rw [Matrix.det_fin_one]
  -- a single DFT entry is a unit-modulus complex number, hence nonzero.
  have hnorm : ‖(stdAddChar (-(ci 0 * ri 0)) : ℂ)‖ = 1 := norm_stdAddChar (N := p) (-(ci 0 * ri 0))
  intro hzero
  simp only [Matrix.of_apply] at hzero
  rw [hzero, norm_zero] at hnorm
  exact one_ne_zero hnorm.symm

/-- **Tao's additive uncertainty principle, reduced to Chebotarev (PROVEN reduction).**

`ChebotarevMinorNonvanishing p ⟹ TaoUncertainty p`, i.e. granting that every minor of the prime DFT
matrix is nonzero, every nonzero `f : ZMod p → ℂ` satisfies `|supp f| + |supp 𝓕f| ≥ p + 1`.

This is the standard Tao argument: by contradiction assume `|A| + |B| ≤ p` for `A = supp f`,
`B = supp (𝓕 f)`; then `|A| ≤ |Bᶜ|`, pick `R ⊆ Bᶜ` of size `|A|`; the restriction of `𝓕 f` to `R`
is `M *ᵥ (f ∘ enum A) = 0` for the Chebotarev submatrix `M` (rows = `R`, columns = `A`); Chebotarev
makes `M` invertible, forcing `f ∘ enum A = 0`, i.e. `f` vanishes on `A` (also off `A` by
definition), so `f = 0` — contradiction.

PROVEN (axiom-clean), consuming only the named `ChebotarevMinorNonvanishing`. -/
theorem tao_of_chebotarev (hCheb : ChebotarevMinorNonvanishing p) : TaoUncertainty p := by
  intro f hf
  -- By contradiction: suppose `|supp f| + |supp (𝓕 f)| ≤ p`.
  by_contra hlt
  set A : Finset (ZMod p) := supp f with hA
  set B : Finset (ZMod p) := supp (𝓕 f) with hB
  -- `hlt : ¬ (p + 1 ≤ |A| + |B|)`, i.e. `|A| + |B| ≤ p`.
  have hle : A.card + B.card ≤ p := by omega
  -- `|univ| = p`.
  have hcardp : Fintype.card (ZMod p) = p := ZMod.card p
  -- `|A| ≤ |Bᶜ|`.
  have hBc : Bᶜ.card = p - B.card := by
    rw [Finset.card_compl, hcardp]
  have hAleBc : A.card ≤ Bᶜ.card := by omega
  -- Pick `R ⊆ Bᶜ` with `|R| = |A|`.
  obtain ⟨R, hRsub, hRcard⟩ := Finset.exists_subset_card_eq hAleBc
  -- Enumerate `R` and `A` by injections `Fin |A| → ZMod p`.
  set n := A.card with hn
  -- equivalences from `Fin n` onto the (sub)types of `R` and `A`.
  let eR : Fin n ≃ R := (R.equivFinOfCardEq hRcard).symm
  let eA : Fin n ≃ A := (A.equivFinOfCardEq hn.symm).symm
  let ri : Fin n → ZMod p := fun i => ((eR i : R) : ZMod p)
  let ci : Fin n → ZMod p := fun j => ((eA j : A) : ZMod p)
  -- both selections are injective.
  have hri_inj : Function.Injective ri := by
    intro a b hab
    exact eR.injective (Subtype.ext (by simpa [ri] using hab))
  have hci_inj : Function.Injective ci := by
    intro a b hab
    exact eA.injective (Subtype.ext (by simpa [ci] using hab))
  -- `ci j ∈ A` and `ri i ∈ Bᶜ`.
  have hci_mem : ∀ j, ci j ∈ A := fun j => (eA j).2
  have hri_mem : ∀ i, ri i ∈ Bᶜ := fun i => hRsub (eR i).2
  -- the Chebotarev submatrix.
  set M : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun (i j : Fin n) => (stdAddChar (-(ci j * ri i)) : ℂ)) with hM
  -- the candidate kernel vector `v j = f (ci j)`.
  set v : Fin n → ℂ := fun j => f (ci j) with hv
  -- KEY: `(M *ᵥ v) i = (𝓕 f) (ri i)`, which is `0` since `ri i ∈ Bᶜ`.
  have hkey : M *ᵥ v = 0 := by
    funext i
    -- `(𝓕 f) (ri i) = 0` because `ri i ∉ supp (𝓕 f) = B`.
    have hzero : (𝓕 f) (ri i) = 0 := by
      have : ri i ∉ B := by
        have := hri_mem i
        simpa [Finset.mem_compl] using this
      by_contra hne
      exact this (by simp [hB, supp, Finset.mem_filter, hne])
    -- expand `(M *ᵥ v) i` as `∑ j, M i j * v j`, reindex to `A`, then back to the full `dft`.
    change (∑ j : Fin n, M i j * v j) = (0 : ℂ)
    simp only [hM, hv, Matrix.of_apply]
    -- the goal is now `∑ j, stdAddChar (-(ci j * ri i)) * f (ci j) = 0`.
    -- reindex `Fin n` → `A` via `eA`, getting a sum over `A`; then re-add the zero terms
    -- (off `A`, `f` vanishes) to recover the full `dft` sum.
    have hreidx : (∑ j : Fin n, (stdAddChar (-(ci j * ri i)) : ℂ) * f (ci j))
        = ∑ a ∈ A, (stdAddChar (-(a * ri i)) : ℂ) * f a := by
      rw [← Finset.sum_coe_sort A (fun a => (stdAddChar (-((a : ZMod p) * ri i)) : ℂ) * f a)]
      exact (Equiv.sum_comp eA
        (fun a => (stdAddChar (-((a : ZMod p) * ri i)) : ℂ) * f a))
    rw [hreidx]
    -- the full dft sum over `ZMod p` equals the sum over `A` (terms off `A = supp f` vanish).
    have hfull : (𝓕 f) (ri i)
        = ∑ a ∈ A, (stdAddChar (-(a * ri i)) : ℂ) * f a := by
      rw [dft_apply]
      simp only [smul_eq_mul]
      refine (Finset.sum_subset (Finset.filter_subset _ _) (fun a _ ha => ?_)).symm
      -- `a ∉ A = supp f` means `f a = 0`.
      have : f a = 0 := by
        simpa [hA, supp, Finset.mem_filter] using ha
      rw [this, mul_zero]
    rw [← hfull, hzero]
  -- Chebotarev: `M.det ≠ 0`, so `M *ᵥ v = 0` forces `v = 0`.
  have hdet : M.det ≠ 0 := hCheb n ri ci hri_inj hci_inj
  have hv0 : v = 0 := Matrix.eq_zero_of_mulVec_eq_zero hdet hkey
  -- `v = 0` means `f` vanishes on `A`; `f` also vanishes off `A` by definition of `supp`.
  -- Conclude `f = 0`, contradicting `hf`.
  apply hf
  funext x
  by_cases hx : x ∈ A
  · -- `x ∈ A`, write `x = ci j` for some `j` and use `v j = 0`.
    obtain ⟨j, hj⟩ : ∃ j, ci j = x := ⟨eA.symm ⟨x, hx⟩, by simp [ci, Equiv.apply_symm_apply]⟩
    have := congrFun hv0 j
    simp only [hv, Pi.zero_apply] at this
    rw [← hj]; simpa using this
  · -- `x ∉ A = supp f` means `f x = 0`.
    have : f x = 0 := by simpa [hA, supp, Finset.mem_filter] using hx
    simpa using this

end ProximityGap.Frontier.TaoFromChebotarev

/-! ## Axiom audit (expected: `propext, Classical.choice, Quot.sound` only — no `sorryAx`).
`ChebotarevMinorNonvanishing` is a `def … : Prop` (a named classical hypothesis), so it carries no
axioms; the PROVEN content below consumes / discharges it. -/
#print axioms ProximityGap.Frontier.TaoFromChebotarev.chebotarev_one
#print axioms ProximityGap.Frontier.TaoFromChebotarev.tao_of_chebotarev
