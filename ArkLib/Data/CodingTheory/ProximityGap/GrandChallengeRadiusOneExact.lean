/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeRadiusOne

/-!
# The EXACT radius-one MCA error `ε_mca(RS, 1)` and the decided §1 MCA prize

`GrandChallengeRadiusOne.lean` proves the upper bound
`ε_mca(RS, 1) ≤ C(n, k+1) / |F|` (`epsMCA_one_le_choose_div`). This file proves the
**matching lower bound** in the large-field regime, yielding the *exact* value

  `ε_mca(RS, 1) = C(n, k+1) / |F|`  (`epsMCA_one_eq_choose_div`)

whenever `k + 1 ≤ n` and `|F| > C(C(n, k+1), 2)`, and uses it to **decide** the formal §1
Grand MCA Challenge for Reed–Solomon by the single inequality `C(n, k+1)/|F| ≤ ε*`
(`grandMCAChallenge_iff_choose_le`).

## Strategy for the lower bound

Fix the *deep-hole* second word `u₁ i := (domain i) ^ k` (evaluations of `Xᵏ`). For every
`(k+1)`-subset `T` of `ι`, the unique degree-`≤ k` interpolant of `u₁` through `T` is `Xᵏ`
itself, which has degree exactly `k`, so `u₁` is **non-extendable** on `T`.

The `Xᵏ`-coefficient functional `c_T(u) := (Lagrange.interpolate T domain u).coeff k` is
`F`-linear, satisfies `c_T(u₁) = 1`, and a word `u` is extendable on `T` iff `c_T(u) = 0`.
For a first word `u₀`, the line `u₀ + γ • u₁` is extendable on `T` iff `γ = -c_T(u₀) =: γ_T`,
so each `γ_T` realises `mcaEvent` with witness `T`. The functionals `c_T` are pairwise
distinct (separated by an indicator word), so the `c_T(u₀)` — hence the `γ_T` — can be made
pairwise distinct by avoiding the `C(C(n, k+1), 2)` hyperplanes `{c_T = c_{T'}}`, a union
of `q^{n-1}`-sized kernels that does not cover `(ι → F)` once `q > C(C(n,k+1), 2)`. The bad
`γ`-set then contains the `C(n, k+1)` distinct `γ_T`, giving `Pr_γ ≥ C(n,k+1)/q`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code Polynomial ReedSolomon
open scoped ProbabilityTheory BigOperators

section Exact

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The `Xᵏ`-coefficient functional of the Lagrange interpolant through a node set `T`.
For `T` of size `k + 1` this is `c_T(u) = ∑ i ∈ T, u i / ∏ j ∈ T \ {i}, (domain i - domain j)`,
the leading coefficient of the interpolant; it is `F`-linear in `u`. -/
noncomputable def cT (domain : ι ↪ F) (k : ℕ) (T : Finset ι) : (ι → F) →ₗ[F] F :=
  (Polynomial.lcoeff F k).comp (Lagrange.interpolate T (fun i => domain i))

lemma cT_apply (domain : ι ↪ F) (k : ℕ) (T : Finset ι) (u : ι → F) :
    cT domain k T u = (Lagrange.interpolate T (fun i => domain i) u).coeff k := rfl

/-- The deep-hole word: evaluations of `Xᵏ`. -/
noncomputable def deepHole (domain : ι ↪ F) (k : ℕ) : ι → F := fun i => (domain i) ^ k

/-- **Key identity `c_T(u₁) = 1`.** For a `(k+1)`-subset `T`, the interpolant of the deep-hole
word `deepHole = (Xᵏ ∘ domain)` through `T` is `Xᵏ` itself, whose `k`-th coefficient is `1`. -/
lemma cT_deepHole (domain : ι ↪ F) {k : ℕ} {T : Finset ι} (hT : T.card = k + 1) :
    cT domain k T (deepHole domain k) = 1 := by
  have hinj : Set.InjOn (fun i => domain i) (↑T : Set ι) :=
    fun _ _ _ _ h => domain.injective h
  -- interpolant of (fun i => (X^k).eval (domain i)) through T is X^k since deg X^k = k < #T
  have hdeg : (X ^ k : F[X]).degree < (T.card : WithBot ℕ) := by
    rw [hT]
    calc (X ^ k : F[X]).degree ≤ (k : WithBot ℕ) := degree_X_pow_le k
      _ < ((k + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self k
  have hpoly : Lagrange.interpolate T (fun i => domain i)
      (fun i => (X ^ k : F[X]).eval (domain i)) = X ^ k :=
    Lagrange.interpolate_poly_eq_self hinj (by rwa [Nat.cast_id] at hdeg ⊢)
  have hval : (deepHole domain k) = (fun i => (X ^ k : F[X]).eval (domain i)) := by
    funext i; simp [deepHole, eval_pow, eval_X]
  rw [cT_apply, hval, hpoly]
  rw [coeff_X_pow, if_pos rfl]

/-- **Extendability ⟺ `c_T = 0`.** For a `(k+1)`-subset `T`, a word `u` agrees on `T` with some
RS codeword iff its interpolant has vanishing `k`-th coefficient, i.e. `c_T(u) = 0`. -/
lemma extendable_iff_cT_eq_zero (domain : ι ↪ F) {k : ℕ} {T : Finset ι} (hT : T.card = k + 1)
    (u : ι → F) :
    (∃ w ∈ (ReedSolomon.code domain k : Set (ι → F)), ∀ i ∈ T, w i = u i) ↔
      cT domain k T u = 0 := by
  have hinj : Set.InjOn (fun i => domain i) (↑T : Set ι) :=
    fun _ _ _ _ h => domain.injective h
  set p : F[X] := Lagrange.interpolate T (fun i => domain i) u with hp
  have hpdeg : p.degree < (T.card : WithBot ℕ) := Lagrange.degree_interpolate_lt _ hinj
  have hpeval : ∀ i ∈ T, p.eval (domain i) = u i := fun i hi =>
    Lagrange.eval_interpolate_at_node u hinj hi
  constructor
  · -- extendable ⇒ the extending codeword's poly equals p, has degree < k ⇒ coeff k = 0
    rintro ⟨w, hw, hwagree⟩
    rw [SetLike.mem_coe, mem_code_iff_exists_polynomial] at hw
    obtain ⟨q, hqdeg, hq⟩ := hw
    -- q and p agree on T (size k+1) and both degree < k+1, so q = p
    have hqeval : ∀ i ∈ T, q.eval (domain i) = u i := by
      intro i hi
      have : w i = q.eval (domain i) := congrFun hq i
      rw [← this, hwagree i hi]
    have hqdeg' : q.degree < (T.card : WithBot ℕ) := by
      rw [hT]
      calc q.degree < (k : WithBot ℕ) := hqdeg
        _ < ((k + 1 : ℕ) : WithBot ℕ) := by exact_mod_cast Nat.lt_succ_self k
    have hqp : q = p := by
      refine Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := T) (v := fun i => domain i)
        hinj hqdeg' hpdeg ?_
      intro i hi
      rw [hqeval i hi, ← hpeval i hi]
    -- coeff k of p = coeff k of q = 0 since deg q < k
    rw [cT_apply, ← hp, ← hqp]
    exact Polynomial.coeff_eq_zero_of_degree_lt hqdeg
  · -- c_T u = 0 ⇒ p has degree < k ⇒ p is a deg<k poly extending u on T
    intro hc
    rw [cT_apply, ← hp] at hc
    have hpdeg_k : p.degree < (k : WithBot ℕ) := by
      -- p.degree ≤ k (since < k+1) and coeff k = 0 ⇒ degree < k
      have hle : p.degree ≤ (k : WithBot ℕ) := by
        rw [hT] at hpdeg
        exact Order.le_of_lt_succ (by exact_mod_cast hpdeg)
      rcases lt_or_eq_of_le hle with h | h
      · exact h
      · -- degree = k but coeff k = 0 is impossible unless... use leadingCoeff
        exfalso
        have hk : p.natDegree = k := natDegree_eq_of_degree_eq_some h.symm
        have : p.coeff k ≠ 0 := by
          rw [← hk]
          exact Polynomial.leadingCoeff_ne_zero.mpr (by
            intro h0; rw [h0, degree_zero] at h; exact absurd h.symm (by simp))
        exact this hc
    refine ⟨evalOnPoints domain p, ?_, ?_⟩
    · rw [SetLike.mem_coe, mem_code_iff_exists_polynomial]
      exact ⟨p, hpdeg_k, rfl⟩
    · intro i hi
      change p.eval (domain i) = u i
      exact hpeval i hi

/-- The deep-hole word `u₁ = (Xᵏ ∘ domain)` is non-extendable on every `(k+1)`-subset. -/
lemma nonExtendable_deepHole (domain : ι ↪ F) {k : ℕ} {T : Finset ι} (hT : T.card = k + 1) :
    NonExtendableOn (ReedSolomon.code domain k : Set (ι → F)) T (deepHole domain k) := by
  rw [NonExtendableOn, extendable_iff_cT_eq_zero domain hT, cT_deepHole domain hT]
  exact one_ne_zero

/-- **`γ_T := -c_T(u₀)` makes the line extendable on `T`.** For any first word `u₀`, the line
`u₀ + γ • u₁` is extendable on a `(k+1)`-subset `T` iff `γ = -c_T(u₀)`. -/
lemma line_extendable_iff (domain : ι ↪ F) {k : ℕ} {T : Finset ι} (hT : T.card = k + 1)
    (u₀ : ι → F) (γ : F) :
    (∃ w ∈ (ReedSolomon.code domain k : Set (ι → F)), ∀ i ∈ T, w i = u₀ i + γ • (deepHole domain k) i)
      ↔ γ = -cT domain k T u₀ := by
  rw [extendable_iff_cT_eq_zero domain hT]
  -- c_T (u₀ + γ • u₁) = c_T u₀ + γ • c_T u₁ = c_T u₀ + γ
  have hlin : cT domain k T (u₀ + γ • deepHole domain k)
      = cT domain k T u₀ + γ * cT domain k T (deepHole domain k) := by
    rw [map_add, map_smul]; ring
  rw [hlin, cT_deepHole domain hT, mul_one]
  constructor
  · intro h; linear_combination h
  · intro h; rw [h]; ring

/-- **Each `γ_T` realises `mcaEvent`.** With the deep-hole second word, for any first word `u₀`
and any `(k+1)`-subset `T`, the scalar `γ := -c_T(u₀)` satisfies `mcaEvent (RS) 1 u₀ u₁ γ`
with witness set `T`. -/
lemma mcaEvent_at_gammaT (domain : ι ↪ F) {k : ℕ} {T : Finset ι} (hT : T.card = k + 1)
    (u₀ : ι → F) :
    mcaEvent (ReedSolomon.code domain k : Set (ι → F)) 1 u₀ (deepHole domain k)
      (-cT domain k T u₀) := by
  refine ⟨T, ?_, ?_, ?_⟩
  · -- size clause vacuous at δ = 1: (1 - 1) * n = 0 ≤ card
    simp
  · -- line extendable on T at γ = -c_T(u₀)
    exact (line_extendable_iff domain hT u₀ _).mpr rfl
  · -- no joint pair: u₁ non-extendable on T
    rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
    exact nonExtendable_deepHole domain hT ⟨v₁, hv₁, fun i hi => (hagree i hi).2⟩

/-- **Separation of distinct functionals.** For two distinct `(k+1)`-subsets `T ≠ T'`, the
linear functional `c_T - c_{T'}` is nonzero: pick `i₀ ∈ T \ T'` and evaluate at the indicator
word `e_{i₀}`, where `c_T(e_{i₀}) ≠ 0 = c_{T'}(e_{i₀})`. -/
lemma cT_sub_ne_zero (domain : ι ↪ F) {k : ℕ} {T T' : Finset ι}
    (hT : T.card = k + 1) (hT' : T'.card = k + 1) (hne : T ≠ T') :
    cT domain k T - cT domain k T' ≠ 0 := by
  classical
  -- pick i₀ ∈ T \ T'  (cards equal, sets distinct ⇒ some element of T not in T')
  have hexists : ∃ i₀ ∈ T, i₀ ∉ T' := by
    by_contra h
    push_neg at h
    -- T ⊆ T' and equal cards ⇒ T = T'
    exact hne (Finset.eq_of_subset_of_card_le h (le_of_eq (hT.trans hT'.symm)))
  obtain ⟨i₀, hi₀T, hi₀T'⟩ := hexists
  -- indicator word e_{i₀}
  set e : ι → F := fun i => if i = i₀ then 1 else 0 with he
  intro hcontra
  -- c_{T'}(e) = 0: e restricted to T' is the zero word (i₀ ∉ T'), interpolant is 0
  have hcT'e : cT domain k T' e = 0 := by
    have hzero : (∃ w ∈ (ReedSolomon.code domain k : Set (ι → F)), ∀ i ∈ T', w i = e i) := by
      refine ⟨0, (ReedSolomon.code domain k).zero_mem, ?_⟩
      intro i hi
      have : i ≠ i₀ := fun h => hi₀T' (h ▸ hi)
      simp [he, this]
    exact (extendable_iff_cT_eq_zero domain hT' e).mp hzero
  -- c_T(e) ≠ 0: e is NOT extendable on T, since e|T has a single 1 at i₀ — the interpolant
  -- is a nonzero Lagrange basis polynomial of degree k.
  have hcTe : cT domain k T e ≠ 0 := by
    rw [cT_apply]
    -- interpolant of e through T = (Lagrange.basis T domain i₀), a degree-k poly, coeff k ≠ 0
    have hinj : Set.InjOn (fun i => domain i) (↑T : Set ι) :=
      fun _ _ _ _ h => domain.injective h
    have hbasis : Lagrange.interpolate T (fun i => domain i) e = Lagrange.basis T (fun i => domain i) i₀ := by
      rw [Lagrange.interpolate_apply]
      rw [← Finset.add_sum_erase _ _ hi₀T]
      have h1 : C (e i₀) * Lagrange.basis T (fun i => domain i) i₀
          = Lagrange.basis T (fun i => domain i) i₀ := by
        simp [he]
      rw [h1]
      have h0 : ∑ i ∈ T.erase i₀, C (e i) * Lagrange.basis T (fun i => domain i) i = 0 := by
        refine Finset.sum_eq_zero ?_
        intro i hi
        have : i ≠ i₀ := (Finset.mem_erase.mp hi).1
        simp [he, this]
      rw [h0, add_zero]
    rw [hbasis]
    -- coeff k of basis = leadingCoeff (since natDegree basis = #T - 1 = k) ≠ 0
    have hnatdeg : (Lagrange.basis T (fun i => domain i) i₀).natDegree = k := by
      rw [Lagrange.natDegree_basis hinj hi₀T, hT]
    rw [← hnatdeg, ← Polynomial.leadingCoeff]
    exact Polynomial.leadingCoeff_ne_zero.mpr (Lagrange.basis_ne_zero hinj hi₀T)
  -- contradiction: applying the zero functional to e gives c_T e - c_{T'} e = 0
  have := congrFun (congrArg (DFunLike.coe) hcontra) e
  simp only [LinearMap.sub_apply, LinearMap.zero_apply, hcT'e, sub_zero] at this
  exact hcTe this

/-- **Kernel cardinality of a nonzero functional.** A nonzero linear functional
`φ : (ι → F) →ₗ[F] F` has kernel of `F`-dimension `n - 1`, hence the set of its zeros has
cardinality `q^{n-1}`. -/
lemma card_ker_eq (φ : (ι → F) →ₗ[F] F) (hφ : φ ≠ 0) :
    Fintype.card (LinearMap.ker φ) = Fintype.card F ^ (Fintype.card ι - 1) := by
  classical
  -- finrank of kernel = n - 1 by rank-nullity + surjectivity (range = ⊤, finrank 1)
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top]
    -- range is a submodule of F (dim 1); nonzero ⇒ range = ⊤
    rcases (Submodule.eq_bot_or_eq_top (LinearMap.range φ)) with h | h
    · exfalso; apply hφ
      ext u
      have : φ u ∈ LinearMap.range φ := ⟨u, rfl⟩
      rw [h, Submodule.mem_bot] at this
      simpa using this
    · exact h
  have hrange : Module.finrank F (LinearMap.range φ) = 1 := by
    rw [LinearMap.range_eq_top.mpr hsurj]
    simp [Module.finrank_top, Module.finrank_self]
  have hrn := finrank_range_add_finrank_ker φ
  rw [hrange, Module.finrank_pi (R := F) (ι := ι)] at hrn
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at hrn
  have hker : Module.finrank F (LinearMap.ker φ) = Fintype.card ι - 1 := by omega
  rw [Module.card_eq_pow_finrank (K := F) (V := LinearMap.ker φ), hker]

/-- **Bad-set cardinality bound.** For each pair of distinct subsets, the set of words on which
the two functionals agree has cardinality `q^{n-1}`. Translating to the filter `Finset`. -/
lemma card_agree_le (domain : ι ↪ F) {k : ℕ} {T T' : Finset ι}
    (hT : T.card = k + 1) (hT' : T'.card = k + 1) (hne : T ≠ T') :
    (Finset.univ.filter (fun u : ι → F => cT domain k T u = cT domain k T' u)).card
      = Fintype.card F ^ (Fintype.card ι - 1) := by
  classical
  set φ : (ι → F) →ₗ[F] F := cT domain k T - cT domain k T' with hφdef
  have hφ : φ ≠ 0 := cT_sub_ne_zero domain hT hT' hne
  -- filter = ker φ as sets
  have hbij : (Finset.univ.filter (fun u : ι → F => cT domain k T u = cT domain k T' u))
      = (Finset.univ.filter (fun u : ι → F => u ∈ LinearMap.ker φ)) := by
    apply Finset.filter_congr
    intro u _
    rw [LinearMap.mem_ker]
    simp only [hφdef, LinearMap.sub_apply, eq_iff_iff]
    constructor
    · intro h; rw [h]; ring
    · intro h; linarith [sub_eq_zero.mp (by linear_combination h)]
  rw [hbij]
  -- card of filter (· ∈ ker) = Fintype.card ker
  have : (Finset.univ.filter (fun u : ι → F => u ∈ LinearMap.ker φ)).card
      = Fintype.card (LinearMap.ker φ) := by
    rw [Fintype.card_eq.mpr ⟨?_⟩]
    · rfl
    · exact (Equiv.subtypeEquivRight (by simp)).trans
        (Equiv.Set.ofEq (by ext; simp)) |>.symm.trans (Equiv.refl _)
  rw [this]
  exact card_ker_eq φ hφ

end Exact

end ProximityGap
