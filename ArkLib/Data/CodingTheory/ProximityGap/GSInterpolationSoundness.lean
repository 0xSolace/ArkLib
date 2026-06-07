import Mathlib
import ArkLib.Data.CodingTheory.ProximityGap.BivariateVanishing
import ArkLib.ToMathlib.BivariateDegreeToolkit

/-! **GS interpolation soundness** (BCIKS20 §5 Claim 5.7 / `hcount` core, GS99 Lemma 4):
a bivariate `Q` vanishing to order `m` at the `|A|` distinct agreement points
`(ω i, P (ω i))`, whose curve restriction `Q.eval P` has degree `< m·|A|`, must restrict to
zero on the curve `Y = P(X)`. This is the multiplicity Schwartz–Zippel forcing the GS factor. -/

open Polynomial Finset

namespace ArkLib.GS

variable {F : Type*} [CommRing F] [IsDomain F]

/-- **The soundness theorem.** If `Q` vanishes to order `m` at each `(ω i, P (ω i))` for `i` in a
finite index set `A` on which `ω` is injective, and the curve restriction `Q.eval P` has
`natDegree < m * |A|`, then `Q.eval P = 0`. The distinct roots `ω i` each contribute
multiplicity `≥ m`, summing to `≥ m·|A|`, exceeding the degree budget unless the restriction
vanishes. -/
theorem eval_eq_zero_of_vanishesToOrder_card {m : ℕ} {Q : Polynomial (Polynomial F)}
    {P : Polynomial F} {ι : Type*} (A : Finset ι) (ω : ι → F) (hω : Set.InjOn ω A)
    (hvan : ∀ i ∈ A, vanishesToOrder m Q (ω i) (P.eval (ω i)))
    (hdeg : (Q.eval P).natDegree < m * A.card) :
    Q.eval P = 0 := by
  classical
  by_contra hne
  -- Each ω i is a root of the restriction of multiplicity ≥ m.
  have hmult : ∀ i ∈ A, m ≤ rootMultiplicity (ω i) (Q.eval P) :=
    fun i hi => (hvan i hi).le_rootMultiplicity_eval P rfl hne
  -- Lower bound: m·|A| ≤ ∑ multiplicities.
  have hsum_ge : m * A.card ≤ ∑ i ∈ A, rootMultiplicity (ω i) (Q.eval P) := by
    calc m * A.card = ∑ _i ∈ A, m := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ i ∈ A, rootMultiplicity (ω i) (Q.eval P) := Finset.sum_le_sum hmult
  -- Upper bound: ∑ multiplicities ≤ card roots ≤ natDegree.
  have hsum_le : ∑ i ∈ A, rootMultiplicity (ω i) (Q.eval P) ≤ (Q.eval P).natDegree := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; simp only [Nat.zero_mul, Nat.not_lt_zero] at hdeg
    have hcount : ∑ i ∈ A, rootMultiplicity (ω i) (Q.eval P)
        = ∑ x ∈ A.image ω, (Q.eval P).roots.count x := by
      rw [Finset.sum_image (fun i hi j hj h => hω hi hj h)]
      exact Finset.sum_congr rfl (fun i _ => (Polynomial.count_roots (Q.eval P)).symm)
    rw [hcount]
    have hsub : A.image ω ⊆ (Q.eval P).roots.toFinset := by
      intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [Multiset.mem_toFinset, ← Multiset.count_pos, Polynomial.count_roots]
      exact lt_of_lt_of_le hmpos (hmult i hi)
    calc ∑ x ∈ A.image ω, (Q.eval P).roots.count x
        ≤ ∑ x ∈ (Q.eval P).roots.toFinset, (Q.eval P).roots.count x :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
      _ = Multiset.card (Q.eval P).roots := Multiset.toFinset_sum_count_eq _
      _ ≤ (Q.eval P).natDegree := (Q.eval P).card_roots'
  omega

/-- **Degree bridge.** The curve restriction `Q.eval P` has natDegree bounded by the
`(1, deg P)`-weighted degree of `Q`. Connects the soundness degree hypothesis to the in-tree
weighted-degree budget. -/
theorem natDegree_eval_le_natWeightedDegree (Q : Polynomial (Polynomial F)) (P : Polynomial F) :
    (Q.eval P).natDegree ≤ Polynomial.Bivariate.natWeightedDegree Q 1 P.natDegree := by
  rw [Polynomial.eval_eq_sum_range]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  rw [Finset.mem_range] at hn
  calc (Q.coeff n * P ^ n).natDegree
      ≤ (Q.coeff n).natDegree + (P ^ n).natDegree := Polynomial.natDegree_mul_le
    _ ≤ (Q.coeff n).natDegree + n * P.natDegree := by gcongr; exact Polynomial.natDegree_pow_le
    _ = 1 * (Q.coeff n).natDegree + P.natDegree * n := by rw [one_mul, mul_comm]
    _ ≤ Polynomial.Bivariate.natWeightedDegree Q 1 P.natDegree :=
        Polynomial.Bivariate.weight_le_natWeightedDegree_of_lt_natDegree_succ (f := Q) hn

/-- Monotonicity of the `(1, v)`-weighted degree in the weight `v`. -/
theorem natWeightedDegree_one_mono {Q : Polynomial (Polynomial F)} {v₁ v₂ : ℕ} (h : v₁ ≤ v₂) :
    Polynomial.Bivariate.natWeightedDegree Q 1 v₁ ≤
      Polynomial.Bivariate.natWeightedDegree Q 1 v₂ := by
  unfold Polynomial.Bivariate.natWeightedDegree
  exact Finset.sup_mono_fun (fun m _ => by gcongr)

/-- **Claim 5.7 vanishing in the in-tree `hcount` form.** If `Q` vanishes to order `m` at the
`|A|` distinct agreement points and the `(1, k)`-weighted degree is below `m·|A|` (the `hcount`
inequality, with `deg P ≤ k`), the curve restriction vanishes. -/
theorem eval_eq_zero_of_vanishesToOrder_of_natWeightedDegree {m k : ℕ}
    {Q : Polynomial (Polynomial F)} {P : Polynomial F} {ι : Type*}
    (A : Finset ι) (ω : ι → F) (hω : Set.InjOn ω A)
    (hvan : ∀ i ∈ A, vanishesToOrder m Q (ω i) (P.eval (ω i)))
    (hP : P.natDegree ≤ k)
    (hcount : Polynomial.Bivariate.natWeightedDegree Q 1 k < m * A.card) :
    Q.eval P = 0 := by
  refine eval_eq_zero_of_vanishesToOrder_card A ω hω hvan ?_
  calc (Q.eval P).natDegree
      ≤ Polynomial.Bivariate.natWeightedDegree Q 1 P.natDegree :=
        natDegree_eval_le_natWeightedDegree Q P
    _ ≤ Polynomial.Bivariate.natWeightedDegree Q 1 k := natWeightedDegree_one_mono hP
    _ < m * A.card := hcount

#print axioms ArkLib.GS.eval_eq_zero_of_vanishesToOrder_card
#print axioms ArkLib.GS.natDegree_eval_le_natWeightedDegree
#print axioms ArkLib.GS.eval_eq_zero_of_vanishesToOrder_of_natWeightedDegree

end ArkLib.GS
