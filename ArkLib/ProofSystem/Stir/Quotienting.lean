/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import CompPoly.Data.MvPolynomial.Notation

open Polynomial NNReal ReedSolomon ListDecodable

namespace Quotienting

variable {n : ℕ}
         {F : Type*} [Field F] [DecidableEq F]
         {ι : Finset F}

/-- Let `Ans : S → F`, `ansPoly(Ans, S)` is the unique interpolating polynomial of degree < |S|
    with `AnsPoly(s) = Ans(s)` for each s ∈ S.

    Note: For S=∅ we get Ans'(x) = 0 (the zero polynomial) -/
noncomputable def ansPoly (S : Finset F) (Ans : S → F) : Polynomial F :=
  Lagrange.interpolate S.attach (fun i => (i : F)) Ans

/-- VanishingPoly is the vanishing polynomial on S, i.e. the unique polynomial of degree |S|+1
    that is 0 at each s ∈ S and is not the zero polynomial. That is V(X) = ∏(s ∈ S) (X - s). -/
noncomputable def vanishingPoly (S : Finset F) : Polynomial F :=
  ∏ s ∈ S, (Polynomial.X - Polynomial.C s)

omit [DecidableEq F] in
/-- The vanishing polynomial vanishes at every point of `S`. -/
lemma vanishingPoly_eval_eq_zero {S : Finset F} {s : F} (hs : s ∈ S) :
    (vanishingPoly S).eval s = 0 := by
  unfold vanishingPoly
  rw [Polynomial.eval_prod]
  exact Finset.prod_eq_zero hs (by simp)

omit [DecidableEq F] in
/-- The vanishing polynomial is nonzero off `S`. -/
lemma vanishingPoly_eval_ne_zero {S : Finset F} {s : F} (hs : s ∉ S) :
    (vanishingPoly S).eval s ≠ 0 := by
  unfold vanishingPoly
  rw [Polynomial.eval_prod]
  refine Finset.prod_ne_zero_iff.mpr fun a ha => ?_
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact sub_ne_zero_of_ne (fun h => hs (h ▸ ha))

omit [DecidableEq F] in
/-- The vanishing polynomial is monic. -/
lemma vanishingPoly_monic (S : Finset F) : (vanishingPoly S).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun s _ => Polynomial.monic_X_sub_C s)

omit [DecidableEq F] in
/-- The vanishing polynomial has degree exactly `|S|`. -/
lemma vanishingPoly_natDegree (S : Finset F) : (vanishingPoly S).natDegree = S.card := by
  unfold vanishingPoly
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun s _ => Polynomial.monic_X_sub_C s)]
  simp

/-- The answer polynomial has degree below `|S|`. -/
lemma ansPoly_degree_lt (S : Finset F) (Ans : S → F) :
    (ansPoly S Ans).degree < S.card := by
  unfold ansPoly
  have h := Lagrange.degree_interpolate_lt (s := S.attach) (v := fun i => (i : F)) Ans
    Subtype.val_injective.injOn
  rwa [Finset.card_attach] at h

/-- The answer polynomial interpolates `Ans` on `S`. -/
lemma ansPoly_eval {S : Finset F} (Ans : S → F) {s : F} (hs : s ∈ S) :
    (ansPoly S Ans).eval s = Ans ⟨s, hs⟩ := by
  unfold ansPoly
  exact Lagrange.eval_interpolate_at_node Ans
    Subtype.val_injective.injOn (Finset.mem_attach S ⟨s, hs⟩)

/-- Definition 4.2
  funcQuotient is the quotient function that outputs
  if x ∈ S,  Fill(x).
  else       (f(x) - Ans'(x)) / V(x).
  Note here that, V(x) = 0 ∀ x ∈ S, otherwise V(x) ≠ 0. -/
noncomputable def funcQuotient (f : ι → F) (S : Finset F) (Ans Fill : S → F) : ι → F :=
  fun x =>
    if hx : x.val ∈ S then Fill ⟨x.val, hx⟩ -- if x ∈ S,  Fill(x).
    else (f x - (ansPoly S Ans).eval x.val) / (vanishingPoly S).eval x.val

/-- Definition 4.3
  polyQuotient is the polynomial derived from the polynomials fPoly, Ans' and V, where
  Ans' is a polynomial s.t. Ans'(x) = fPoly(x) for x ∈ S, and
  V is the vanishing polynomial on S as before.
  Then, polyQuotient = (fPoly - Ans') / V, where
  polyQuotient.degree < (fPoly.degree - ι.card) -/
noncomputable def polyQuotient (S : Finset F) (fPoly : F[X]) : F[X] :=
    (fPoly - (ansPoly S (fun s => fPoly.eval s))) / (vanishingPoly S)

/-- We define the set disagreementSet(f,ι,S,Ans) as the set of all points x ∈ ι that lie in S
such that the Ans' disagrees with f, we have
disagreementSet := { x ∈ ι ∩ S ∧ AnsPoly x ≠ f x }. -/
noncomputable def disagreementSet (f : ι → F) (S : Finset F) (Ans : S → F) : Finset F :=
  Set.toFinset ({x : ι | x.val ∈ S ∧ (ansPoly S Ans).eval x.val ≠ f x}.image Subtype.val)

/-- The quotient-reconstruction polynomial `w * V_S + Ans'` stays below `degree` whenever
`deg w < degree - |S|` and `|S| < degree`. -/
lemma reconstruct_mem_degreeLT {S : Finset F} {degree : ℕ} (hS_lt : S.card < degree)
    {w : Polynomial F} (hw : w ∈ Polynomial.degreeLT F (degree - S.card)) (Ans : S → F) :
    w * vanishingPoly S + ansPoly S Ans ∈ Polynomial.degreeLT F degree := by
  rw [Polynomial.mem_degreeLT] at hw ⊢
  refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) (max_lt ?_ ?_)
  · rcases eq_or_ne w 0 with rfl | hw0
    · rw [zero_mul, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe _
    · rw [Polynomial.degree_mul,
        Polynomial.degree_eq_natDegree (vanishingPoly_monic S).ne_zero,
        vanishingPoly_natDegree]
      have h1 : w.degree + (S.card : WithBot ℕ)
          < ((degree - S.card : ℕ) : WithBot ℕ) + (S.card : WithBot ℕ) :=
        WithBot.add_lt_add_right (by simp) hw
      refine lt_of_lt_of_eq h1 ?_
      rw [← Nat.cast_add, Nat.sub_add_cancel hS_lt.le]
  · exact lt_trans (ansPoly_degree_lt S Ans) (by exact_mod_cast hS_lt)

omit [DecidableEq F] in
/-- Evaluation vectors of `degreeLT` polynomials are codewords. -/
lemma evalOnPoints_mem_code {degree : ℕ} {domain : ι ↪ F} {p : Polynomial F}
    (hp : p ∈ Polynomial.degreeLT F degree) :
    (fun x => p.eval (domain x)) ∈ code domain degree :=
  Submodule.mem_map.mpr ⟨p, hp, rfl⟩

/-- Decoding round-trip: a codeword that is the evaluation vector of a polynomial of degree
below `degree ≤ |ι|` decodes back to that polynomial (interpolation uniqueness). -/
lemma decodeLT_evalOnPoints {degree : ℕ} {domain : ι ↪ F} (hdeg : degree ≤ ι.card)
    {p : Polynomial F} (hp : p ∈ Polynomial.degreeLT F degree)
    (c : code domain degree) (hc : ∀ x, c.val x = p.eval (domain x)) :
    ((decodeLT c : Polynomial F)) = p := by
  have hval : c.val = fun x => p.eval (domain x) := funext hc
  have hlt : p.degree < (((Finset.univ : Finset ι)).card : WithBot ℕ) := by
    rw [Polynomial.mem_degreeLT] at hp
    refine lt_of_lt_of_le hp ?_
    rw [Finset.card_univ, Fintype.card_coe]
    exact_mod_cast hdeg
  have h := Lagrange.eq_interpolate (s := (Finset.univ : Finset ι)) (v := ⇑domain)
    domain.injective.injOn hlt
  calc ((decodeLT c : Polynomial F))
      = Lagrange.interpolate Finset.univ ⇑domain c.val := rfl
    _ = Lagrange.interpolate Finset.univ ⇑domain (fun i => p.eval (domain i)) := by rw [hval]
    _ = p := h.symm

/-- Quotienting Lemma 4.4
  Let `f : ι → F` be a function, `degree` a degree parameter, `δ ∈ (0,1)` be a distance parameter
  `S` be a set with |S| < degree, `Ans, Fill : S → F`. Suppose for all `u ∈ Λ(code, f, δ)`,
  there exists `x : S`, such that `uPoly(x) ≠ Ans(x)` then
  `δᵣ(funcQuotient(f, S, Ans, Fill), code[ι, F, degree - |S|]) + |T|/|ι| > δ`,
  where T is the disagreementSet as defined above -/
lemma quotienting {degree : ℕ} {domain : ι ↪ F} [Nonempty ι]
  (S : Finset F) (hS_lt : S.card < degree) (r : F)
  (f : ι → F) (Ans Fill : S → F) (δ : ℝ≥0) (hδPos : δ > 0) (hδLt : δ < 1)
  (h : ∀ u : code domain degree, u.val ∈ (closeCodewordsRel ↑(code domain degree) f δ) →
    ∃ x : S, ((decodeLT u) : F[X]).eval x.val ≠ Ans x) :
    δᵣ((funcQuotient f S Ans Fill), (code domain (degree - S.card))) +
      ((disagreementSet f S Ans).card) / (ι.card) > δ := by
  sorry

end Quotienting
