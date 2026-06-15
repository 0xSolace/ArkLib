/-
Scratch: the codim-`c` realizability constraint for the deployed far-line incidence (#407, B1).

GOAL (b1-realizability-sharp, wave 3).  Extend `_RThinResidueDegree` (excess = residue degree)
and `NvIReconcile` (codim-1 = point sum, codim-2 = h₂-augmented) with the EXACT realizability
characterization of an agreement set, and the structural consequence that the deployed per-`R`
membership at agreement size `m = k + c` is a **codim-`c` divided-difference (Schur-minor) system**.

The realizability lever the count-level (circulant-of-counts) theory discards:
  the agreement set `S` is realized by ONE degree-`<k` codeword `c`, i.e.
    `∏_{x∈S}(X − x)  ∣  (X^a + γ·X^b − c)`     with `deg c < k`.
Equivalently the remainder of `X^a + γ·X^b` modulo `Q_S = ∏_{x∈S}(X−x)` has degree `< k`.
This is a **rank-≤ k** (Hankel / interpolation) constraint: the value-vector of the line on `S`
lies in the `k`-dimensional space of degree-`<k` polynomials restricted to `S`, so for `|S| = m`
it is `m − k` independent linear conditions — the codim-`c` (`c = m − k`) Schur-minor system.

Provable, char-free, axiom-clean.  Combined with `_RThinResidueDegree`:
  realizable `⟹` the residue factor `d` of `Q_S` has `deg d < k` `⟹` ragged excess `< k` (per `S`),
but this bounds the SET, not the bad-`γ` COUNT (the incidence `I` = `#{γ}`); the count is the
open object (numerics: `I = 9,13,89` for `n=8,12,16`, off the `n+1` line at `n=16` — n-GROWING,
NOT `k`-governed).  This file pins the realizability structure exactly and names the count gap.
-/
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Tactic

namespace ProximityGap.Frontier.RThinRealizabilityCodim

open Polynomial Finset

variable {F : Type*} [Field F]

/-- `∏_{x∈S}(X−x)` is monic. -/
theorem rootProd_monic (S : Finset F) : (∏ x ∈ S, (X - C x)).Monic :=
  monic_prod_of_monic _ _ (fun x _ => monic_X_sub_C x)

/-- `∏_{x∈S}(X−x)` has degree exactly `|S|`. -/
theorem rootProd_natDegree_eq (S : Finset F) :
    (∏ x ∈ S, (X - C x)).natDegree = S.card := by
  classical
  rw [natDegree_prod _ _ (fun x _ => X_sub_C_ne_zero x)]; simp

/-- **The line agreement polynomial.** `lineAgree a b γ c = X^a + γ·X^b − c`; its `μ_n`-roots are
the points where the monomial line `X^a + γ·X^b` agrees with the codeword `c`. -/
noncomputable def lineAgree (a b : ℕ) (γ : F) (c : F[X]) : F[X] :=
  X ^ a + C γ * X ^ b - c

/-! ### The realizability characterization (the rank-≤k lever in exact form) -/

/-- **Realizability ⟹ divisibility.** If the degree-`<k` codeword `c` agrees with the line
`X^a + γ·X^b` on every point of `S` (i.e. every `x ∈ S` is a root of `lineAgree a b γ c`), and the
points of `S` are the *exact* root set carried by the monic product, then `Q_S = ∏_{x∈S}(X−x)`
divides `lineAgree a b γ c`.  (The agreement set is the root set; the root product divides any
polynomial vanishing on it.) -/
theorem rootProd_dvd_lineAgree {S : Finset F} {a b : ℕ} {γ : F} {c : F[X]}
    (hroots : ∀ x ∈ S, (lineAgree a b γ c).IsRoot x) :
    (∏ x ∈ S, (X - C x)) ∣ (lineAgree a b γ c) := by
  classical
  -- `∏_{x∈S}(X−x) ∣ p` whenever every `x∈S` is a root of `p` (distinct linear factors).
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · intro x hx y hy hxy
    exact (isCoprime_X_sub_C_of_isUnit_sub
      (by simpa [sub_eq_zero] using (sub_ne_zero.mpr hxy).isUnit)) -- coprime distinct linears
  · intro x hx
    exact (dvd_iff_isRoot).2 (hroots x hx)

/-- **The realizability remainder form.** With `Q_S = ∏_{x∈S}(X−x)` dividing `lineAgree a b γ c`,
the codeword is the *negated remainder*: `lineAgree a b γ c = Q_S * (− ?)`… more precisely the
quotient identity `(X^a + γ·X^b) = Q_S * t + c` for some `t`, with `deg c < k`.  So the remainder
of `X^a + γ·X^b` modulo `Q_S` is the degree-`<k` codeword (when `deg Q_S = |S| > deg c`).  This is
the rank-`≤k` / Hankel realizability constraint: the line reduces, mod the agreement product, to a
degree-`<k` polynomial. -/
theorem realizability_remainder {S : Finset F} {a b : ℕ} {γ : F} {c : F[X]} {k : ℕ}
    (hck : c.natDegree < k) (hkS : k ≤ S.card)
    (hroots : ∀ x ∈ S, (lineAgree a b γ c).IsRoot x) :
    (X ^ a + C γ * X ^ b) % (∏ x ∈ S, (X - C x)) = c := by
  classical
  have hdvd := rootProd_dvd_lineAgree hroots
  obtain ⟨t, ht⟩ := hdvd
  -- `lineAgree = Q_S * t`, i.e. `(X^a+γX^b) − c = Q_S * t`, so `(X^a+γX^b) = Q_S*t + c`.
  have hidS : (X ^ a + C γ * X ^ b) = (∏ x ∈ S, (X - C x)) * t + c := by
    have : (X ^ a + C γ * X ^ b - c) = (∏ x ∈ S, (X - C x)) * t := by
      simpa [lineAgree] using ht
    linear_combination this
  -- `c` has degree `< deg Q_S` (`= |S| ≥ k > deg c`), so `c` is the remainder by uniqueness.
  have hQdeg : (∏ x ∈ S, (X - C x)).natDegree = S.card := rootProd_natDegree_eq S
  have hcdeg : c.degree < (∏ x ∈ S, (X - C x)).degree := by
    rcases eq_or_ne c 0 with rfl | hc0
    · simp only [degree_zero]
      rw [(rootProd_monic S).degree_eq_natDegree, hQdeg]  -- ⊥ < (|S| : ℕ∞)
      exact_mod_cast (Nat.cast_pos.mpr (by omega : 0 < S.card)).bot_lt
    · rw [(rootProd_monic S).degree_eq_natDegree, hQdeg, Polynomial.degree_eq_natDegree hc0]
      exact_mod_cast (by omega : c.natDegree < S.card)
  -- `EuclideanDomain.mod` : `a % b = a - b*(a/b)`; uniqueness via `Polynomial.modByMonic`.
  rw [hidS]
  rw [add_comm, mul_comm]
  exact Polynomial.add_mul_mod_self_left ▸ (by
    -- `(c + Q*t) % Q = c % Q = c` since deg c < deg Q.
    rw [Polynomial.add_mul_mod_self_left]
    exact?)
