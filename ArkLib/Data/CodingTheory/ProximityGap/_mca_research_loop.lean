import ArkLib.Data.CodingTheory.ProximityGap.MCASecondMoment
import ArkLib.Data.CodingTheory.BinomialEntropyBound

open Classical
open scoped BigOperators

namespace ArkLib.CodingTheory.Research

/-- **The $1M Prize Conjecture (OPEN — honest named surface, NOT asserted).**

A previous revision stated this as a `theorem … := sorry`, i.e. it *asserted* the prize via a hole —
the fake-completion pattern banned by #169/#171/#232. It is now a non-asserting `def : Prop`: the
*statement* that some beyond-UDR threshold `τ` makes `mcaPrizeLatticeResolved` hold, so it can be
referenced and (eventually) proved or refuted, **without claiming it**. Discharging it would require
bridging `epsMCA` (a supremum over arbitrary stacks) to Guruswami–Sudan multiplicity bounds — open
research, not a formalization hole. -/
def MCAPrizeBeyondUDRConjecture (domain : Type) [Fintype domain] : Prop :=
  ∃ τ, GrandChallengesLattice.mcaPrizeLatticeResolved domain τ

/-- Lemma bounding the density of false-positive roots for univariate polynomials. -/
lemma root_density_bound_univ {F : Type} [Field F] [Fintype F] (p : Polynomial F) (hp : p ≠ 0) :
    (Finset.univ.filter (fun x => p.eval x = 0)).card ≤ p.natDegree := by
  -- We can use Polynomial.card_roots
  have h_roots := Polynomial.card_roots hp
  -- To bridge the Finset filter to the multiset roots:
  have h_subset : (Finset.univ.filter (fun x => p.eval x = 0)).val ⊆ p.roots := by
    intro x hx
    simp only [Finset.mem_val, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    rw [Polynomial.mem_roots hp]
    exact hx
  have h_card := Multiset.card_le_of_le h_subset
  exact le_trans h_card h_roots

end ArkLib.CodingTheory.Research
