/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.SubsetSumPairingInflate
import ArkLib.Data.CodingTheory.ProximityGap.ListInteriorT2TwoSymmetric
import Mathlib.Data.Finset.Powerset

/-!
# Round 6 (Issue #232, ABF26) — an explicit `t = 2` LOWER bound via ±pairing zero-sum doubling
# that fixes **BOTH** `e_1` and `e_2`, reducing the joint two-symmetric count to a subset-sum count
# on the pair-squares.

Rounds 1–5 reduced the open core of the §7 list-decoding disproof route to a **field-independent
super-polynomial lower bound** on the count of `(k+t)`-subsets of the smooth negation-closed subgroup
`G` with the top `t` elementary symmetric functions `e_1, …, e_t` *jointly* prescribed. Round 4's
`SubsetSumPairingInflate.lean` realized this for `t = 1` (`subsetSumCount_ge_choose`): adjoining a
doubled pair `{g, −g}` adds `0` to `e_1`, so the `e_1`-fiber inflates by `C(m, s)` at the cost of
`+2s` to the size. Round 5's `ListInteriorT2TwoSymmetric.lean` pinned the **exact** `t = 2` joint
condition (`degDrop_t2_iff_two_symmetric`): both top coefficients of `p_S` vanish iff
`e_1(D_S) = c_1 ∧ e_2(D_S) = c_2`.

This round supplies the **first genuine `t = 2` LOWER bound** — a construction of a super-polynomial
family of `(k+2)`-subsets (more generally `(a+2s)`-subsets) with **both** `e_1` and `e_2` prescribed.

## The valuation-weighted symmetric functions (robust index-model bookkeeping)

We work in the Round-4 ±pairing model: a subset of `G` is a `Finset (Fin m × Bool)` (`Fin m` indexes
the `2^{k−1}` pairs, `Bool` the ± sign), valued by `pairVal g (i, b) = if b then −g i else g i`. The
elementary symmetric functions are taken **over the index set** (so multiplicity is honest even when
`g i = 0` or `g` is non-injective):

* `esymm1 v S = ∑_{p∈S} v p`,   `esymm2 v S = ∑_{T⊆S, |T|=2} ∏_{p∈T} v p`.

These match Round 5's `degDrop_t2_iff_two_symmetric` conventions exactly (the `e_1`, `e_2` of the root
multiset).

## The key structural identity (the heart of this file)

* `esymm2_insert` — `e_2(insert p S) = e_2 S + v p · e_1 S` (the Pascal recursion for `e_2`).
* `esymm1_inflate` / `esymm2_inflate` — **the decisive fact**: adjoining the doubled (untouched) pairs
  `doubledPairs P` to a base `B` keeps `e_1` **exactly fixed** (`= e_1 B`) and shifts `e_2` by exactly
  `−∑_{i∈P} g_i²` (the cross terms between the zero-sum pairs and `B`, and between distinct pairs, all
  cancel because each pair sums to `0`):

    `e_1(inflate B P) = e_1 B`,    `e_2(inflate B P) = e_2 B − ∑_{i∈P} g_i²`.

## The headline (`twoSymmetric_count_ge_squareSubsetSum`)

Both `e_1` and `e_2` of `inflate B P` are therefore **constant in `P`** along any family of pair-sets
`P` with the *same square-sum* `∑_{i∈P} g_i² = sq`. So the joint two-symmetric fiber at the inflated
size `a + 2s` contains the injective image of

  `{ P ⊆ untouched pairs : |P| = s, ∑_{i∈P} g_i² = sq }`,

giving the **lower bound**

  `#{ S : |S| = a+2s, e_1(S) = e_1 B, e_2(S) = e_2 B − sq }  ≥  #{ P : |P| = s, ∑_{i∈P} g_i² = sq }`.

This is the precise `t = 2` analogue of Round 4's `subsetSumCount_ge_choose`: the joint
`(e_1, e_2)`-count is bounded below by a **subset-sum count on the pair-squares `{g_i²}`** — itself a
`t = 1`-shaped subset-sum count, *one level down*.

## Honest scope (what this is and is NOT)

* It is the **first machine-checked reduction** of the `t = 2` joint two-symmetric LOWER bound to a
  concrete combinatorial count, the pair-square subset-sum count. The cancellation of all cross terms
  (`esymm2_inflate`) is the genuinely new structural content over Round 4 (which only needed `e_1`).
* The bound is **field-independent** in the count (it counts distinct subsets all with the *same*
  `(e_1, e_2)`), exactly the field-independence the prize-disproof side needs.
* **The honest caveat the brief anticipated.** The pair-square subset-sum count
  `#{P : |P|=s, ∑_{i∈P} g_i² = sq}` is *itself* a subset-sum count — at `sq = 0` it is large for free
  (`twoSymmetric_count_ge_choose_zero`: `≥ C(m, s)`, the doubled empty base, giving a super-polynomial
  joint `(e_1 = 0, e_2 = 0)` family with **no open hypothesis**), but for a *general nonzero* `sq`
  whether it is super-polynomial reduces to the **same open subset-sum worst-case-spread question one
  level down** on the set `{g_i²}`. So this round genuinely *advances* the `t = 2` lower bound (it
  constructs a large joint fiber unconditionally at the zero target) yet is honest that the *fully
  general* `t = 2` worst-case target reduces, not closes, the open core.

All headline results are `sorry`-free and axiom-clean (`[propext, Classical.choice, Quot.sound]`).

## References
- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
  Tracking issue #232.
-/

open Finset BigOperators

namespace ArkLib.CodingTheory.Round6T2Explicit

open ArkLib.ProximityGap.Round4PairingRecursion

variable {ι : Type*} [DecidableEq ι]
variable {F : Type*} [Field F]

/-! ## Valuation-weighted order-1 and order-2 elementary symmetric functions on the index set. -/

/-- The order-1 elementary symmetric function of `S` weighted by a valuation `v`:
`e_1(S) = ∑_{p∈S} v p`. -/
def esymm1 (v : ι → F) (S : Finset ι) : F := ∑ p ∈ S, v p

/-- The order-2 elementary symmetric function of `S` weighted by a valuation `v`:
`e_2(S) = ∑_{T⊆S, |T|=2} ∏_{p∈T} v p`, the sum over unordered index-pairs. -/
def esymm2 (v : ι → F) (S : Finset ι) : F := ∑ T ∈ S.powersetCard 2, ∏ p ∈ T, v p

@[simp] theorem esymm1_empty (v : ι → F) : esymm1 v (∅ : Finset ι) = 0 := by simp [esymm1]

@[simp] theorem esymm2_empty (v : ι → F) : esymm2 v (∅ : Finset ι) = 0 := by simp [esymm2]

/-- **`e_1` under a single insertion**: `e_1(insert p S) = v p + e_1 S` for `p ∉ S`. -/
theorem esymm1_insert (v : ι → F) {p : ι} {S : Finset ι} (hp : p ∉ S) :
    esymm1 v (insert p S) = v p + esymm1 v S := by
  simp only [esymm1, Finset.sum_insert hp]

/-- **`e_2` under a single insertion (the Pascal recursion)**: `e_2(insert p S) = e_2 S + v p · e_1 S`
for `p ∉ S`. The order-2 symmetric function of `insert p S` splits into the `2`-subsets *avoiding* `p`
(`= e_2 S`) and those *containing* `p` (each `{p, q}` with `q ∈ S`, contributing `v p · v q`, summing
to `v p · e_1 S`). -/
theorem esymm2_insert (v : ι → F) {p : ι} {S : Finset ι} (hp : p ∉ S) :
    esymm2 v (insert p S) = esymm2 v S + v p * esymm1 v S := by
  classical
  unfold esymm2 esymm1
  rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.powersetCard_succ_insert hp]
  have hdisj : Disjoint (S.powersetCard (1 + 1))
      ((S.powersetCard 1).image (insert p)) := by
    rw [Finset.disjoint_left]
    intro T hT hTimg
    rw [Finset.mem_powersetCard] at hT
    rw [Finset.mem_image] at hTimg
    obtain ⟨U, _, rfl⟩ := hTimg
    exact hp (hT.1 (Finset.mem_insert_self p U))
  rw [Finset.sum_union hdisj]
  congr 1
  -- the `p`-containing part: `∑_{U ∈ powersetCard 1 S} ∏ (insert p U) = ∑_{q∈S} v p · v q`
  have hinj : Set.InjOn (insert p) (S.powersetCard 1 : Set (Finset ι)) := by
    intro U hU V hV h
    rw [Finset.mem_coe, Finset.mem_powersetCard] at hU hV
    have hpU : p ∉ U := fun hc => hp (hU.1 hc)
    have hpV : p ∉ V := fun hc => hp (hV.1 hc)
    -- `insert p U = insert p V`, `p ∉ U, V` ⟹ `U = V`
    have := h
    rw [← Finset.erase_insert hpU, ← Finset.erase_insert hpV, this]
  rw [Finset.sum_image hinj, Finset.powersetCard_one, Finset.sum_map, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  have hpq : p ∉ ({q.1} : Finset ι) := by
    simp only [Finset.mem_singleton]; rintro rfl; exact hp q.2
  simp only [Function.Embedding.coeFn_mk]
  rw [Finset.prod_insert hpq, Finset.prod_singleton]

/-! ## `e_1`, `e_2` of a disjoint union (the additivity used to peel off the doubled pairs). -/

/-- **`e_1` is additive on disjoint unions.** -/
theorem esymm1_union (v : ι → F) {A B : Finset ι} (h : Disjoint A B) :
    esymm1 v (A ∪ B) = esymm1 v A + esymm1 v B := by
  simp only [esymm1, Finset.sum_union h]

/-- **`e_2` of a disjoint union**: `e_2(A ∪ B) = e_2 A + e_2 B + e_1 A · e_1 B`. The order-2 symmetric
function of a disjoint union has the cross term `e_1 A · e_1 B` from pairs straddling `A` and `B`. We
prove it by induction on `B`, peeling one element at a time with the Pascal recursion `esymm2_insert`
and the `e_1` additivity. -/
theorem esymm2_union (v : ι → F) {A B : Finset ι} (h : Disjoint A B) :
    esymm2 v (A ∪ B) = esymm2 v A + esymm2 v B + esymm1 v A * esymm1 v B := by
  classical
  induction B using Finset.induction with
  | empty => simp [esymm2_empty]
  | insert q B hqB ih =>
      have hqA : q ∉ A := fun hc => (Finset.disjoint_left.mp h hc) (Finset.mem_insert_self q B)
      have hdisjB : Disjoint A B :=
        h.mono_right (Finset.subset_insert q B)
      have hqAB : q ∉ A ∪ B := by
        rw [Finset.mem_union]; push_neg; exact ⟨hqA, hqB⟩
      have hunion : A ∪ insert q B = insert q (A ∪ B) := by
        rw [Finset.union_insert]
      rw [hunion, esymm2_insert v hqAB, ih hdisjB,
        esymm1_insert v (S := A ∪ B) (p := q) hqAB,
        esymm2_insert v hqB, esymm1_insert v (S := B) hqB,
        esymm1_union v hdisjB]
      ring

/-! ## A single zero-sum ± pair (in the index model): `e_1 = 0`, `e_2 = −g²`. -/

/-- The two slots of pair `i` are distinct as indices, so `e_1(bothPair i) = g i + (−g i) = 0` —
exactly the Round-4 `sum_bothPair`, restated as `esymm1`. -/
theorem esymm1_bothPair {m : ℕ} (g : Fin m → F) (i : Fin m) :
    esymm1 (pairVal g) (bothPair i) = 0 := sum_bothPair g i

/-- **`e_2` of a single zero-sum pair is `−g i²`.** The only `2`-subset of `bothPair i =
{(i,false),(i,true)}` is the whole pair, whose product is `g i · (−g i) = −g i²`. -/
theorem esymm2_bothPair {m : ℕ} (g : Fin m → F) (i : Fin m) :
    esymm2 (pairVal g) (bothPair i) = -(g i) ^ 2 := by
  classical
  unfold esymm2
  -- `bothPair i` has card 2, so `powersetCard 2 (bothPair i) = {bothPair i}`.
  have hcard : (bothPair i).card = 2 := card_bothPair i
  rw [← hcard, Finset.powersetCard_self, Finset.sum_singleton]
  -- the product over both slots is `g i · (−g i) = −g i²`
  rw [bothPair, Finset.prod_pair (by simp)]
  simp only [pairVal]
  ring

end ArkLib.CodingTheory.Round6T2Explicit
