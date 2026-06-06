/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import Mathlib
import ArkLib.ToMathlib.SubspacePolyLinearized
import ArkLib.ToMathlib.BKR06Injection
import ArkLib.ToMathlib.BKR06Close

/-!
# BKR06 end-to-end: tight family + closeness wiring (`hclose` discharged)

This file performs the final wiring of the BKR06 (Ben-Sasson–Kopparty–Radhakrishnan,
FOCS 2006) superpolynomial Reed–Solomon list-size construction, composing three
previously-proven bricks:

1. the **tight pigeonhole family** with all parameter side conditions discharged
   (`BKR06.bkr06_tight_family_hfamily_param_free`, `SubspacePolyLinearized.lean`):
   a family of `≥ q^{m·u − v²}` distinct dimension-`v` subspaces of `K = 𝔽_{q^m}`
   whose subspace polynomials pairwise agree above degree `q^u`;
2. the **agreement→relative-distance conversion** (`BKR06Close.lean`): a codeword
   agreeing with the received word on `≥ a` of `N` points lies in the
   `δ`-close-codeword set once `q^{β−1} ≤ a/N`;
3. the **injective encoding + counting hand-off** (`BKR06Injection.lean`):
   an injective family of close codewords lower-bounds the close-codeword count.

The two new pieces of arithmetic are:

* `bkr06_param_ineq_extension` — the closeness parameter inequality **at the
  extension parameters** `N = #K = q^m`, `a = q^v`: it reduces to `β·m ≤ v`, i.e.
  exactly BKR06's `v ≈ β·m` dimension convention.
* `agreement_count_ge_card` — with a surjective evaluation domain, the codeword
  `eval (pivot − P_W)` agrees with `eval pivot` on at least `#W = q^v` points (the
  points of `W` itself, via the proven root identity).

The headline result is `bkr06_close_codewords_card_ge_tight`: for `2 ≤ q = #F`,
`v ≤ m = [K:F]`, cutoff `u ≤ v` with `v² ≤ m·u` and `u < m`, and any `β` with
`β·m ≤ v`, there is a pivot word whose `δ = 1 − (#K)^{β−1}`-close-codeword set in
`RS[K, K, q^u + 1]` has at least `q^{m·u − v²}` elements — the BKR06 tight list-size
lower bound with **every** side condition (`hlin`, `hexp`, `hparam`, `hexp_nonneg`,
`hclose`, `hsmall`, `hdistinct`, `hfamily`) discharged in-tree.

All declarations compile `sorry`/`axiom`-free and are axiom-clean
(`[propext, Classical.choice, Quot.sound]`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

noncomputable section

open Polynomial Finset

namespace BKR06

universe u

variable {K : Type u} [Field K] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra F K]

/-! ## The closeness parameter inequality at extension parameters -/

/-- **BKR06 closeness parameter inequality, extension form.**  At the extension
parameters the domain size is `N = q^m` and the agreement count is `a = q^v`, so the
closeness inequality `N^{β−1} ≤ a/N` reads `q^{m(β−1)} ≤ q^{v−m}`, which holds iff
`β·m ≤ v` — exactly BKR06's `v ≈ β·m` dimension convention.  We prove the direction
needed for closeness. -/
lemma bkr06_param_ineq_extension (q m v : ℕ) (β : ℝ) (hq : 2 ≤ q)
    (hβv : β * (m : ℝ) ≤ (v : ℝ)) :
    ((q : ℝ) ^ m) ^ (β - 1) ≤ ((q : ℝ) ^ v) / (q : ℝ) ^ m := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.le_of_lt (Nat.lt_of_lt_of_le Nat.one_lt_two hq)
  have hL : ((q : ℝ) ^ m) ^ (β - 1) = (q : ℝ) ^ ((m : ℝ) * (β - 1)) := by
    rw [← Real.rpow_natCast (q : ℝ) m, ← Real.rpow_mul (le_of_lt hq0)]
  have hR : ((q : ℝ) ^ v) / (q : ℝ) ^ m = (q : ℝ) ^ ((v : ℝ) - (m : ℝ)) := by
    rw [Real.rpow_sub hq0, Real.rpow_natCast, Real.rpow_natCast]
  rw [hL, hR]
  exact Real.rpow_le_rpow_of_exponent_le hq1 (by nlinarith)

/-! ## Agreement count at the subspace points -/

/-- **Agreement count `≥ #W`.**  With a surjective evaluation domain, the BKR06
codeword `eval (pivot − P_W)` agrees with the received word `eval pivot` on at least
`#W` evaluation points — namely the points of `W` itself, where `P_W` vanishes
(`evalOnPoints_sub_subspacePoly_agrees_on_W`). -/
lemma agreement_count_ge_card
    (domain : K ↪ K) (hsurj : Function.Surjective domain)
    (pivot : K[X]) (W : Submodule F K) [Fintype W] :
    Fintype.card W ≤
      (Finset.univ.filter (fun x : K =>
        ReedSolomon.evalOnPoints domain pivot x
          = ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset W)) x)).card := by
  classical
  have hsub : (Finset.univ.filter (fun x : K => domain x ∈ W))
      ⊆ Finset.univ.filter (fun x : K =>
          ReedSolomon.evalOnPoints domain pivot x
            = ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset W)) x) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact evalOnPoints_sub_subspacePoly_agrees_on_W domain pivot W x hx
  have hcard : (Finset.univ.filter (fun x : K => domain x ∈ W)).card = Fintype.card W := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr
      ((Equiv.ofBijective _ ⟨domain.injective, hsurj⟩).subtypeEquiv
        (fun x => Iff.rfl))
  calc Fintype.card W = (Finset.univ.filter (fun x : K => domain x ∈ W)).card := hcard.symm
    _ ≤ _ := Finset.card_le_card hsub

/-! ## `hclose` discharged at the BKR06 extension parameters -/

/-- **The `hclose` residual, discharged.**  A family member's codeword
`eval (pivot − P_W)` (with `W` of dimension `v` and `pivot − P_W` of degree `< k`)
lies in the `δ = 1 − (#K)^{β−1}`-close-codeword set of the received word
`eval pivot` in `RS[K, K, k]`, provided `β·m ≤ v` (BKR06's `v ≈ β·m`).  Composes the
proven agreement count (`agreement_count_ge_card`), the extension-parameter
closeness inequality (`bkr06_param_ineq_extension`), and the generic
agreement→relative-distance brick (`BKR06Close.mem_closeCodewordsRel_of_agreement`). -/
theorem mem_closeCodewordsRel_of_subspace
    (domain : K ↪ K) (hsurj : Function.Surjective domain)
    (pivot : K[X]) (k : ℕ) (W : Submodule F K) [Fintype W]
    (q v : ℕ) (hq : 2 ≤ q) (hqcard : Fintype.card F = q)
    (hdim : Module.finrank F W = v) (hvm : v ≤ Module.finrank F K)
    (hdeg : pivot - subspacePoly (subFinset W) ∈ Polynomial.degreeLT K k)
    (β : ℝ) (hβv : β * (Module.finrank F K : ℝ) ≤ (v : ℝ)) :
    ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset W))
      ∈ ListDecodable.closeCodewordsRel
          ((ReedSolomon.code domain k : Set (K → K)))
          (ReedSolomon.evalOnPoints domain pivot)
          (1 - (Fintype.card K : ℝ) ^ (β - 1)) := by
  classical
  have hKcard : Fintype.card K = q ^ Module.finrank F K := by
    rw [← hqcard]; exact Module.card_eq_pow_finrank (K := F) (V := K)
  have hWcard : Fintype.card W = q ^ v := by
    rw [← hqcard, ← hdim]; exact Module.card_eq_pow_finrank (K := F) (V := W)
  apply BKR06Close.mem_closeCodewordsRel_of_agreement
      (C := (ReedSolomon.code domain k : Set (K → K)))
      (a := q ^ v) (q := Fintype.card K) (β := β)
  · exact evalOnPoints_mem_code_of_degree_lt domain _ k hdeg
  · rw [← hWcard]
    exact agreement_count_ge_card domain hsurj pivot W
  · rw [hKcard]
    exact Nat.pow_le_pow_right (by omega) hvm
  · rfl
  · rw [hKcard]
    push_cast
    exact bkr06_param_ineq_extension q (Module.finrank F K) v β hq hβv

/-! ## End-to-end: the tight close-codeword count -/

/-- **BKR06 tight close-codeword lower bound, end-to-end.**  For `2 ≤ q = #F`,
dimension `v ≤ m := [K:F]`, cutoff `u ≤ v` with `v² ≤ m·u` and `u < m`, and any
`β` with `β·m ≤ v` (BKR06's `v ≈ β·m` convention): there is a pivot word whose
close-codeword set at relative radius `δ = 1 − (#K)^{β−1}` in `RS[K, K, q^u + 1]`
(full evaluation domain) has at least `q^{m·u − v²}` elements.

Every side condition of the BKR06 chain is discharged in-tree: `hlin`
(`subspacePoly_isQLinearized_of_finrank`), `hexp`/`hparam`/`hexp_nonneg`
(`bkr06_tight_family_hfamily_param_free`), `hsmall` (from the pigeonhole window
`q^u + 1 ≤ q^m`), `hdistinct` (pigeonhole injectivity), `hclose`
(`mem_closeCodewordsRel_of_subspace`), and the final count
(`bkr06_family_close_codewords_card_ge`). -/
theorem bkr06_close_codewords_card_ge_tight
    (q : ℕ) (hq : 2 ≤ q) (hqcard : Fintype.card F = q)
    (v u : ℕ) (hv : v ≤ Module.finrank F K) (huv : u ≤ v)
    (hexp_nonneg : v ^ 2 ≤ Module.finrank F K * u) (hum : u < Module.finrank F K)
    (β : ℝ) (hβv : β * (Module.finrank F K : ℝ) ≤ (v : ℝ)) :
    ∃ pivot : K[X],
      (q : ℝ) ^ ((Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2) ≤
        ((ListDecodable.closeCodewordsRel
            ((ReedSolomon.code (Function.Embedding.refl K) (q ^ u + 1) : Set (K → K)))
            (ReedSolomon.evalOnPoints (Function.Embedding.refl K) pivot)
            (1 - (Fintype.card K : ℝ) ^ (β - 1))).ncard : ℝ) := by
  classical
  obtain ⟨ι, hF, hD, 𝓛, hFL, hdim, hinj, hwindow, hbound⟩ :=
    bkr06_tight_family_hfamily_param_free q hq hqcard v u hv huv hexp_nonneg
  -- the family is nonempty: its size dominates a positive real power
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_two hq
  haveI : Nonempty ι := by
    rcases isEmpty_or_nonempty ι with hE | hN
    · exfalso
      rw [Fintype.card_eq_zero] at hbound
      have hpos : (0 : ℝ) < (q : ℝ) ^ ((Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2) :=
        Real.rpow_pos_of_pos hq0 _
      simp only [Nat.cast_zero] at hbound
      linarith
    · exact hN
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  refine ⟨subspacePoly (subFinset (𝓛 i₀)), ?_⟩
  set pivot : K[X] := subspacePoly (subFinset (𝓛 i₀)) with hpivot
  set domain : K ↪ K := Function.Embedding.refl K with hdomain
  have hsurj : Function.Surjective domain := fun x => ⟨x, rfl⟩
  set k : ℕ := q ^ u + 1 with hk
  have hKcard : Fintype.card K = q ^ Module.finrank F K := by
    rw [← hqcard]; exact Module.card_eq_pow_finrank (K := F) (V := K)
  have hk_le : k ≤ Fintype.card K := by
    rw [hKcard, hk]
    have : q ^ u < q ^ Module.finrank F K :=
      Nat.pow_lt_pow_right (by omega) hum
    omega
  have hdeg : ∀ i, pivot - subspacePoly (subFinset (𝓛 i)) ∈ Polynomial.degreeLT K k :=
    fun i => hwindow i₀ i
  have hsmall : ∀ i,
      (pivot - subspacePoly (subFinset (𝓛 i))).natDegree < Fintype.card K := by
    intro i
    by_cases h0 : pivot - subspacePoly (subFinset (𝓛 i)) = 0
    · rw [h0]
      simp only [Polynomial.natDegree_zero]
      exact Nat.lt_of_lt_of_le (Nat.succ_pos _) hk_le
    · have hdeg_lt : (pivot - subspacePoly (subFinset (𝓛 i))).degree < (k : ℕ) :=
        Polynomial.mem_degreeLT.mp (hdeg i)
      exact Nat.lt_of_lt_of_le
        ((Polynomial.natDegree_lt_iff_degree_lt h0).mpr hdeg_lt) hk_le
  have hclose : ∀ i,
      ReedSolomon.evalOnPoints domain (pivot - subspacePoly (subFinset (𝓛 i)))
        ∈ ListDecodable.closeCodewordsRel
            ((ReedSolomon.code domain k : Set (K → K)))
            (ReedSolomon.evalOnPoints domain pivot)
            (1 - (Fintype.card K : ℝ) ^ (β - 1)) :=
    fun i => mem_closeCodewordsRel_of_subspace domain hsurj pivot k (𝓛 i)
      q v hq hqcard (hdim i) hv (hdeg i) β hβv
  have hcount :=
    bkr06_family_close_codewords_card_ge domain hsurj pivot k
      (1 - (Fintype.card K : ℝ) ^ (β - 1)) 𝓛 hsmall hinj hclose
  calc (q : ℝ) ^ ((Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2)
      ≤ (Fintype.card ι : ℝ) := hbound
    _ ≤ _ := by exact_mod_cast hcount

/-! ## ABF26 T3.12 exponent form

`bkr06_close_codewords_card_ge_tight` restated in the bare T3.12 statement's
`q^{(α−β²)·log q}` exponent shape (`CodingTheory.rs_lambda_superpoly_extension_bkr06` /
its `_of_family` reduction in `ListDecoding/Bounds.lean`), at the explicit
`α := β² + (m·u − v²)/log q` — the exact `α`/`β` bookkeeping BKR06 performs under
`v ≈ β·m` and the `k = q^u` cutoff convention.  This is a **fully-proven, non-residual**
instance of the T3.12 close-codeword count at the extension parameters where the BKR06
construction actually lives.

**Remaining gap to the bare T3.12 front door** (the documented PARAMETER DEFECT /
base-parameter reconciliation, *not* claimed here):
* the bare statement's window is `k = ⌊q^α⌋` while the construction's is `k = q^u + 1`
  (needs close-codeword-count monotonicity in `k` along the nested RS codes, plus the
  floor bookkeeping `q^u + 1 ≤ ⌊q^α⌋` in the `β² < α` regime);
* the bare statement quantifies over abstract index types `ι` with `#ι = #F = q`
  (needs transport of the count along an equivalence `ι ≃ K`);
* the `α ≤ β²` regime of the bare statement (target `≤ q^0 = 1`) needs only a single
  exhibited close codeword and is not routed through the tight family. -/

/-- **ABF26 T3.12 [BKR06 Cor 2.2] — tight count in `q^{(α−β²)·log q}` exponent form,
fully proven.**  At the explicit `α := β² + (m·u − v²)/log q`, the constructed pivot's
close-codeword set in `RS[K, K, q^u + 1]` at radius `δ = 1 − (#K)^{β−1}` has at least
`q^{(α−β²)·log q}` elements — the bare T3.12 statement's count shape, with **every**
hypothesis of the chain discharged in-tree. -/
theorem rs_close_codewords_card_ge_bkr06_exponent_form
    (q : ℕ) (hq : 2 ≤ q) (hqcard : Fintype.card F = q)
    (v u : ℕ) (hv : v ≤ Module.finrank F K) (huv : u ≤ v)
    (hexp_nonneg : v ^ 2 ≤ Module.finrank F K * u) (hum : u < Module.finrank F K)
    (β : ℝ) (hβv : β * (Module.finrank F K : ℝ) ≤ (v : ℝ)) :
    ∃ pivot : K[X],
      (q : ℝ) ^ (((β ^ 2 + ((Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2) / Real.log q)
          - β ^ 2) * Real.log q) ≤
        ((ListDecodable.closeCodewordsRel
            ((ReedSolomon.code (Function.Embedding.refl K) (q ^ u + 1) : Set (K → K)))
            (ReedSolomon.evalOnPoints (Function.Embedding.refl K) pivot)
            (1 - (Fintype.card K : ℝ) ^ (β - 1))).ncard : ℝ) := by
  have hq1 : (1 : ℝ) < q := by exact_mod_cast Nat.lt_of_lt_of_le one_lt_two hq
  have hlogq : Real.log q ≠ 0 := (Real.log_pos hq1).ne'
  obtain ⟨pivot, hp⟩ :=
    bkr06_close_codewords_card_ge_tight q hq hqcard v u hv huv hexp_nonneg hum β hβv
  refine ⟨pivot, ?_⟩
  have hexp : ((β ^ 2 + ((Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2) / Real.log q)
      - β ^ 2) * Real.log q = (Module.finrank F K : ℝ) * u - (v : ℝ) ^ 2 := by
    field_simp
    ring
  rwa [hexp]

/-! ## Window monotonicity (gap (1) of the T3.12 base-parameter reconciliation)

The bare T3.12 statement's window is `k = ⌊q^α⌋`; the construction's is `k = q^u + 1`.
Reed-Solomon codes are nested in the degree bound (`ReedSolomon.code_mono`), so the
close-codeword set — and hence its count — is monotone in the window.  This transports
the proven tight count from the construction's window to any larger one. -/

/-- `closeCodewordsRel` is monotone in the code. -/
lemma closeCodewordsRel_mono_code {C C' : Set (K → K)} (h : C ⊆ C')
    (w : K → K) (δ : ℝ) :
    ListDecodable.closeCodewordsRel C w δ ⊆ ListDecodable.closeCodewordsRel C' w δ :=
  fun _ hc => ⟨h hc.1, hc.2⟩

/-- **Close-codeword count is monotone in the RS window.**  For `k ≤ k'`, the nested
codes `RS[K, domain, k] ⊆ RS[K, domain, k']` give
`|Λ(RS[k], w, δ)| ≤ |Λ(RS[k'], w, δ)|`. -/
theorem rs_closeCodewords_ncard_mono_window
    (domain : K ↪ K) (w : K → K) (δ : ℝ) {k k' : ℕ} (hk : k ≤ k') :
    (ListDecodable.closeCodewordsRel
        ((ReedSolomon.code domain k : Set (K → K))) w δ).ncard ≤
      (ListDecodable.closeCodewordsRel
        ((ReedSolomon.code domain k' : Set (K → K))) w δ).ncard :=
  Set.ncard_le_ncard
    (closeCodewordsRel_mono_code
      (fun _ hc => ReedSolomon.code_mono hk domain hc) w δ)
    (Set.toFinite _)

/-! ## The trivial regime `α ≤ β²` (gap (3))

When `α ≤ β²` the T3.12 count target `q^{(α−β²)·log q} ≤ q^0 = 1` is met by exhibiting
a *single* close codeword: the pivot word itself (at `pivot = 0`, the zero codeword is
`δ`-close to itself for any `δ ≥ 0`, and `δ = 1 − (#K)^{β−1} ≥ 0` for `β ≤ 1`).  No
tight family is needed in this regime. -/

/-- **T3.12 count shape, trivial regime `α ≤ β²` (fully proven).**  For `β ≤ 1` and
`α ≤ β²`, every RS window admits a pivot whose close-codeword set at
`δ = 1 − (#K)^{β−1}` meets the (≤ 1) count target `(#K)^{(α−β²)·log (#K)}`. -/
theorem rs_close_codewords_card_ge_trivial_regime
    (α β : ℝ) (hαβ : α ≤ β ^ 2) (hβ : β ≤ 1)
    (domain : K ↪ K) (k : ℕ) :
    ∃ pivot : K[X],
      (Fintype.card K : ℝ) ^ ((α - β ^ 2) * Real.log (Fintype.card K)) ≤
        ((ListDecodable.closeCodewordsRel
            ((ReedSolomon.code domain k : Set (K → K)))
            (ReedSolomon.evalOnPoints domain pivot)
            (1 - (Fintype.card K : ℝ) ^ (β - 1))).ncard : ℝ) := by
  refine ⟨0, ?_⟩
  have hK1 : (1 : ℝ) ≤ Fintype.card K := by
    exact_mod_cast Fintype.card_pos (α := K)
  -- the radius is nonnegative: `(#K)^{β−1} ≤ 1` for `β ≤ 1`
  have hδ0 : (0 : ℝ) ≤ 1 - (Fintype.card K : ℝ) ^ (β - 1) := by
    have := Real.rpow_le_one_of_one_le_of_nonpos hK1 (by linarith : β - 1 ≤ 0)
    linarith
  -- the zero codeword is in the close-codeword set of the zero received word
  have hmem : (0 : K → K) ∈ ListDecodable.closeCodewordsRel
      ((ReedSolomon.code domain k : Set (K → K)))
      (ReedSolomon.evalOnPoints domain 0)
      (1 - (Fintype.card K : ℝ) ^ (β - 1)) := by
    constructor
    · exact (ReedSolomon.code domain k).zero_mem
    · simp only [map_zero, ListDecodable.relHammingBall, Set.mem_setOf_eq,
        Code.relHammingDist, hammingDist_self]
      push_cast
      simpa using hδ0
  -- hence the count is at least one
  have hpos : 0 < (ListDecodable.closeCodewordsRel
      ((ReedSolomon.code domain k : Set (K → K)))
      (ReedSolomon.evalOnPoints domain 0)
      (1 - (Fintype.card K : ℝ) ^ (β - 1))).ncard :=
    Set.ncard_pos (Set.toFinite _) |>.mpr ⟨0, hmem⟩
  -- and the target is at most one
  have htarget : (Fintype.card K : ℝ) ^ ((α - β ^ 2) * Real.log (Fintype.card K)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hK1
      (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.log_nonneg hK1))
  calc (Fintype.card K : ℝ) ^ ((α - β ^ 2) * Real.log (Fintype.card K))
      ≤ 1 := htarget
    _ ≤ _ := by exact_mod_cast hpos

#print axioms BKR06.bkr06_param_ineq_extension
#print axioms BKR06.agreement_count_ge_card
#print axioms BKR06.mem_closeCodewordsRel_of_subspace
#print axioms BKR06.bkr06_close_codewords_card_ge_tight
#print axioms BKR06.rs_close_codewords_card_ge_bkr06_exponent_form
#print axioms BKR06.rs_closeCodewords_ncard_mono_window
#print axioms BKR06.rs_close_codewords_card_ge_trivial_regime

end BKR06
