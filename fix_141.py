import re

with open('ArkLib/Data/CodingTheory/ProximityGap/GrandChallenge141PrizeMath.lean', 'r') as f:
    content = f.read()

# We want to remove the sections that are now obsolete
# Everything between `/-! ## 2. The per-input GS prize form is a theorem` and `/-! ## 3. Reduction` 
# Wait, let's just use Python's replace

# Remove the text `epsMCAgs_prizeBound_conjecture_holds` from axioms
content = content.replace('#print axioms epsMCAgs_prizeBound_conjecture_holds\n', '')
content = content.replace('#print axioms epsMCAgs_prizeBound_conjecture_of_uniformConjecture\n', '')
content = content.replace('#print axioms exists_epsMCAgsMassBound_of_prizeBound_conjecture\n', '')
content = content.replace('#print axioms epsMCAgs_prizeBound_conjecture_of_uniform_epsMCAgsMassBound\n', '')
content = content.replace('#print axioms epsMCAgs_prizeBound_conjecture_iff_uniform_epsMCAgsMassBound\n', '')

# Replace epsMCAgs_prizeBound_of_listSize_clears
old_reduction = """theorem epsMCAgs_prizeBound_of_listSize_clears
    (domain : ι ↪ F) (j : Fin 4) (m : ℕ) (η δ : ℝ≥0) (hη : 0 < η)
    (L : WordStack F (Fin 2) ι → Finset (ι → F))
    (hδ : (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ))
    (ℓ : ℕ) (c₁ c₂ c₃ : ℝ)
    (hcov : ∀ u, PivotCovering (F := F)
      ((ReedSolomon.code (domain := domain)
        ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) δ L u)
    (hsize : ∀ u, (L u).card ≤ ℓ)
    (hclear : ((ℓ : ENNReal) / (Fintype.card F : ENNReal)) ≤
      ENNReal.ofReal
        (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η c₁ c₂ c₃)) :
    epsMCAgs_prizeBound_conjecture domain j m η δ hη L hδ :=
  ⟨c₁, c₂, c₃,
    le_trans
      (epsMCAgs_le_listSize_div_of_pivotCovering
        (F := F) _ δ L ℓ hcov hsize)
      hclear⟩"""

new_reduction = """theorem epsMCAgs_prizeBound_of_listSize_clears
    (domain : ι ↪ F) (m : ℕ)
    (ℓ : Fin 4 → ℝ≥0 → ℝ≥0 → (WordStack F (Fin 2) ι → Finset (ι → F)) → ℕ)
    (c₁ c₂ c₃ : ℝ)
    (hcov : ∀ (j : Fin 4) (η δ : ℝ≥0) (hη : 0 < η)
      (hδ : (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ))
      (L : WordStack F (Fin 2) ι → Finset (ι → F)) (u : WordStack F (Fin 2) ι),
      PivotCovering (F := F)
        ((ReedSolomon.code (domain := domain)
          ⌊(ProximityGap.prizeRates j : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))) δ L u)
    (hsize : ∀ (j : Fin 4) (η δ : ℝ≥0) (hη : 0 < η)
      (hδ : (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ))
      (L : WordStack F (Fin 2) ι → Finset (ι → F)) (u : WordStack F (Fin 2) ι),
      (L u).card ≤ ℓ j η δ L)
    (hclear : ∀ (j : Fin 4) (η δ : ℝ≥0) (hη : 0 < η)
      (hδ : (δ : ℝ) ≤ 1 - (ProximityGap.prizeRates j : ℝ) - (η : ℝ))
      (L : WordStack F (Fin 2) ι → Finset (ι → F)),
      ((ℓ j η δ L : ENNReal) / (Fintype.card F : ENNReal)) ≤
        ENNReal.ofReal
          (epsMCAgsPrizeBound (Fintype.card F) m (ProximityGap.prizeRates j) η c₁ c₂ c₃)) :
    epsMCAgs_prizeBound_conjecture domain m := by
  refine ⟨c₁, c₂, c₃, ?_⟩
  intro j η δ hη hδ L
  exact le_trans
    (epsMCAgs_le_listSize_div_of_pivotCovering
      (F := F) _ δ L (ℓ j η δ L) (hcov j η δ hη hδ L) (hsize j η δ hη hδ L))
    (hclear j η δ hη hδ L)"""

content = content.replace(old_reduction, new_reduction)

# Now remove the block from line 108 up to line 276
start_marker = "/-- A prize rate is strictly positive:"
end_marker = "theorem exists_prize_mcaLowerWitness_of_uniformConjecture"
start_idx = content.find(start_marker)
end_idx = content.find(end_marker)

if start_idx != -1 and end_idx != -1:
    content = content[:start_idx] + content[end_idx:]

with open('ArkLib/Data/CodingTheory/ProximityGap/GrandChallenge141PrizeMath.lean', 'w') as f:
    f.write(content)

