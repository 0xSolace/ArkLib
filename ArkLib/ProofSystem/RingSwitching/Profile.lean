/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Prelude

/-!
# Ring-Switching Profile

The `RingSwitchingProfile` abstraction captures the packing-layer data that every ring-switching
reduction needs, so that the protocol skeleton can be written once and instantiated by Binius
(DP24), Hachi (NOZ26 / ePrint 2026/156), and future small-ring/large-ring PCS work.

It is a `structure` passed **explicitly** (not a `class`): distinct profiles may share the same
carriers `(B, L, κ)` (e.g. with different bases), so instance resolution would be ambiguous.

It is stated over `CommRing` (not `Field`): Hachi's carrier `L = R_q` is not a field. The
`Field`-only steps (Schwartz–Zippel over `|L|`) stay at the soundness use-sites in the
ring-switching files, not here.

## Fields and their two instantiations

| field | Binius (DP24) | Hachi (ePrint 2026/156) |
|---|---|---|
| `B`, `L` | small field `K`, tower field `L` | `R_q^H ≅ F_{q^k}`, `R_q` |
| `basis` | binary `K`-basis of `L`, rank `2^κ` | `ψ` of Theorem 2, rank `d/k = 2^κ` |
| `A` | tensor algebra `L ⊗[K] L` | `R_q` itself (`= L`) |
| `φ₀`, `φ₁` | `α ↦ α ⊗ 1`, `α ↦ 1 ⊗ α` | `id`, the automorphism `σ₋₁` |
| `decomposeRows`/`Columns` | `L`-coords of `ŝ` in `L ⊗_K L` | coords of `Y ∈ R_q` via `ψ` |

The only structural difference — Hachi has no separate tensor object (`A = L`, `φ₀ = id`,
`φ₁ = σ₋₁`) while Binius has `A = L ⊗_K L` — is absorbed by `A`, `φ₀`, `φ₁` being explicit fields.
The eq̃/trace inner-product law (DP24 §2.5 / Hachi Theorem 2) is deferred: it is added when the
protocol code is rewired through the profile (it is the property the step-2/5/9 checks rely on).
-/

noncomputable section

namespace RingSwitching

open Module
open scoped TensorProduct

/-- The packing-layer data a ring-switching reduction abstracts over. `L` is free of rank `2^κ`
over the small ring `B` (via `basis`); `A` is the pack/trace carrier where the folded element `ŝ`
lives (and which the batching phase sends on the wire). See the module docstring for the Binius and
Hachi instantiations of each field. -/
structure RingSwitchingProfile (B L : Type) (κ : ℕ)
    [CommRing B] [CommRing L] [Algebra B L] where
  /-- rank-`2^κ` `B`-basis of `L`. -/
  basis : Basis (Fin κ → Fin 2) B L
  /-- pack/trace carrier; Binius `L ⊗[K] L`, Hachi `R_q` (`= L`). The batching wire type. -/
  A : Type
  [commRingA : CommRing A]
  [algLA : Algebra L A]
  /-- column embedding `L → A`; Binius `α ↦ α ⊗ 1`, Hachi `id`. -/
  φ₀ : L →+* A
  /-- row embedding `L → A`; Binius `α ↦ 1 ⊗ α`, Hachi the automorphism `σ₋₁`. -/
  φ₁ : L →+* A
  /-- `L`-coordinates of an `A`-element via the φ₁-side rank-`2^κ` `L`-module structure on `A`. -/
  decomposeRows : A → (Fin κ → Fin 2) → L
  /-- `L`-coordinates of an `A`-element via the φ₀-side rank-`2^κ` `L`-module structure on `A`. -/
  decomposeColumns : A → (Fin κ → Fin 2) → L

attribute [instance] RingSwitchingProfile.commRingA RingSwitchingProfile.algLA

/-- The Binius (binary-tower) instantiation of `RingSwitchingProfile`, built from the existing
tensor-algebra definitions in `Prelude.lean`. This is the compile-level validation that the profile
shape fits the real Binius data: `A := L ⊗[K] L`, embeddings `φ₀ = · ⊗ 1` / `φ₁ = 1 ⊗ ·`, and the
decompositions are the `K`-basis coordinates via the left/right `L`-module structures. -/
def binaryTowerProfile (κ : ℕ) [NeZero κ] (K L : Type)
    [Field K] [Field L] [Algebra K L] (β : Basis (Fin κ → Fin 2) K L) :
    RingSwitchingProfile K L κ where
  basis := β
  A := TensorAlgebra K L
  commRingA := inferInstanceAs (CommRing (L ⊗[K] L))
  algLA := Algebra.TensorProduct.leftAlgebra
  φ₀ := φ₀ L K
  φ₁ := φ₁ L K
  decomposeRows := fun s => decompose_tensor_algebra_rows (L := L) (K := K) (β := β) s
  decomposeColumns := fun s => decompose_tensor_algebra_columns (L := L) (K := K) (β := β) s

end RingSwitching

end
