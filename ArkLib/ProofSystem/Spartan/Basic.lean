/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.ConstraintSystem.R1CS

/-!
# Spartan compatibility module

The detailed Spartan PIOP sketch is not part of the current active local proof
surface. This module preserves the package import path used by `ArkLib.lean`
without asserting protocol-security theorems.
-/

namespace Spartan

noncomputable section

/-- The public parameters of the padded Spartan protocol. -/
structure PublicParams where
  /-- Number of bits in the row dimension. -/
  l_m : Nat
  /-- Number of bits in the full variable dimension. -/
  l_n : Nat
  /-- Number of bits in the witness dimension. -/
  l_w : Nat
  /-- The witness dimension is at most the full variable dimension. -/
  l_w_le_l_n : l_w <= l_n

namespace PublicParams

/-- The R1CS dimensions/sizes are the powers of two of the public parameters. -/
def toSizeR1CS (pp : PublicParams) : R1CS.Size where
  m := 2 ^ pp.l_m
  n := 2 ^ pp.l_n
  n_w := 2 ^ pp.l_w
  n_w_le_n := Nat.pow_le_pow_of_le (by decide) pp.l_w_le_l_n

end PublicParams

end

end Spartan
