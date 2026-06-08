/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-!
# Loop 22 — the `μ_d`-invariant subcode `{Q(X^d)}`: the object the open question lives in

(Companion to Loop 21, which independently showed a *single* symmetry orbit of size `≤ N=2^m` is
absorbed by the prize numerator — so a one-orbit symmetry disproof gives only linear growth and
fails. Loop 22 formalizes the *subcode* the multi-orbit / subgroup version of that question lives in.)

Loop 20 gave the smooth-domain RS automorphism group `μ_N` (scaling by roots of unity). Forcing a
large free orbit (disproof) needs an *intermediate* subgroup `μ_d` (`d ∣ N`): symmetric enough to
permute the list, not so transitive that invariant words collapse to constants. This file formalizes
the exact object that trade-off lives in: the **`μ_d`-invariant subcode**.

A polynomial fixed by the whole subgroup `μ_d` (scaling by every `d`-th root of unity) is exactly a
polynomial in `X^d`, i.e. `Q(X^d)`. We prove the invariance: for any `ζ` with `ζ^d = 1`,

    (Q(X^d)) ∘ (ζ·X) = Q(X^d).

So the `μ_d`-fixed degree-`<k` codewords are `{Q(X^d) : deg Q < k/d}` — a subcode of dimension
`≈ k/d`. The open question is then crisp: at a `μ_d`-invariant received word, are the close codewords
*also* `μ_d`-invariant (hence in this small `k/d`-dimensional subcode — *controlled*, proof lean), or
can a *non-invariant* close codeword exist (whose `μ_d`-orbit, size `∣ d`, all lies in the list ⇒
list `≥ d`, disproof lean)? Larger `d` shrinks the invariant subcode (more control) but raises the
transitivity (Loop 20). Per Loop 21, a single orbit is absorbed; the live question is whether *many*
`μ_d`-orbits of non-invariant close codewords coexist at radius `1−ρ−η`.

Sorry-free, axiom-clean. See `DISPROOF_LOG.md` (Loop22 — the `μ_d`-invariant subcode).
-/

namespace ArkLib.ProximityGap.StructureLoop22

open Polynomial

variable {F : Type*} [Field F]

/-- `X^d` scaled by `ζ` is `ζ^d · X^d`: `(X^d) ∘ (ζ·X) = (ζ·X)^d = C(ζ^d)·X^d`. -/
theorem xpow_comp_scale (d : ℕ) (ζ : F) :
    ((X : F[X]) ^ d).comp (C ζ * X) = C (ζ ^ d) * X ^ d := by
  rw [pow_comp, X_comp, mul_pow, ← C_pow]

/-- **`μ_d`-invariance of `Q(X^d)`.** For any `ζ` with `ζ^d = 1` (a `d`-th root of unity), scaling the
argument by `ζ` fixes every polynomial of the form `Q(X^d)`:

    (Q(X^d)) ∘ (ζ·X) = Q(X^d).

So `{Q(X^d)}` is exactly the `μ_d`-fixed subspace, and intersected with `deg < k` it is the
`μ_d`-invariant subcode `{Q(X^d) : deg Q < k/d}`. -/
theorem invariant_subcode_fixed (Q : F[X]) {d : ℕ} {ζ : F} (hζ : ζ ^ d = 1) :
    (Q.comp (X ^ d)).comp (C ζ * X) = Q.comp (X ^ d) := by
  rw [comp_assoc, xpow_comp_scale, hζ, map_one, one_mul]

/-- **The invariant subcode has the dimension of the `Q`-degrees: `deg Q(X^d) = d · deg Q`.** So
`deg Q(X^d) < k ⟺ deg Q < k/d`, confirming the `μ_d`-invariant subcode is `≈ k/d`-dimensional —
shrinking as the symmetry subgroup `μ_d` grows. -/
theorem invariant_subcode_natDegree (Q : F[X]) (d : ℕ) :
    (Q.comp (X ^ d)).natDegree = d * Q.natDegree := by
  rw [natDegree_comp, natDegree_X_pow, Nat.mul_comm]

end ArkLib.ProximityGap.StructureLoop22
