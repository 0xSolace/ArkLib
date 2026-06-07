/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2BijectionApply

/-!
# BCIKS20 Appendix A.4 — P2 assembly status anchor (issue #9)

Both sides of the carved core `RestrictedFaaDiBrunoMatch` are now explicit partition sums, all
proven in `P2BijectionApply`:

* LHS — `restrictedFaaDiBrunoSum_eq_partitionForm`;
* RHS — `coeff_succ_βHenselAssembled_partitionForm` / `restrictedMatch_rhs_eq_recursionPartitionForm`
  (`-ζ · coeff(t+1)(βHenselAssembled) = ζ · recSum / den`);
* α₀-Taylor identity — `hasseEvalAtRoot_eq_taylorSum`;
* Y-Hasse commutation — `evalX_hasseDeriv_Y_coeff`.

The genuine combinatorial core of the per-term identification — the order-`k` Hasse-derivative
evaluation `(hasseDeriv k p).eval a = ∑_i C(i,k)·p.coeff i·a^{i-k}` — is proven independently as
`Polynomial.hasseDeriv_eval_eq_sum` (`ArkLib/ToMathlib/Polynomial/HasseDerivEval.lean`).

The remaining P2 obligation is the per-`(i₁,λ)` term-level equality assembling these into
`RestrictedFaaDiBrunoMatch`; this file is a status anchor (no new content) to keep the milestone
explicit.  See issue #9.
-/

namespace BCIKS20.HenselNumerator.P2Assembly

-- Status anchor only; all assembly milestones are proven in `P2BijectionApply`.

end BCIKS20.HenselNumerator.P2Assembly
