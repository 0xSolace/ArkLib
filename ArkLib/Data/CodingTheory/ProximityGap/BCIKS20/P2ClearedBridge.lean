import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2FubiniReabsorb
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.P2ClearedGap

namespace BCIKS20.HenselNumerator
open Polynomial Polynomial.Bivariate
variable {F : Type} [Field F]
variable (H : F[X][Y]) [Fact (Irreducible H)] [Fact (0 < H.natDegree)]

#check hasseEvalAtRoot_mul_W_pow_eq_embedding_cleared
end BCIKS20.HenselNumerator
