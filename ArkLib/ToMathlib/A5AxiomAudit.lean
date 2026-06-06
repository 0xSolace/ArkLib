import ArkLib.ToMathlib.GK16Claim16Witness
import ArkLib.ToMathlib.GK16Claim16Core
import ArkLib.ToMathlib.GK16BudgetCoeff
import ArkLib.Data.CodingTheory.ProximityGap.GK16RootCounting
import ArkLib.Data.CodingTheory.ProximityGap.GK16Lemma12
import ArkLib.Data.CodingTheory.ProximityGap.GK16DegreeBudget
import ArkLib.Data.CodingTheory.ProximityGap.GK16Wronskian
import ArkLib.Data.CodingTheory.ProximityGap.GK16FrsTransport
import ArkLib.Data.CodingTheory.ProximityGap.GK16Claim16Transport
import ArkLib.ToMathlib.GSFactorData
import ArkLib.Data.CodingTheory.ProximityGap.GSFactorExtract
import ArkLib.Data.CodingTheory.ProximityGap.VandermondeMCAExtract
import ArkLib.ToMathlib.HcardDischarge

open ArkLib.FRS.GK16

#print axioms claim16_rootMultiplicity_ge
#print axioms le_rootMultiplicity_det_of_col_dvd
#print axioms Polynomial.coeff_prod_sum_of_natDegree_le
#print axioms ArkLib.FRS.GK16.foldedWronskian_ne_zero_of_linearIndependent
#print axioms ArkLib.FRS.GK16.gk16Lemma12HardResidual_holds
#print axioms ArkLib.FRS.GK16.sum_rootMultiplicity_foldedWronskian_le
#print axioms ArkLib.FRS.GK16.sum_rootMultiplicity_le_natDegree
