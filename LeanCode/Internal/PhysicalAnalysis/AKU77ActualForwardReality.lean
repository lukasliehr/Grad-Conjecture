import AKU76SharpOriginalJFPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 3000
open scoped ComplexConjugate
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.QuotientProjection Grad.NonlinearRange Grad.NonlinearProduct Grad.CompletedReality

/-- The actual eta-zero derivative as a complex linear map in its two fields. -/
def physicalEtaZeroLinear (parameters : PhaseParameters) (length : ℝ) (base : QuotientState parameters) :
    (ACore parameters 3 × ACore parameters 1) →ₗ[ℂ] QuotientRows parameters where
  toFun pair := physicalEtaZeroRows parameters length base pair.1 pair.2
  map_add' first second := by
    funext row
    fin_cases row
    all_goals simp [physicalEtaZeroRows,physicalVariationRadialCorrection,physicalVariationAffine,
      map_add,LinearMap.add_apply]
    all_goals abel
  map_smul' scalar pair := by
    funext row
    fin_cases row
    all_goals simp [physicalEtaZeroRows,physicalVariationRadialCorrection,physicalVariationAffine,
      map_smul,LinearMap.smul_apply,smul_add,smul_sub,smul_comm scalar base.1]

/-- The original operator commutes with physical real conjugation at a real
current. Spin rows swap, while determinant and scalar rows do not. -/
theorem physicalEtaZeroRows_conjugate (parameters : PhaseParameters) (length : ℝ)
    (base : QuotientState parameters) (scalarReal : conj base.1 = base.1)
    (fieldReal : cartesianCoreConjugation parameters base.2.1 = base.2.1)
    (vector : ACore parameters 3) (scalar : ACore parameters 1) :
    zCoreConjugation parameters (physicalEtaZeroRows parameters length base vector scalar) =
      physicalEtaZeroRows parameters length base
        (cartesianCoreConjugation parameters vector) (cartesianCoreConjugation parameters scalar) := by
  have affineReal := affineStateCore_real length base scalarReal fieldReal
  have variation : cartesianCoreConjugation parameters (physicalVariationAffine base.1 vector) =
      physicalVariationAffine base.1 (cartesianCoreConjugation parameters vector) := by
    rw [physicalVariationAffine,map_add,timeDerivativeCore_conjugate,coreConjugation_complex_smul,
      valueMapCore_conjugate tangentGeneratorMap tangentGeneratorMap_conjugate,scalarReal]
    rfl
  have radial : cartesianCoreConjugation parameters (physicalVariationRadialCorrection base.2.1 vector) =
      physicalVariationRadialCorrection base.2.1 (cartesianCoreConjugation parameters vector) := by
    rw [physicalVariationRadialCorrection,map_add,quotientDotCurried_conjugate,quotientDotCurried_conjugate,fieldReal]
    rfl
  funext row
  fin_cases row
  · change cartesianCoreConjugation parameters
      (partialMinusCore parameters scalar -
        dotOperation parameters (partialMinusCore parameters vector) (rotationCore parameters base.2.1) -
        dotOperation parameters (partialMinusCore parameters base.2.1) (rotationCore parameters vector) +
        starZMulCore parameters (physicalVariationRadialCorrection base.2.1 vector)) = _
    rw [map_add,map_sub,map_sub,partialMinusCore_conjugate,dotOperation_conjugate,partialMinusCore_conjugate,rotationCore_conjugate,
      dotOperation_conjugate,partialMinusCore_conjugate,rotationCore_conjugate,starZMulCore_conjugate,fieldReal,radial]
    rfl
  · change cartesianCoreConjugation parameters
      (partialPlusCore parameters scalar -
        dotOperation parameters (partialPlusCore parameters vector) (rotationCore parameters base.2.1) -
        dotOperation parameters (partialPlusCore parameters base.2.1) (rotationCore parameters vector) +
        zMulCore parameters (physicalVariationRadialCorrection base.2.1 vector)) = _
    rw [map_add,map_sub,map_sub,partialPlusCore_conjugate,dotOperation_conjugate,partialPlusCore_conjugate,rotationCore_conjugate,
      dotOperation_conjugate,partialPlusCore_conjugate,rotationCore_conjugate,zMulCore_conjugate,fieldReal,radial]
    rfl
  · change cartesianCoreConjugation parameters (removeAngularCore parameters
      (determinantOperation parameters (partialCore parameters 0 vector) (partialCore parameters 1 base.2.1)
          (affineStateCore parameters length base) +
        determinantOperation parameters (partialCore parameters 0 base.2.1) (partialCore parameters 1 vector)
          (affineStateCore parameters length base) +
        determinantOperation parameters (partialCore parameters 0 base.2.1) (partialCore parameters 1 base.2.1)
          (physicalVariationAffine base.1 vector))) = _
    rw [removeAngularCore_conjugate,(cartesianCoreConjugation parameters).map_add,(cartesianCoreConjugation parameters).map_add,determinantOperation_conjugate,determinantOperation_conjugate,
      determinantOperation_conjugate,partialCore_conjugate,partialCore_conjugate,partialCore_conjugate,
      partialCore_conjugate,fieldReal,affineReal,variation]
    rfl
  · change cartesianCoreConjugation parameters (removeAngularCore parameters
      (dotOperation parameters (rotationCore parameters vector) (affineStateCore parameters length base) +
        dotOperation parameters (rotationCore parameters base.2.1) (physicalVariationAffine base.1 vector) -
        timeDerivativeCore parameters scalar)) = _
    rw [removeAngularCore_conjugate,map_sub,map_add,dotOperation_conjugate,dotOperation_conjugate,
      rotationCore_conjugate,rotationCore_conjugate,timeDerivativeCore_conjugate,fieldReal,affineReal,variation]
    rfl

end Grad.FinitePhysicalJetLift
