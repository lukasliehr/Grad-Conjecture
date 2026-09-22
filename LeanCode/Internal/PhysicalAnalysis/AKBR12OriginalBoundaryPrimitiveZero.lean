import AKBR11ActualOriginalHighBoundaryZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalKernelOuterUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Cor18 Grad.PhysicalCoordinates
open Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularCrossMaps
open Grad.AnnularOriginalSmoothCore Grad.OriginalKernelCovariantRecovery Grad.ActualSmoothPhysicalField

variable (parameters : PhaseParameters) (compact : ℝ)
    (state : RetainedInverseState parameters parameters.length compact)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (vector : ACore parameters 3)
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)
    (constrained : VectorConstraints parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed
      (toPhysicalCore parameters vector))

include insideSeed constrained

/-- The complete primitive outer row is zero once its SAME covariant is
the actual original constrained field. The derivative and mean are literal. -/
theorem originalTupleBoundaryPrimitive_zero (tuple : OriginalSmoothTuple parameters lower)
    (recovery : tupleCovariantTrace parameters parameters.length compact lower positive state tuple ⟨1,bounded.le,le_rfl⟩=
      originalCurveNegativeTrace
        (originalPolarCovariantCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low
          lower positive bounded vector) ⟨1,bounded.le,le_rfl⟩) :
    lowStateBoundaryPR parameters parameters.length compact state
      (tupleNormalizedInput parameters lower positive tuple ⟨1,bounded.le,le_rfl⟩)=0 := by
  let input := tupleNormalizedInput parameters lower positive tuple ⟨1,bounded.le,le_rfl⟩
  have phase : radialKernelParameters parameters (tupleRadius lower positive ⟨1,bounded.le,le_rfl⟩)=parameters := radialKernelParameters_one parameters
  have supported : IsAngularMeanFree parameters 0 0 (input 0) := by
    change IsAngularMeanFree parameters 0 0 ((tupleNormalizedInput parameters lower positive tuple ⟨1,bounded.le,le_rfl⟩) 0)
    rw [originalTupleNormalized_outer parameters lower positive bounded tuple]
    have original := tupleSevenInput_supported parameters lower positive tuple ⟨1,bounded.le,le_rfl⟩
    rw [phase] at original
    exact original
  have derivative : IsAngularDerivative parameters 0 0 (input 3) (input 1) := by
    change IsAngularDerivative parameters 0 0 ((tupleNormalizedInput parameters lower positive tuple ⟨1,bounded.le,le_rfl⟩) 3)
      ((tupleNormalizedInput parameters lower positive tuple ⟨1,bounded.le,le_rfl⟩) 1)
    rw [originalTupleNormalized_outer parameters lower positive bounded tuple]
    have original := tupleSevenInput_scalarDerivative parameters lower positive tuple ⟨1,bounded.le,le_rfl⟩
    rw [phase] at original
    exact original
  have covariant := (originalTupleCovariant_outer parameters parameters.length compact lower positive bounded state tuple).symm.trans recovery
  apply highBoundaryPrimitiveTrace_injective parameters 0 0
  have primitive := actualPhysicalBoundaryPR_eq_high parameters parameters.length state.boundaryState.val.rho state.boundaryState.val.alpha
    state.boundaryState.val.delta state.boundaryState.val.parameter state.boundaryState.val.epsilon compact state.boundaryState.val.field
    state.boundaryState.property state.boundaryState.val.compactNonnegative state.boundaryState.val.alphaSmall state.boundaryState.val.deltaSmall
    state.boundaryState.val.parameterSmall 0 0 input supported derivative
  apply primitive.trans
  have zeroTrace : highBoundaryPrimitiveTrace parameters 0 0 0=0 := by simp [highBoundaryPrimitiveTrace]
  rw [zeroTrace]
  unfold actualHighPhysicalBoundary fullSevenSlotKernelAction actualHighPhysicalBoundaryKernel
  simp only [ContinuousLinearMap.comp_apply,fullNegativeKernelAction_comp]
  change fullNegativeKernelAction parameters 0 0 (highAngularKernel parameters 1)
    (fullNegativeKernelAction parameters 0 0
      (actualBoundaryMultiplier parameters parameters.length state.val.val.rho state.val.val.alpha state.val.val.delta state.val.val.parameter
        state.val.val.epsilon compact state.val.val.field state.val.val.compactNonnegative state.val.val.alphaSmall state.val.val.deltaSmall
        state.val.val.parameterSmall state.boundaryState.coefficientSmall)
      (fullNegativeKernelAction parameters 0 0 state.boundaryState.covariant (sevenSlotFlatten parameters 0 0 input)))=0
  rw [covariant]
  exact originalDomain_actualHighBoundary_zero parameters compact state lower positive bounded vector insideSeed constrained

end Grad.OriginalKernelOuterUniqueness
