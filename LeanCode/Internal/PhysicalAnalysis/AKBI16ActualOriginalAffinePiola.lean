import AKBI15OriginalDeterminantAxialDifferentiation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
open Set Filter
open scoped BigOperators
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.NonlinearProduct Grad.SourceCollar Grad.FinitePhysicalJetLift Grad.AxisSplit
open Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelRetainedDecay

/-- The original unnormalized three adjugate flux components. Planar
components acquire exactly 1/L in the actual Cartesian frame. -/
def originalAffineCofactorFluxCore {parameters : PhaseParameters} (length : ℝ)
    (state : QuotientState parameters) (vector : ACore parameters 3) : Fin 3 → ACore parameters 1 :=
  ![determinantOperation parameters vector (partialCore parameters 1 state.2.1) (affineStateCore parameters length state),
    determinantOperation parameters (partialCore parameters 0 state.2.1) vector (affineStateCore parameters length state),
    determinantOperation parameters (partialCore parameters 0 state.2.1) (partialCore parameters 1 state.2.1) vector]

theorem originalAffine_partial {parameters : PhaseParameters} (length : ℝ) (state : QuotientState parameters) (direction : Fin 2) :
    partialCore parameters direction (affineStateCore parameters length state)=
      timeDerivativeCore parameters (partialCore parameters direction state.2.1)+
      state.1 • valueMapCore parameters tangentGeneratorMap (partialCore parameters direction state.2.1) := by
  simp only [affineStateCore,map_add,map_smul,← originalTime_partial,partialCore_valueMap,
    eTConstantCore,originalConstant_partial,smul_zero,add_zero,stateField,stateScalar]
  rfl

/-- Actual affine Piola on the SAME original all-grade core. The toroidal
rotation terms cancel with the divergence of the genuine adjugate flux. -/
theorem originalAffine_piola {parameters : PhaseParameters} (length : ℝ) (state : QuotientState parameters)
    (vector : ACore parameters 3) :
    partialCore parameters 0 (originalAffineCofactorFluxCore length state vector 0)+
      partialCore parameters 1 (originalAffineCofactorFluxCore length state vector 1)+
      timeDerivativeCore parameters (originalAffineCofactorFluxCore length state vector 2)=
    determinantOperation parameters (partialCore parameters 0 vector) (partialCore parameters 1 state.2.1) (affineStateCore parameters length state)+
      determinantOperation parameters (partialCore parameters 0 state.2.1) (partialCore parameters 1 vector) (affineStateCore parameters length state)+
      determinantOperation parameters (partialCore parameters 0 state.2.1) (partialCore parameters 1 state.2.1) (physicalVariationAffine state.1 vector) := by
  simp only [originalAffineCofactorFluxCore,Matrix.cons_val,originalDeterminant_partial,originalDeterminant_time,
    originalAffine_partial,partialCore_commute 1 0,physicalVariationAffine]
  apply coreValue_ext
  intro point angle
  apply PiLp.ext
  intro coordinate
  have only : coordinate=0 := Subsingleton.elim _ _
  subst coordinate
  simp only [coreValue_add,PiLp.add_apply,coreValue_determinantOperation,coreValue_smul,coreValue_valueMap,
    tangentGeneratorMap_value,Grad.NonlinearQuotient.complexDeterminant_eq,
    Grad.NonlinearQuotient.complexTangentGenerator,PiLp.smul_apply,smul_eq_mul,Matrix.cons_val]
  ring

/-- The literal homogeneous quotient determinant row is exactly zero
projected divergence of this SAME original adjugate-frame flux. -/
theorem originalHomogeneous_affinePiola {parameters : PhaseParameters} (length : ℝ) (state : QuotientState parameters)
    (vector : ACore parameters 3) (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 state ![(0,vector,scalar)]=0) :
    removeAngularCore parameters (partialCore parameters 0 (originalAffineCofactorFluxCore length state vector 0)+
      partialCore parameters 1 (originalAffineCofactorFluxCore length state vector 1)+
      timeDerivativeCore parameters (originalAffineCofactorFluxCore length state vector 2))=0 := by
  rw [originalAffine_piola]
  have actual := congrFun homogeneous (2 : Fin 4)
  rw [quotientRowsDerivative_etaZero] at actual
  exact actual

end Grad.OriginalKernelHomogeneousGraph
