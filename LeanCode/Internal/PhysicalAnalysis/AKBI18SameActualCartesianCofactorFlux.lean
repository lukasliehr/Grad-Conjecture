import AKBI17OriginalAdjugateFluxAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
open scoped BigOperators
namespace Grad.OriginalKernelHomogeneousGraph
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.NonlinearProduct Grad.SourceCollar Grad.FinitePhysicalJetLift Grad.AxisSplit
open Grad.OriginalKernelCovariantRecovery Grad.OriginalKernelRetainedDecay
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollarCoefficients

def originalCartesianCofactorFluxCore {parameters : PhaseParameters} (length : ℝ)
    (state : QuotientState parameters) (vector : ACore parameters 3) : ACore parameters 3 :=
  originalScalarTripletCore ![(length : ℂ)⁻¹ • originalAffineCofactorFluxCore length state vector 0,
    (length : ℂ)⁻¹ • originalAffineCofactorFluxCore length state vector 1,
    originalAffineCofactorFluxCore length state vector 2]

/-- Literal B_C(F_C^T U) equals the normalized adjugate flux of the SAME
original state, on the whole closed disk and at the original width. -/
theorem originalCartesianCofactorFlux_value (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (nonzero : length≠0) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6≤originalCoefficientLowRadius parameters length)
    (state : QuotientState parameters) (sameBase : state.2.1=planarReferenceCore parameters+base)
    (sameEpsilon : state.1=(epsilon : ℂ)) (vector : ACore parameters 3) (point : ClosedDisk) (angle : ℝ) :
    WithLp.toLp 2 ((originalPhysicalSignedCofactor parameters length epsilon base angle point).mulVec
      ((originalPhysicalFrameMatrix parameters length epsilon base angle point).transpose.mulVec (coreValue vector point angle)))=
      coreValue (originalCartesianCofactorFluxCore length state vector) point angle := by
  let frame := originalPhysicalFrameMatrix parameters length epsilon base angle point
  have inverse : frame*frame⁻¹=1 := by
    rw [← originalInverseFamily_eq_matrixInverse parameters length rho epsilon base small 0 angle point]
    exact (originalInverseFamily_matrix_identity parameters length epsilon base
      (originalCoefficient_low_margin parameters length rho epsilon base small).2.2 0 angle point).1
  have firstColumn : physicalColumn frame 0=coreValue (partialCore parameters 0 state.2.1) point angle := by
    rw [sameBase]
    apply PiLp.ext
    intro component
    exact (originalTotalFirstDerivative_frame parameters length epsilon base 0 point angle component).symm
  have secondColumn : physicalColumn frame 1=coreValue (partialCore parameters 1 state.2.1) point angle := by
    rw [sameBase]
    apply PiLp.ext
    intro component
    exact (originalTotalFirstDerivative_frame parameters length epsilon base 1 point angle component).symm
  have affine : affineStateCore parameters length state=
      affineStateCore parameters length ((epsilon : ℂ),planarReferenceCore parameters+base,0) := by
    change timeDerivativeCore parameters state.2.1+state.1 • valueMapCore parameters tangentGeneratorMap state.2.1+
      (length : ℂ) • eTConstantCore parameters=_
    rw [sameBase,sameEpsilon]
    rfl
  have thirdColumn : physicalColumn frame 2=(length : ℂ)⁻¹ • coreValue (affineStateCore parameters length state) point angle := by
    rw [affine]
    apply PiLp.ext
    intro component
    exact originalFrame_axialColumn parameters length epsilon nonzero base point angle component
  have first := determinant_replace_first frame frame⁻¹ inverse (coreValue vector point angle)
  have second := determinant_replace_second frame frame⁻¹ inverse (coreValue vector point angle)
  have third := originalDeterminant_replace_third frame frame⁻¹ inverse (coreValue vector point angle)
  rw [secondColumn,thirdColumn,complexDeterminant_smul_third,← coreValue_determinantOperation] at first
  rw [firstColumn,thirdColumn,complexDeterminant_smul_third,← coreValue_determinantOperation] at second
  rw [firstColumn,secondColumn,← coreValue_determinantOperation] at third
  change WithLp.toLp 2 ((frame.det • (frame⁻¹*(frame⁻¹).transpose)).mulVec (frame.transpose.mulVec (coreValue vector point angle)))=_
  rw [originalSignedCofactor_action frame frame⁻¹ inverse]
  apply PiLp.ext
  intro component
  rw [originalCartesianCofactorFluxCore,originalScalarTripletCore_value]
  fin_cases component
  · change frame.det*matrixOperator frame⁻¹ (coreValue vector point angle) 0=
      coreValue ((length : ℂ)⁻¹ • determinantOperation parameters vector (partialCore parameters 1 state.2.1)
        (affineStateCore parameters length state)) point angle 0
    rw [coreValue_smul]
    exact first.symm
  · change frame.det*matrixOperator frame⁻¹ (coreValue vector point angle) 1=
      coreValue ((length : ℂ)⁻¹ • determinantOperation parameters (partialCore parameters 0 state.2.1) vector
        (affineStateCore parameters length state)) point angle 0
    rw [coreValue_smul]
    exact second.symm
  · exact third.symm

end Grad.OriginalKernelHomogeneousGraph
