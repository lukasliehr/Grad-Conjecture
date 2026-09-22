import AKAR32OriginalFluxDecay

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.OriginalKernelRetainedDecay.Consumer
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.FinitePhysicalJetLift Grad.OriginalFlatAxisDecay
open Grad.SourceCollar Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularReconstruction Grad.ActualSmoothPhysicalField Grad.AnnularSmoothCore Grad.SourceCollarFullSource

theorem actualFlux_cartesian_formula (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (radius : RadialPoint) (vector : ℝ × ℝ → ComplexEuclidean 3) (xi : ℝ × ℝ → ComplexEuclidean 1)
    (angles : ℝ × ℝ) :
    originalPhysicalRawFlux parameters length epsilon base radius vector xi angles =
      let point := Grad.SourceCollarDivision.polarClosedPoint radius.val angles.1 radius.property.1 radius.property.2
      let frame := originalPhysicalFrameMatrix parameters length epsilon base angles.2 point
      let inverse := familyMatrix (originalInverseFamily parameters length epsilon base) 0 angles.2 point
      originalPolarRadialValue (WithLp.toLp 2 ((frame.det • inverse).mulVec (vector angles))) angles.1+
      originalPolarTangentialValue (WithLp.toLp 2 ((frame.det • (inverse*inverse.transpose)).mulVec
        (originalPolarRadialVector ((radius.val : ℂ)⁻¹ • xi angles) angles.1))) angles.1 := by
  have low := (originalAxis_primitive_margin parameters length rho epsilon base small).1
  unfold originalPhysicalRawFlux
  rw [physicalMatrixProduct_apply,physicalMatrixProduct_apply,
    originalCofactorCovectorFamily_matrix parameters length rho epsilon base low,
    originalCofactorFamily_matrix parameters length rho epsilon base low]

/-- Exact original smooth-domain consumer: the literal quotient derivative
vanishes, U has the original Cartesian first jets zero, and every retained
field and norm uses that SAME U, S, state and analytic width. -/
theorem originalSmooth_kernel_retained_decay (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 8 ≤ originalCoefficientLowRadius parameters length)
    (state : QuotientState parameters) (sameBase : state.2.1=planarReferenceCore parameters+base)
    (vector : GradeCore parameters 3 4) (flat : ∀ cell, ZeroCartesianFirstJets (vector.toCore.val cell))
    (scalar : ACore parameters 1)
    (homogeneous : quotientRowsDerivative parameters length 1 state ![(0,vector.toCore,scalar)] = 0)
    (radius : RadialPoint) (positive : 0<radius.val) :
    let xi := originalCoreCircleTrace parameters (originalKernelXi state.2.1 vector.toCore scalar) radius
    let rotatedXi := originalCoreCircleTrace parameters (rotationCore parameters (originalKernelXi state.2.1 vector.toCore scalar)) radius
    let p := originalKernelPhysicalP parameters length rho epsilon base small radius state.2.1 vector.toCore scalar
    let x := originalKernelPhysicalX parameters length rho epsilon base small radius state.2.1 vector.toCore scalar
    OriginalCircleRepresents parameters radius p
      (removePolarMean (originalPhysicalRawFlux parameters length epsilon base radius
        (originalCoreCircle parameters vector.toCore radius)
        (originalCoreCircle parameters (originalKernelXi state.2.1 vector.toCore scalar) radius))) ∧
    OriginalCircleRotation p x ∧
    ‖xi‖≤originalScalarDecayConstant parameters length*radius.val^(5/2:ℝ)*‖vector‖ ∧
    ‖rotatedXi‖≤originalScalarDecayConstant parameters length*radius.val^(5/2:ℝ)*‖vector‖ ∧
    ‖x‖≤originalFluxDecayConstant parameters length*radius.val^(3/2:ℝ)*‖vector‖ := by
  have scalarDecay := originalKernelXi_scalar_decay parameters length rho epsilon base small state sameBase vector flat scalar homogeneous radius
  exact ⟨originalKernelPhysicalP_represents parameters length rho epsilon base small radius state.2.1 vector.toCore scalar,
    originalKernelPhysicalX_is_rotation parameters length rho epsilon base small radius state.2.1 vector.toCore scalar,
    scalarDecay.1,scalarDecay.2,
    originalKernelPhysicalX_decay parameters length rho epsilon base small state sameBase vector flat scalar homogeneous radius positive⟩

end Grad.OriginalKernelRetainedDecay.Consumer
