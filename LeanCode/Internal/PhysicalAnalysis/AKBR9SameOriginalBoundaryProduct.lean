import AKBR8OriginalPhysicalRowFourier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalKernelOuterUniqueness
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.SourceCollar Grad.Cor18
open Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.BoundaryTrace
open Grad.OriginalKernelRetainedDecay Grad.AnnularReconstruction Grad.PhysicalCoordinates
open Grad.OriginalKernelCovariantRecovery Grad.ActualBoundaryPrimitives Grad.ActualPolarFlux
open Grad.ActualPhysicalField Grad.ActualSmoothPhysicalField Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Ledger

/-- The original AD19 row, expressed as the same algebraic covector pairing. -/
theorem originalBoundaryRow_pairing (parameters : PhaseParameters) (length rho alpha delta parameter epsilon : ℝ)
    (base : ACore parameters 3) (axial polar : ℝ) (point : ClosedDisk) (component : Fin 3) :
    originalBoundaryRow parameters length rho alpha delta parameter epsilon base axial polar point component=
      matrixPairing (fun coordinate => ((spatialColumn point).transpose*
        (physicalSeedMatrix rho alpha delta parameter axial)⁻¹*planarPhysicalInclusion.transpose) 0 coordinate)
        (originalPhysicalFrameMatrix parameters length epsilon base axial point)⁻¹.transpose (polarVector component polar) := by
  unfold originalBoundaryRow originalPhysicalBoundaryMatrix
  rw [←Matrix.mulVec_mulVec]
  rfl

variable (parameters : PhaseParameters) (compact : ℝ)
    (state : RetainedInverseState parameters parameters.length compact)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (vector : ACore parameters 3)
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)

/-- The SAME covariant reconstructed from the original U has precisely the
stored seed-inverted radial row at r=1. The total frame inverse cancels. -/
theorem originalBoundaryProduct_sameOriginalRow (angles : ℝ×ℝ) :
    originalBoundaryProduct parameters parameters.length compact state.boundaryState
      (fun angles => (originalPolarCovariantCurves parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field
        state.val.val.low lower positive bounded vector).fullField bounded (1,angles)) angles=
    originalBoundaryRowSeries parameters
      (rowField parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed (toPhysicalCore parameters vector)) angles := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  apply (originalBoundaryProduct_value parameters parameters.length compact state.boundaryState _ angles).trans
  simp_rw [originalBoundaryRow_pairing]
  rw [originalPolarMatrixPairing]
  have same := originalPolarCovariantCurves_recovers_U parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field
    state.val.val.low lower positive bounded vector 1 ⟨bounded.le,le_rfl⟩ angles
  rw [SmoothLowPhysicalRow.fullField_physicalUFromPolar parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field
    state.val.val.low lower positive bounded _ 1 ⟨bounded.le,le_rfl⟩ angles,
    originalInverseTransposeFamily_matrix parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low,
    originalInverseFamily_eq_matrixInverse parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low] at same
  have contraction := congrArg (fun value : ComplexEuclidean 3 =>
    (((spatialColumn (Grad.SourceCollarDivision.polarClosedPoint 1 angles.1 zero_le_one le_rfl)).transpose*
      (physicalSeedMatrix state.val.val.rho state.val.val.alpha state.val.val.delta state.val.val.parameter angles.2)⁻¹*
      planarPhysicalInclusion.transpose).mulVec value) 0) same
  change _=_ at contraction
  apply contraction.trans
  have storage := originalBoundaryCovector_storage (originalCoefficientSeed parameters compact state.val.val) insideSeed
    (Grad.SourceCollarDivision.polarClosedPoint 1 angles.1 zero_le_one le_rfl) angles.2
    (originalCoreCircle parameters vector ⟨1,zero_le_one,le_rfl⟩ angles)
  apply storage.trans
  unfold originalBoundaryRowSeries originalBoundaryRadialOperator originalCoreCircle
  simp only [rowField,LinearMap.comp_apply,originalCoreValue_seedInverse,planarPartCore,coreValue_gaugeValueMap,
    toPhysicalCore,coreValue_valueMap]
  simp [Grad.SourceCollarDivision.polarClosedPoint,polarPlane,collarPlane,matrixUnit_apply,operatorBasis]

end Grad.OriginalKernelOuterUniqueness
