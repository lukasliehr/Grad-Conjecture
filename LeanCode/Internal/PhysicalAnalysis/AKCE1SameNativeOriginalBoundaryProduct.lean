import AKCA23ActualScalarCartesianPolynomial
import AKBR12OriginalBoundaryPrimitiveZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.SourceCollar Grad.Cor18
open Grad.SourceCollarCoefficients Grad.SourceCollarDivision Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.BoundaryTrace
open Grad.OriginalKernelRetainedDecay Grad.AnnularReconstruction Grad.PhysicalCoordinates
open Grad.OriginalKernelCovariantRecovery Grad.ActualBoundaryPrimitives Grad.ActualPolarFlux
open Grad.ActualPhysicalField Grad.ActualSmoothPhysicalField Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Ledger

open Grad.OriginalKernelOuterUniqueness

variable (parameters : PhaseParameters) (compact : ℝ)
    (state : RetainedInverseState parameters parameters.length compact)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (vector : ACore parameters 3)
    (insideSeed : originalCoefficientSeed parameters compact state.val.val∈Seed.parameterDomain)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (same : ∀ angles : ℝ×ℝ,
      (curves.physicalUFromPolar parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field
        state.val.val.low lower positive bounded).fullField bounded (1,angles)=
          originalCoreCircle parameters vector ⟨1,zero_le_one,le_rfl⟩ angles)

include same

/-- The SAME covariant reconstructed from the original U has precisely the
stored seed-inverted radial row at r=1. The total frame inverse cancels. -/
theorem nativeBoundaryProduct_sameOriginalRow (angles : ℝ×ℝ) :
    originalBoundaryProduct parameters parameters.length compact state.boundaryState
      (fun angles => curves.fullField bounded (1,angles)) angles=
    originalBoundaryRowSeries parameters
      (rowField parameters (originalCoefficientSeed parameters compact state.val.val) insideSeed (toPhysicalCore parameters vector)) angles := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  apply (originalBoundaryProduct_value parameters parameters.length compact state.boundaryState _ angles).trans
  simp_rw [originalBoundaryRow_pairing]
  rw [originalPolarMatrixPairing]
  have sameValue := same angles
  rw [SmoothLowPhysicalRow.fullField_physicalUFromPolar parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field
    state.val.val.low lower positive bounded _ 1 ⟨bounded.le,le_rfl⟩ angles,
    originalInverseTransposeFamily_matrix parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low,
    originalInverseFamily_eq_matrixInverse parameters parameters.length state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low] at sameValue
  have contraction := congrArg (fun value : ComplexEuclidean 3 =>
    (((spatialColumn (Grad.SourceCollarDivision.polarClosedPoint 1 angles.1 zero_le_one le_rfl)).transpose*
      (physicalSeedMatrix state.val.val.rho state.val.val.alpha state.val.val.delta state.val.val.parameter angles.2)⁻¹*
      planarPhysicalInclusion.transpose).mulVec value) 0) sameValue
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

end Grad.OriginalCoreRealization
