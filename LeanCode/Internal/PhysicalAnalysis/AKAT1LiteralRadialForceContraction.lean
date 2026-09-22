import AKAJ4ExactCartesianPhysicalForce

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualCartesianEquations
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra Grad.ActualPhysicalField
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualSmoothPhysicalField Grad.ActualCurrentPrimitives Grad.ActualPolarEquations Grad.SourceCollar
open Grad.BoundaryKernelAction Grad.AnnularWeightedSmoothness Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualGaugeSigmaPrimitives

private theorem retainedForceContractionAlgebra (angle : ℝ)
    (matrix : Matrix (Fin 3) (Fin 3) ℂ) (polar : ComplexEuclidean 3) :
    (∑ component : Fin 3, (2 * polarMatrixEntry 0 component angle matrix +
      if component = 1 then 2 else 0) * polar component) =
      2 * polar 1 + matrixPairing ((2 : ℂ) • physicalRadialVector angle) matrix (cartesianCovariantValue angle polar) := by
  simp [polarMatrixEntry,polarVector,matrixPairing,cartesianCovariantValue,polarDomainMatrix,
    Matrix.mulVec,dotProduct,Fin.sum_univ_three,physicalRadialVector,physicalTangentialVector,physicalToroidalVector]
  ring

theorem originalRetainedForce_cartesian (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (axial angle : ℝ) (point : ClosedDisk) (polar : ComplexEuclidean 3) :
    (∑ component : Fin 3, originalRetainedForceRow parameters length epsilon base axial angle point component * polar component) =
      2 * polar 1 + matrixPairing ((2 : ℂ) • physicalRadialVector angle)
        (originalForceMatrix parameters length epsilon base axial point) (cartesianCovariantValue angle polar) := by
  simp_rw [originalRetainedForceRow_deviation parameters length rho epsilon base small]
  exact retainedForceContractionAlgebra angle _ polar

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : AnnularReconstructionState parameters length compact)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

/-- Exact radial force contraction against the SAME physical U. The two
polar frame contributions are retained before Cartesian conversion. -/
theorem originalRetainedForce_sameU (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (∑ component : Fin 3,originalRetainedForceRow parameters length state.val.data.epsilon state.val.data.field
      angles.2 angles.1 (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) component *
        curves.fullField bounded (radius,angles) component) =
      2 * curves.fullField bounded (radius,angles) 1 +
      matrixPairing ((2 : ℂ) • physicalRadialVector angles.1)
        (rotatedPhysicalFrameMatrix parameters 1 1 state.val.data.epsilon state.val.data.field angles.2
          (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) *
            Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose
        ((curves.physicalUFromPolar parameters length state.val.data.rho state.val.data.epsilon state.val.data.field
          state.val.low lower positive bounded).fullField bounded (radius,angles)) := by
  rw [originalRetainedForce_cartesian parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low]
  have sameU := curves.fullField_physicalUFromPolar parameters length state.val.data.rho state.val.data.epsilon state.val.data.field
    state.val.low lower positive bounded radius inside angles
  rw [originalInverseTransposeFamily_matrix parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low,
    originalInverseFamily_eq_matrixInverse parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low] at sameU
  rw [sameU]
  change _ + matrixPairing _ (_ * _) _ = _ + matrixPairing _ _ (Matrix.mulVec _ _)
  unfold matrixPairing
  rw [Matrix.mulVec_mulVec]

end Grad.ActualCartesianEquations
