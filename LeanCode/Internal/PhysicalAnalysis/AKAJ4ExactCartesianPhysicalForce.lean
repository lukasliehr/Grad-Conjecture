import AKAJ3SamePhysicalForceMatrixAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualForceMatrixFidelity
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceCollarRestriction
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra Grad.ActualPhysicalField
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualSmoothPhysicalField Grad.ActualCurrentPrimitives Grad.ActualPolarEquations Grad.SourceCollar
open Grad.BoundaryKernelAction Grad.AnnularWeightedSmoothness Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2

/-- The polar covariant contracts against Q before any Cartesian inverse. -/
theorem forcePolarContraction_cartesian (kind : Fin 2) (angle : ℝ)
    (matrix : Matrix (Fin 3) (Fin 3) ℂ) (polar : ComplexEuclidean 3) :
    (∑ component : Fin 3,forcePolarComponent kind angle matrix component * polar component) =
      matrixPairing (if kind = 0 then (2 : ℂ) • physicalTangentialVector angle else (-2 : ℂ) • physicalToroidalVector)
        matrix (cartesianCovariantValue angle polar) := by
  simp [forcePolarComponent,matrixPairing,cartesianCovariantValue,polarDomainMatrix,
    Matrix.mulVec,dotProduct,Fin.sum_univ_three]
  ring

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : AnnularReconstructionState parameters length compact) (kind : Fin 2)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

/-- The completed force row is the literal original Cartesian contraction
against SAME U = F_C^{-T} Q a_c. Its +2 and -2 factors and L normalization are unchanged. -/
theorem fullField_forceCartesianU (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (physicalForceCurves parameters length compact lower positive bounded state kind curves).fullField bounded (radius,angles) 0 =
      matrixPairing (if kind = 0 then (2 : ℂ) • physicalTangentialVector angles.1 else (-2 : ℂ) • physicalToroidalVector)
        (rotatedPhysicalFrameMatrix parameters 1 1 state.val.data.epsilon state.val.data.field angles.2
          (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) *
            Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose
        ((curves.physicalUFromPolar parameters length state.val.data.rho state.val.data.epsilon state.val.data.field
          state.val.low lower positive bounded).fullField bounded (radius,angles)) := by
  rw [fullField_forceMatrixComponent parameters length compact lower positive bounded state kind curves radius inside angles,
    forcePolarContraction_cartesian]
  have sameU := curves.fullField_physicalUFromPolar parameters length state.val.data.rho state.val.data.epsilon state.val.data.field
    state.val.low lower positive bounded radius inside angles
  rw [originalInverseTransposeFamily_matrix parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low,
    originalInverseFamily_eq_matrixInverse parameters length state.val.data.rho state.val.data.epsilon state.val.data.field state.val.low] at sameU
  rw [sameU]
  change matrixPairing _ (_ * _) _ = matrixPairing _ _ (Matrix.mulVec _ _)
  unfold matrixPairing
  rw [Matrix.mulVec_mulVec]

end Grad.ActualForceMatrixFidelity
