import AKBH2SameInverseWeightMoments
import AKAT1LiteralRadialForceContraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualForceMoments
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra Grad.ActualPhysicalField
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualSmoothPhysicalField Grad.ActualCurrentPrimitives Grad.ActualPolarEquations
open Grad.BoundaryKernelAction Grad.AnnularWeightedSmoothness Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualNativeCellMoments

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

def sameForceMatrixCurves :=
  curves.cartesianCovariant.matrixAction parameters (forceMatrixFamily parameters length epsilon base)
    (forceMatrixFamily_coherent parameters length rho epsilon base small) lower positive bounded

/-- The full completed force matrix is applied before selecting any integer cell. -/
theorem sameForceMatrixCurves_sameU (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (sameForceMatrixCurves parameters length rho epsilon base small lower positive bounded curves).fullField bounded (radius,angles) =
      WithLp.toLp 2 (((rotatedPhysicalFrameMatrix parameters 1 1 epsilon base angles.2
        (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) *
          Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose).mulVec
        ((curves.physicalUFromPolar parameters length rho epsilon base small lower positive bounded).fullField bounded (radius,angles))) := by
  rw [sameForceMatrixCurves,curves.cartesianCovariant.fullField_matrixAction,
    physicalMatrixProduct_apply,forceMatrixFamily_actual parameters length rho epsilon base small]
  rw [curves.fullField_cartesianCovariant bounded radius inside angles]
  have sameU := curves.fullField_physicalUFromPolar parameters length rho epsilon base small lower positive bounded radius inside angles
  rw [originalInverseTransposeFamily_matrix parameters length rho epsilon base small,
    originalInverseFamily_eq_matrixInverse parameters length rho epsilon base small] at sameU
  rw [sameU]
  unfold originalForceMatrix
  rw [Matrix.mulVec_mulVec]
  all_goals exact inside

end Grad.ActualForceMoments
