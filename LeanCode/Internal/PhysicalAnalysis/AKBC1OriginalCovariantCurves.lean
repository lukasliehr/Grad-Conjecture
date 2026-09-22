import AKBA13SamePhysicalGraphTraces

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.OriginalKernelGraphRestriction Grad.OriginalKernelRetainedDecay Grad.ActualPhysicalField
open Grad.SourceCollar Grad.AnnularKernelL2

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6≤originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0<lower) (bounded : lower<1) (vector : ACore parameters 3)

/-- All original weighted grades of the actual Cartesian covariant F^T U. -/
def originalCartesianCovariantCurves :=
  (originalVectorLowCurves parameters lower positive bounded vector).matrixAction parameters
    (originalTransposeFrameFamily parameters length epsilon base)
    (originalTransposeFrameFamily_estimate parameters length rho epsilon base small).actualCoherent lower positive bounded

theorem originalCartesianCovariantCurves_fullField (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (originalCartesianCovariantCurves parameters length rho epsilon base small lower positive bounded vector).fullField bounded (radius,angles) =
      WithLp.toLp 2 ((originalPhysicalFrameMatrix parameters length epsilon base angles.2
        (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2)).transpose.mulVec
          (originalCoreCircle parameters vector ⟨radius,positive.le.trans inside.1,inside.2⟩ angles)) := by
  unfold originalCartesianCovariantCurves
  rw [SmoothLowPhysicalRow.fullField_matrixAction parameters _ _ lower positive bounded _ radius inside angles,
    physicalMatrixProduct_apply,originalVectorLowCurves_fullField parameters lower positive bounded vector radius inside angles]
  rw [originalTransposeFrameFamily,familyMatrix_transpose (unitDiskAdmissible parameters) _
    (originalFullFrameFamily_estimate parameters length rho epsilon base
      (originalCoefficient_low_margin parameters length rho epsilon base small).1).actualCoherent,
    originalFullFrameFamily_matrix]

end Grad.OriginalKernelCovariantRecovery
