import AKAR7UniformActualMatrixActions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Grad.OriginalKernelRetainedDecay
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.SourceCollarDivision
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.PhaseAlgebra Grad.BoundaryLift
open Grad.SourceCollarCoefficients Grad.ActualPhysicalField Grad.SourceCollar
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Envelope

theorem originalTransposeFrameFamily_matrix (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (base : ACore parameters 3) (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalTransposeFrameFamily parameters length epsilon base) grade angle point =
      (originalPhysicalFrameMatrix parameters length epsilon base angle point).transpose := by
  unfold originalTransposeFrameFamily
  rw [familyMatrix_transpose (unitDiskAdmissible parameters) _
    (originalFullFrameFamily_estimate parameters length rho epsilon base
      (originalCoefficient_low_margin parameters length rho epsilon base small).1).actualCoherent,
    originalFullFrameFamily_matrix]

/-- The exact covector matrix D = B F_C^T = det(F_C) F_C^{-1}.
The inverse is the already accepted original Neumann family. -/
theorem originalCofactorCovectorFamily_matrix (parameters : PhaseParameters) (length rho epsilon : ℝ)
    (base : ACore parameters 3) (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (originalCofactorCovectorFamily parameters length epsilon base) grade angle point =
      (originalPhysicalFrameMatrix parameters length epsilon base angle point).det •
        familyMatrix (originalInverseFamily parameters length epsilon base) grade angle point := by
  have margin := originalCoefficient_low_margin parameters length rho epsilon base small
  have frame := (originalFullFrameFamily_estimate parameters length rho epsilon base margin.1).actualCoherent
  have cofactor := (originalCofactorFamily_estimate parameters length rho epsilon base small).actualCoherent
  unfold originalCofactorCovectorFamily
  rw [familyMatrix_comp (unitDiskAdmissible parameters) _ _ cofactor
    (transposeFamily_coherent (unitDiskAdmissible parameters) _ frame),
    familyMatrix_transpose (unitDiskAdmissible parameters) _ frame,
    originalFullFrameFamily_matrix,originalCofactorFamily_matrix parameters length rho epsilon base small]
  have inverse := (originalInverseFamily_matrix_identity parameters length epsilon base margin.2.2 grade angle point).1
  have transpose : (familyMatrix (originalInverseFamily parameters length epsilon base) grade angle point).transpose *
      (originalPhysicalFrameMatrix parameters length epsilon base angle point).transpose = 1 := by
    simpa only [Matrix.transpose_mul,Matrix.transpose_one] using congrArg Matrix.transpose inverse
  rw [Matrix.smul_mul,Matrix.mul_assoc,transpose,Matrix.mul_one]

end Grad.OriginalKernelRetainedDecay
