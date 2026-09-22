import AKBJ9ActualProjectedThirdForceIntegrability
import AKBD2ProjectedParameterCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualScalarWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra Grad.ActualPhysicalField
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.ActualSmoothPhysicalField Grad.ActualCurrentPrimitives Grad.ActualPolarEquations Grad.ActualForceMoments
open Grad.BoundaryKernelAction Grad.AnnularWeightedSmoothness Grad.AnnularReconstruction
open Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualNativeCellMoments Grad.SourceCollar
open Grad.ActualDeterminantEquations Grad.ActualCartesianEquations

theorem thirdForceMatrix_pairing (matrix : Matrix (Fin 3) (Fin 3) ℂ) (value : ComplexEuclidean 3) :
    matrixPairing ((-2 : ℂ) • physicalToroidalVector) matrix value =
      (-2 : ℂ) * (WithLp.toLp 2 (matrix.mulVec value) : ComplexEuclidean 3) 2 := by
  simp [matrixPairing,physicalToroidalVector,Matrix.mulVec,dotProduct,Fin.sum_univ_three]

variable (parameters : PhaseParameters) (length rho epsilon : ℝ) (base : ACore parameters 3)
    (small : physicalBudget parameters base rho epsilon 6 ≤ originalCoefficientLowRadius parameters length)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

/-- Exact scalar mean-free completed matrix correction in the literal original third equation. -/
theorem sameProjectedThirdForce_fullField (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (-2 * (length : ℂ)) *
      (((sameForceMatrixCurves parameters length rho epsilon base small lower positive bounded curves).bulkUnit (0 : Fin 1) 2).meanFree.fullField bounded (radius,angles)) 0 =
      (length : ℂ) * removePolarMean (fun query =>
        matrixPairing ((-2 : ℂ) • physicalToroidalVector)
          (rotatedPhysicalFrameMatrix parameters 1 1 epsilon base query.2
            (polarClosedPoint radius query.1 (positive.le.trans inside.1) inside.2) * Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose
          ((curves.physicalUFromPolar parameters length rho epsilon base small lower positive bounded).fullField bounded (radius,query))) angles := by
  let matrixCurves := sameForceMatrixCurves parameters length rho epsilon base small lower positive bounded curves
  have projected : ((matrixCurves.bulkUnit (0 : Fin 1) 2).meanFree.fullField bounded (radius,angles)) 0 =
      removePolarMean (fun query => matrixCurves.fullField bounded (radius,query) 2) angles := by
    rw [(matrixCurves.bulkUnit (0 : Fin 1) 2).fullField_meanFree bounded radius inside angles,
      removePolarMean_coordinate _ ((matrixCurves.bulkUnit (0 : Fin 1) 2).fullField_continuous_angles bounded radius inside)]
    congr 1
    funext query
    rw [matrixCurves.fullField_bulkUnit bounded (0 : Fin 1) 2 radius inside query]
    simp [matrixUnit_apply,operatorBasis]
  have actual : (fun query =>
      matrixPairing ((-2 : ℂ) • physicalToroidalVector)
        (rotatedPhysicalFrameMatrix parameters 1 1 epsilon base query.2
          (polarClosedPoint radius query.1 (positive.le.trans inside.1) inside.2) * Matrix.diagonal ![1,1,(length : ℂ)⁻¹]).transpose
        ((curves.physicalUFromPolar parameters length rho epsilon base small lower positive bounded).fullField bounded (radius,query))) =
      (-2 : ℂ) • (fun query => matrixCurves.fullField bounded (radius,query) 2) := by
    funext query
    rw [thirdForceMatrix_pairing]
    change (-2 : ℂ) * _ = (-2 : ℂ) * _
    exact congrArg (fun value : ComplexEuclidean 3 => (-2 : ℂ) * value 2)
      (sameForceMatrixCurves_sameU parameters length rho epsilon base small lower positive bounded curves radius inside query).symm
  change (-2 * (length : ℂ)) * ((matrixCurves.bulkUnit (0 : Fin 1) 2).meanFree.fullField bounded (radius,angles)) 0 = _
  rw [projected,actual]
  change (-2 * (length : ℂ)) * _ = (length : ℂ) * removePolarMean (fun query => (-2 : ℂ) • matrixCurves.fullField bounded (radius,query) 2) angles
  rw [removePolarMean_smul]
  change (-2 * (length : ℂ)) * _ = (length : ℂ) * ((-2 : ℂ) * _)
  ring

end Grad.ActualScalarWeakEquations
