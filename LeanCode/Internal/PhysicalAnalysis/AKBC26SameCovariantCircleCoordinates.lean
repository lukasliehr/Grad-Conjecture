import AKBC25OriginalNegativeCircleIdentification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set
namespace Grad.OriginalKernelCovariantRecovery
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra Grad.SourceCollarFullSource
open Grad.AnnularReconstruction Grad.AnnularOriginalSmoothCore Grad.ActualSmoothPhysicalField
open Grad.BoundaryKernelAction Grad.OriginalKernelRetainedDecay Grad.OriginalKernelGraphRestriction
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollar Grad.ActualPhysicalField
open Grad.ActualCurrentPrimitives

theorem originalPolarCovariantValue_radial (angle : ℝ) (value : ComplexEuclidean 3) :
    matrixUnit (0 : Fin 1) (0 : Fin 3) (originalPolarCovariantValue angle value)=originalPolarRadialValue value angle := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [originalPolarCovariantValue,originalPolarRadialValue,polarDomainMatrix,Matrix.mulVec,dotProduct,
    Fin.sum_univ_three,physicalRadialVector,matrixUnit_apply,operatorBasis]

theorem originalPolarCovariantValue_tangential (angle : ℝ) (value : ComplexEuclidean 3) :
    matrixUnit (0 : Fin 1) (1 : Fin 3) (originalPolarCovariantValue angle value)=originalPolarTangentialValue value angle := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [originalPolarCovariantValue,originalPolarTangentialValue,polarDomainMatrix,Matrix.mulVec,dotProduct,
    Fin.sum_univ_three,physicalTangentialVector,matrixUnit_apply,operatorBasis]
  ring

theorem originalPolarCovariantValue_axial (angle : ℝ) (value : ComplexEuclidean 3) :
    matrixUnit (0 : Fin 1) (2 : Fin 3) (originalPolarCovariantValue angle value)=matrixUnit (0 : Fin 1) (2 : Fin 3) value := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [originalPolarCovariantValue,polarDomainMatrix,Matrix.mulVec,dotProduct,
    Fin.sum_univ_three,physicalToroidalVector,matrixUnit_apply,operatorBasis]

variable {parameters : PhaseParameters} {lower : ℝ} {positive : 0<lower}
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower<1) (radius : Icc lower (1 : ℝ)) (circle : CellL2 3)
    (represented : OriginalCircleRepresents parameters (tupleRadius lower positive radius) circle
      (fun angles => curves.fullField bounded (radius.val,angles)))

include bounded represented

theorem originalPolarNegative_radial :
    OriginalNegativeCircle parameters (tupleRadius lower positive radius)
      (forceCoordinateTrace _ 0 0 0 (originalCurveNegativeTrace (originalPolarFromCartesianCurves curves) radius))
      (originalCircleRadialRow parameters circle) := by
  intro mode
  rw [originalCurveNegative_coordinate_coefficient _ bounded radius]
  have result := (represented.radial (curves.fullField_continuous_angles bounded radius.val radius.property)) mode
  refine Eq.trans ?_ result.symm
  congr 1
  funext angles
  rw [originalPolarFromCartesianCurves_fullField curves bounded radius.val radius.property angles,originalPolarCovariantValue_radial]

theorem originalPolarNegative_tangential :
    OriginalNegativeCircle parameters (tupleRadius lower positive radius)
      (forceCoordinateTrace _ 0 0 1 (originalCurveNegativeTrace (originalPolarFromCartesianCurves curves) radius))
      (originalCircleTangentialRow parameters circle) := by
  intro mode
  rw [originalCurveNegative_coordinate_coefficient _ bounded radius]
  have result := (represented.tangential (curves.fullField_continuous_angles bounded radius.val radius.property)) mode
  refine Eq.trans ?_ result.symm
  congr 1
  funext angles
  rw [originalPolarFromCartesianCurves_fullField curves bounded radius.val radius.property angles,originalPolarCovariantValue_tangential]

theorem originalPolarNegative_axial :
    OriginalNegativeCircle parameters (tupleRadius lower positive radius)
      (forceCoordinateTrace _ 0 0 2 (originalCurveNegativeTrace (originalPolarFromCartesianCurves curves) radius))
      (originalCircleMatrix parameters (matrixUnit (0 : Fin 1) (2 : Fin 3)) circle) := by
  intro mode
  rw [originalCurveNegative_coordinate_coefficient _ bounded radius]
  have result := (represented.valueMap (curves.fullField_continuous_angles bounded radius.val radius.property)
    (matrixUnit (0 : Fin 1) (2 : Fin 3))) mode
  refine Eq.trans ?_ result.symm
  congr 1
  funext angles
  rw [originalPolarFromCartesianCurves_fullField curves bounded radius.val radius.property angles,originalPolarCovariantValue_axial]

end Grad.OriginalKernelCovariantRecovery
