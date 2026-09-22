import AKAC18ExactPeriodicFourierUniqueness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra

 theorem doubleCoefficient_valueMap {source target : ℕ}
    (mapping : ComplexEuclidean source →L[ℂ] ComplexEuclidean target)
    (field : ℝ × ℝ → ComplexEuclidean source) (continuousField : Continuous field) (mode : ℤ × ℤ) :
    doubleCoefficient (fun angles => mapping (field angles)) mode = mapping (doubleCoefficient field mode) := by
  unfold doubleCoefficient
  have inner (polar : ℝ) := angularCoefficient_valueMap mapping (fun axial => field (polar,axial))
    (continuousField.comp (continuous_const.prodMk continuous_id)) mode.2
  simp_rw [inner]
  exact angularCoefficient_valueMap mapping _
    (Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter field continuousField mode.2) mode.1

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1)

theorem SmoothLowPhysicalRow.fullField_angular_shift (radius polar axial : ℝ) :
    curves.fullField bounded (radius,polar+2*Real.pi,axial) = curves.fullField bounded (radius,polar,axial) :=
  curves.fullField_angular_periodic bounded radius axial polar

theorem SmoothLowPhysicalRow.fullField_cell_shift (radius polar axial : ℝ) :
    curves.fullField bounded (radius,polar,axial+2*Real.pi) = curves.fullField bounded (radius,polar,axial) :=
  curves.fullField_cell_periodic bounded radius polar axial

theorem SmoothLowPhysicalRow.fullField_doubleCoefficient (radius : ℝ) (inside : radius ∈ Icc lower 1)
    (mode : ℤ × ℤ) :
    doubleCoefficient (fun angles => curves.fullField bounded (radius,angles)) mode = curves.physicalCurve 0 radius mode := by
  rw [doubleCoefficient,doubleCoefficient_swap _ (curves.fullField_continuous_angles bounded radius inside)]
  exact curves.fullField_coefficient bounded radius inside mode

theorem SmoothLowPhysicalRow.fullField_eq_of_doubleCoefficient (radius : ℝ) (inside : radius ∈ Icc lower 1)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (continuousField : Continuous field)
    (angular : ∀ axial, Function.Periodic (fun polar => field (polar,axial)) (2 * Real.pi))
    (cell : ∀ polar, Function.Periodic (fun axial => field (polar,axial)) (2 * Real.pi))
    (same : ∀ mode, doubleCoefficient field mode = curves.physicalCurve 0 radius mode) :
    (fun angles => curves.fullField bounded (radius,angles)) = field := by
  apply doubleFourier_ext _ _ (curves.fullField_continuous_angles bounded radius inside) continuousField
    (curves.fullField_angular_periodic bounded radius) angular (curves.fullField_cell_periodic bounded radius) cell
  intro mode
  rw [curves.fullField_coefficient bounded radius inside mode,← doubleCoefficient_swap field continuousField]
  exact (same mode).symm

theorem SmoothLowPhysicalRow.fullField_bulkUnit {target : ℕ} (output : Fin target) (input : Fin dimension)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.bulkUnit output input).fullField bounded (radius,angles) =
      matrixUnit output input (curves.fullField bounded (radius,angles)) := by
  apply congrFun ((curves.bulkUnit output input).fullField_eq_of_doubleCoefficient bounded radius inside
    (fun angles => matrixUnit output input (curves.fullField bounded (radius,angles)))
    ((matrixUnit output input).continuous.comp (curves.fullField_continuous_angles bounded radius inside))
    (fun axial polar => congrArg (matrixUnit output input) (curves.fullField_angular_periodic bounded radius axial polar))
    (fun polar axial => congrArg (matrixUnit output input) (curves.fullField_cell_periodic bounded radius polar axial)) _) angles
  intro mode
  rw [doubleCoefficient_valueMap,curves.fullField_doubleCoefficient bounded radius inside mode,
    (curves.bulkUnit output input).physicalCurve_coefficient bounded 0 radius inside mode,
    curves.physicalCurve_coefficient bounded 0 radius inside mode,map_smul]
  rfl
  exact curves.fullField_continuous_angles bounded radius inside

theorem SmoothLowPhysicalRow.fullField_add {second : DivisionRow dimension lower}
    (other : SmoothLowPhysicalRow parameters lower positive second) (radius : ℝ) (inside : radius ∈ Icc lower 1)
    (angles : ℝ × ℝ) :
    (curves.add other).fullField bounded (radius,angles) =
      curves.fullField bounded (radius,angles) + other.fullField bounded (radius,angles) := by
  apply congrFun ((curves.add other).fullField_eq_of_doubleCoefficient bounded radius inside
    (fun angles => curves.fullField bounded (radius,angles)+other.fullField bounded (radius,angles))
    ((curves.fullField_continuous_angles bounded radius inside).add (other.fullField_continuous_angles bounded radius inside))
    (fun axial polar => by
      simp only [curves.fullField_angular_periodic bounded radius axial polar,other.fullField_angular_periodic bounded radius axial polar])
    (fun polar axial => by
      simp only [curves.fullField_cell_periodic bounded radius polar axial,other.fullField_cell_periodic bounded radius polar axial]) _) angles
  intro mode
  rw [doubleCoefficient_add _ _ (curves.fullField_continuous_angles bounded radius inside)
    (other.fullField_continuous_angles bounded radius inside),curves.fullField_doubleCoefficient bounded radius inside mode,
    other.fullField_doubleCoefficient bounded radius inside mode]
  simp only [curves.physicalCurve_coefficient bounded 0 radius inside mode,
    other.physicalCurve_coefficient bounded 0 radius inside mode,
    (curves.add other).physicalCurve_coefficient bounded 0 radius inside mode]
  change _ = _ • (curves.curve 0 radius mode+other.curve 0 radius mode)
  rw [smul_add]

end Grad.ActualSmoothPhysicalField
