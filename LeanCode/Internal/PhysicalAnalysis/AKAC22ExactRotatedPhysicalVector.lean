import AKAC21ActualAngularMultiplication

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.GaugeCoefficients.Physical.Ledger Grad.BoundaryLift Grad.PhaseAlgebra

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1)

theorem SmoothLowPhysicalRow.fullField_sub {second : DivisionRow dimension lower}
    (other : SmoothLowPhysicalRow parameters lower positive second) (radius : ℝ) (inside : radius ∈ Icc lower 1)
    (angles : ℝ × ℝ) :
    (curves.sub other).fullField bounded (radius,angles) =
      curves.fullField bounded (radius,angles) - other.fullField bounded (radius,angles) := by
  apply congrFun ((curves.sub other).fullField_eq_of_doubleCoefficient bounded radius inside
    (fun angles => curves.fullField bounded (radius,angles)-other.fullField bounded (radius,angles))
    ((curves.fullField_continuous_angles bounded radius inside).sub (other.fullField_continuous_angles bounded radius inside))
    (fun axial polar => by
      simp only [curves.fullField_angular_periodic bounded radius axial polar,other.fullField_angular_periodic bounded radius axial polar])
    (fun polar axial => by
      simp only [curves.fullField_cell_periodic bounded radius polar axial,other.fullField_cell_periodic bounded radius polar axial]) _) angles
  intro mode
  rw [doubleCoefficient_sub _ _ (curves.fullField_continuous_angles bounded radius inside)
    (other.fullField_continuous_angles bounded radius inside),curves.fullField_doubleCoefficient bounded radius inside mode,
    other.fullField_doubleCoefficient bounded radius inside mode]
  simp only [curves.physicalCurve_coefficient bounded 0 radius inside mode,
    other.physicalCurve_coefficient bounded 0 radius inside mode,
    (curves.sub other).physicalCurve_coefficient bounded 0 radius inside mode]
  change _ = _ • (curves.curve 0 radius mode-other.curve 0 radius mode)
  rw [smul_sub]


/-- The completed rotation is the literal pointwise Q(theta) rotation of
THE SAME annular covariant field, on every physical circle. -/
theorem SmoothLowPhysicalRow.fullField_cartesianCovariant
    {polar : DivisionRow 3 lower} (field : SmoothLowPhysicalRow parameters lower positive polar)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    field.cartesianCovariant.fullField bounded (radius,angles) =
      cartesianCovariantValue angles.1 (field.fullField bounded (radius,angles)) := by
  let a := field.cosine.bulkUnit (0 : Fin 3) 0
  let b := field.sine.bulkUnit (0 : Fin 3) 1
  let c := field.sine.bulkUnit (1 : Fin 3) 0
  let d := field.cosine.bulkUnit (1 : Fin 3) 1
  let e := field.bulkUnit (2 : Fin 3) 2
  change ((((a.sub b).add c).add d).add e).fullField bounded (radius,angles) = _
  rw [(((a.sub b).add c).add d).fullField_add bounded e radius inside angles,
    ((a.sub b).add c).fullField_add bounded d radius inside angles,
    (a.sub b).fullField_add bounded c radius inside angles,a.fullField_sub bounded b radius inside angles]
  dsimp only [a,b,c,d,e]
  rw [field.cosine.fullField_bulkUnit bounded (0 : Fin 3) 0 radius inside angles,
    field.sine.fullField_bulkUnit bounded (0 : Fin 3) 1 radius inside angles,
    field.sine.fullField_bulkUnit bounded (1 : Fin 3) 0 radius inside angles,
    field.cosine.fullField_bulkUnit bounded (1 : Fin 3) 1 radius inside angles,
    field.fullField_bulkUnit bounded (2 : Fin 3) 2 radius inside angles,
    field.fullField_cosine bounded radius inside angles,field.fullField_sine bounded radius inside angles,
    cartesianCovariantValue_apply]
  apply PiLp.ext
  intro component
  fin_cases component <;> simp [matrixUnit_apply,operatorBasis]

end Grad.ActualSmoothPhysicalField
