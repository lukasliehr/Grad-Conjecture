import AKAC8ExactPhysicalRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularPhysicalFourier

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1)

theorem SmoothLowPhysicalRow.fullField_angular_periodic (radius axial : ℝ) :
    Function.Periodic (fun polar => curves.fullField bounded (radius,polar,axial)) (2 * Real.pi) := by
  intro polar
  apply PiLp.ext
  intro component
  rw [curves.fullField_coordinate,curves.fullField_coordinate]
  exact congrArg (fun value : ComplexEuclidean 1 => value 0)
    (hilbertPhysicalField_angular_periodic lower bounded (curves.componentCurve component) radius axial polar)

theorem SmoothLowPhysicalRow.fullField_cell_periodic (radius polar : ℝ) :
    Function.Periodic (fun axial => curves.fullField bounded (radius,polar,axial)) (2 * Real.pi) := by
  intro axial
  apply PiLp.ext
  intro component
  rw [curves.fullField_coordinate,curves.fullField_coordinate]
  exact congrArg (fun value : ComplexEuclidean 1 => value 0)
    (hilbertPhysicalField_cell_periodic lower bounded (curves.componentCurve component) radius polar axial)

end Grad.ActualSmoothPhysicalField
