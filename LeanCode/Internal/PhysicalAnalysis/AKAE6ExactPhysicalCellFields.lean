import AKAE5SameCellProjectionCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients Grad.SourceBoundaryTrace
open Grad.SourceCollarFullSource Grad.SourceCollarAngular Grad.BoundaryTrace Grad.DiskExtension.Operator
open Grad.ActualCartesianDescent

local instance cellFieldAngularPeriodPositive : Fact (0 < (2 * Real.pi : ℝ)) := ⟨by positivity⟩

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower < 1)

 theorem SmoothLowPhysicalRow.fullField_cellProjection (cell : ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1)
    (angles : ℝ × ℝ) :
    (curves.cellProjection cell).fullField bounded (radius,angles) =
      cellExponential cell angles.2 • angularCoefficient (fun axial => curves.fullField bounded (radius,angles.1,axial)) cell := by
  let part := fun polar => angularCoefficient (fun axial => curves.fullField bounded (radius,polar,axial)) cell
  have partContinuous : Continuous part := Grad.SourceCollarFullSource.angularCoefficient_continuous_parameter
    _ (curves.fullField_continuous_angles bounded radius inside) cell
  let candidate := fun angles : ℝ × ℝ => cellExponential cell angles.2 • part angles.1
  apply congrFun ((curves.cellProjection cell).fullField_eq_of_doubleCoefficient bounded radius inside candidate
    (((cellExponential_smooth cell).continuous.comp continuous_snd).smul (partContinuous.comp continuous_fst)) ?_ ?_ ?_) angles
  · intro axial polar
    change cellExponential cell axial • part (polar+2*Real.pi) = cellExponential cell axial • part polar
    congr 1
    exact congrArg (fun field : ℝ → ComplexEuclidean dimension => angularCoefficient field cell)
      (funext (fun axial => curves.fullField_angular_shift bounded radius polar axial))
  · intro polar axial
    change cellExponential cell (axial+2*Real.pi) • part polar = cellExponential cell axial • part polar
    simp only [← cellCharacter_coe,AddCircle.coe_add_period]
  · intro mode
    rw [curves.physicalCurve_cellProjection bounded cell 0 radius inside mode]
    unfold doubleCoefficient
    have inner (polar : ℝ) : angularCoefficient (fun axial => candidate (polar,axial)) mode.2 =
        if mode.2-cell=0 then part polar else 0 := by
      rw [angularCoefficient_character_mul]
      exact angularCoefficient_constant (part polar) (mode.2-cell)
    simp_rw [inner]
    by_cases same : mode.2=cell
    · rw [if_pos same]
      simp only [sub_self,if_pos, same]
      have actual := curves.fullField_doubleCoefficient bounded radius inside (mode.1,cell)
      exact actual.trans (congrArg (fun query => curves.physicalCurve 0 radius query)
        (show (mode.1,cell)=mode from Prod.ext rfl same.symm))
    · rw [if_neg same]
      simp only [if_neg (sub_ne_zero.mpr same),angularCoefficient_constant]
      split_ifs <;> rfl

/-- An individual physical cell is selected exactly, with all angular modes retained. -/
def SmoothLowPhysicalRow.cartesianCellField (cell : ℤ) (point : SpatialPlane) : ComplexEuclidean dimension :=
  (curves.cellProjection cell).cartesianField bounded (point,0)

theorem SmoothLowPhysicalRow.cartesianCellField_actual (cell : ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar : ℝ) :
    curves.cartesianCellField bounded cell (spatialPlaneOfPair (polarCoord.symm (radius,polar))) =
      angularCoefficient (fun axial => curves.fullField bounded (radius,polar,axial)) cell := by
  rw [SmoothLowPhysicalRow.cartesianCellField,(curves.cellProjection cell).cartesianField_polar bounded radius
    (positive.trans_le inside.1) polar 0,curves.fullField_cellProjection bounded cell radius inside (polar,0)]
  simp [cellExponential]

theorem SmoothLowPhysicalRow.cartesianCellField_smoothAt (cell : ℤ) (point : SpatialPlane)
    (inside : ‖point‖ ∈ Ioo lower 1) :
    ContDiffAt ℝ ∞ (curves.cartesianCellField bounded cell) point :=
  ((curves.cellProjection cell).cartesianField_smoothAt bounded (point,0) inside).comp point
    (contDiffAt_id.prodMk contDiffAt_const)

/-- Exactly the per-cell angular coefficient consumed by the original
physical weighted-energy to Cartesian integrability theorem. -/
theorem SmoothLowPhysicalRow.cartesianCellField_coefficient (cell : ℤ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (angular : ℤ) :
    angularCoefficient (fun polar => curves.cartesianCellField bounded cell
      (spatialPlaneOfPair (polarCoord.symm (radius,polar)))) angular =
        curves.physicalCurve 0 radius (angular,cell) := by
  simp_rw [curves.cartesianCellField_actual bounded cell radius inside]
  exact curves.fullField_doubleCoefficient bounded radius inside (angular,cell)

end Grad.ActualSmoothPhysicalField
