import AKBJ1SameObservedCartesianXi

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace Grad.ActualScalarWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.BoundaryTrace Grad.SourceCollarFullSource Grad.ActualPhysicalField Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianDescent

/-- Actual axial projection preserves the zero polar mean of a continuous scalar field. -/
theorem scalarAxialCell_zeroAngular (field : ℝ × ℝ → ComplexEuclidean 1)
    (continuousField : Continuous field) (zero : ∀ axial, angularCoefficient (fun polar => field (polar,axial)) 0 = 0)
    (cell : ℤ) :
    angularCoefficient (fun polar => angularCoefficient (fun axial => field (polar,axial)) cell) 0 = 0 := by
  rw [doubleCoefficient_swap field continuousField 0 cell]
  simp_rw [zero]
  exact angularCoefficient_zero cell

/-- Every native Xi/r axial cell retains its genuine zero angular coefficient at every radius. -/
theorem scalarCartesianCell_zeroAngular {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (zero : ∀ cell : ℤ, row (0,cell) = 0)
    (cell : ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    angularCoefficient (fun polar => curves.cartesianCellField bounded cell (polarPlane (radius,polar))) 0 = 0 := by
  have same : (fun polar => curves.cartesianCellField bounded cell (polarPlane (radius,polar))) =
      fun polar => angularCoefficient (fun axial => curves.fullField bounded (radius,polar,axial)) cell := by
    funext polar
    rw [← polarPlane_originalParametrization]
    exact curves.cartesianCellField_actual bounded cell radius inside polar
  rw [same]
  exact scalarAxialCell_zeroAngular _
    ((curves.fullField_smooth bounded).continuousOn.comp_continuous (continuous_const.prodMk continuous_id)
      (fun _ => ⟨inside,mem_univ _⟩))
    (fun axial => fullField_mean_of_zeroAngular curves bounded zero radius inside axial) cell

end Grad.ActualScalarWeakEquations
