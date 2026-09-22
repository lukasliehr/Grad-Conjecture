import AKAK11ActualThirdSourceCurves
import AKAK13ProjectedDeterminantRHS

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators
open Grad.SourceCollarFullSource Grad.BoundaryTrace

private theorem scalarFullField_jointAngular {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (radius : ℝ) :
    Function.Periodic (fun angles : ℝ × ℝ => curves.fullField bounded (radius,angles)) (2*Real.pi,0) := by
  rintro ⟨polar,axial⟩
  simp only [Prod.mk_add_mk,add_zero]
  exact curves.fullField_angular_shift bounded radius polar axial

private theorem scalarFullField_jointCell {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (radius : ℝ) :
    Function.Periodic (fun angles : ℝ × ℝ => curves.fullField bounded (radius,angles)) (0,2*Real.pi) := by
  rintro ⟨polar,axial⟩
  simp only [Prod.mk_add_mk,add_zero]
  exact curves.fullField_cell_shift bounded radius polar axial

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (seven : SmoothLowPhysicalRow parameters lower positive
      (fullStrongSevenInput parameters length lower lengthPositive positive (lowerHalf.trans (by norm_num)) data field))
    (third : SmoothLowPhysicalRow parameters lower positive
      (strongToLow parameters lower positive (lowerHalf.trans (by norm_num)) 0 0 data).ofLp.1.ofLp.2)

/-- Literal (x,c,rV,g) fields of the SAME full seven input and prescribed source. -/
def actualDeterminantFields (radius : ℝ) : Fin 4 → ℝ × ℝ → ComplexEuclidean 1 :=
  ![(fun angles => (seven.bulkUnit (0 : Fin 1) 0).fullField (lowerHalf.trans_lt (by norm_num)) (radius,angles)),
    (fun angles => (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 1).fullField
      (lowerHalf.trans_lt (by norm_num)) (radius,angles)),
    (fun angles => (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 2).fullField
      (lowerHalf.trans_lt (by norm_num)) (radius,angles)),
    (fun angles => third.fullField (lowerHalf.trans_lt (by norm_num)) (radius,angles))]

def actualDeterminantCoefficientCurves (grade : ℕ) (radius : ℝ) : Fin 4 → CellL2 1 :=
  ![(seven.bulkUnit (0 : Fin 1) 0).physicalCurve grade radius,
    (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 1).physicalCurve grade radius,
    (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 2).physicalCurve grade radius,
    third.physicalCurve grade radius]

theorem actualDeterminantFields_smooth (radius : ℝ) (inside : radius ∈ Icc lower 1) (index : Fin 4) :
    ContDiff ℝ ∞ (actualDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state data field seven third radius index) := by
  fin_cases index <;> apply physicalField_angles_smooth _ (lowerHalf.trans_lt (by norm_num)) radius inside

theorem actualDeterminantFields_coefficient (radius : ℝ) (inside : radius ∈ Icc lower 1) (index : Fin 4) (mode : ℤ × ℤ) :
    doubleCoefficient (actualDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state data field seven third radius index) mode =
      actualDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius index mode := by
  fin_cases index <;> apply SmoothLowPhysicalRow.fullField_doubleCoefficient _ (lowerHalf.trans_lt (by norm_num)) radius inside mode

theorem actualDeterminantCoefficientCurves_smooth (grade : ℕ) (index : Fin 4) :
    ContDiffOn ℝ ∞ (fun radius => actualDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third grade radius index) (Icc lower 1) := by
  fin_cases index <;> apply SmoothLowPhysicalRow.physicalCurve_smooth _ (lowerHalf.trans_lt (by norm_num)) grade

theorem actualDeterminantFields_angular (radius : ℝ) (index : Fin 4) :
    Function.Periodic (actualDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state data field seven third radius index) (2*Real.pi,0) := by
  fin_cases index
  · exact scalarFullField_jointAngular (seven.bulkUnit (0 : Fin 1) 0) (lowerHalf.trans_lt (by norm_num)) radius
  · exact scalarFullField_jointAngular (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 1) (lowerHalf.trans_lt (by norm_num)) radius
  · exact scalarFullField_jointAngular (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 2) (lowerHalf.trans_lt (by norm_num)) radius
  · exact scalarFullField_jointAngular third (lowerHalf.trans_lt (by norm_num)) radius

theorem actualDeterminantFields_cell (radius : ℝ) (index : Fin 4) :
    Function.Periodic (actualDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state data field seven third radius index) (0,2*Real.pi) := by
  fin_cases index
  · exact scalarFullField_jointCell (seven.bulkUnit (0 : Fin 1) 0) (lowerHalf.trans_lt (by norm_num)) radius
  · exact scalarFullField_jointCell (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 1) (lowerHalf.trans_lt (by norm_num)) radius
  · exact scalarFullField_jointCell (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 2) (lowerHalf.trans_lt (by norm_num)) radius
  · exact scalarFullField_jointCell third (lowerHalf.trans_lt (by norm_num)) radius

end Grad.ActualPolarEquations
