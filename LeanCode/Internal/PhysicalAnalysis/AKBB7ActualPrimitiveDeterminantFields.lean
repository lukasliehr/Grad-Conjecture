import AKBB6LiteralPrimitiveDeterminantRHS

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators
open Grad.SourceCollarFullSource Grad.BoundaryTrace Grad.ActualPolarEquations

private theorem primitiveFullField_jointAngular {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 1 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1) (radius : ℝ) :
    Function.Periodic (fun angles : ℝ × ℝ => curves.fullField bounded (radius,angles)) (2*Real.pi,0) := by
  rintro ⟨polar,axial⟩
  simp only [Prod.mk_add_mk,add_zero]
  exact curves.fullField_angular_shift bounded radius polar axial

private theorem primitiveFullField_jointCell {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
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

/-- Literal (p,b3,rV,g) fields of the SAME full seven input and prescribed source. -/
def actualPrimitiveDeterminantFields (radius : ℝ) : Fin 4 → ℝ × ℝ → ComplexEuclidean 1 :=
  ![(fun angles => (seven.correctedP parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state).fullField (lowerHalf.trans_lt (by norm_num)) (radius,angles)),
    (fun angles => (seven.bThree parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state).fullField
      (lowerHalf.trans_lt (by norm_num)) (radius,angles)),
    (fun angles => (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 2).fullField
      (lowerHalf.trans_lt (by norm_num)) (radius,angles)),
    (fun angles => third.fullField (lowerHalf.trans_lt (by norm_num)) (radius,angles))]

def actualPrimitiveDeterminantCoefficientCurves (grade : ℕ) (radius : ℝ) : Fin 4 → CellL2 1 :=
  ![(seven.correctedP parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state).physicalCurve grade radius,
    (seven.bThree parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state).physicalCurve grade radius,
    (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 2).physicalCurve grade radius,
    third.physicalCurve grade radius]

theorem actualPrimitiveDeterminantFields_smooth (radius : ℝ) (inside : radius ∈ Icc lower 1) (index : Fin 4) :
    ContDiff ℝ ∞ (actualPrimitiveDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state data field seven third radius index) := by
  fin_cases index <;> apply physicalField_angles_smooth _ (lowerHalf.trans_lt (by norm_num)) radius inside

theorem actualPrimitiveDeterminantFields_coefficient (radius : ℝ) (inside : radius ∈ Icc lower 1) (index : Fin 4) (mode : ℤ × ℤ) :
    doubleCoefficient (actualPrimitiveDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state data field seven third radius index) mode =
      actualPrimitiveDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third 0 radius index mode := by
  fin_cases index <;> apply SmoothLowPhysicalRow.fullField_doubleCoefficient _ (lowerHalf.trans_lt (by norm_num)) radius inside mode

theorem actualPrimitiveDeterminantCoefficientCurves_smooth (grade : ℕ) (index : Fin 4) :
    ContDiffOn ℝ ∞ (fun radius => actualPrimitiveDeterminantCoefficientCurves parameters length compact lower positive lowerHalf lengthPositive state data field seven third grade radius index) (Icc lower 1) := by
  fin_cases index <;> apply SmoothLowPhysicalRow.physicalCurve_smooth _ (lowerHalf.trans_lt (by norm_num)) grade

theorem actualPrimitiveDeterminantFields_angular (radius : ℝ) (index : Fin 4) :
    Function.Periodic (actualPrimitiveDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state data field seven third radius index) (2*Real.pi,0) := by
  fin_cases index
  · exact primitiveFullField_jointAngular (seven.correctedP parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state) (lowerHalf.trans_lt (by norm_num)) radius
  · exact primitiveFullField_jointAngular (seven.bThree parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state) (lowerHalf.trans_lt (by norm_num)) radius
  · exact primitiveFullField_jointAngular (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 2) (lowerHalf.trans_lt (by norm_num)) radius
  · exact primitiveFullField_jointAngular third (lowerHalf.trans_lt (by norm_num)) radius

theorem actualPrimitiveDeterminantFields_cell (radius : ℝ) (index : Fin 4) :
    Function.Periodic (actualPrimitiveDeterminantFields parameters length compact lower positive lowerHalf lengthPositive state data field seven third radius index) (0,2*Real.pi) := by
  fin_cases index
  · exact primitiveFullField_jointCell (seven.correctedP parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state) (lowerHalf.trans_lt (by norm_num)) radius
  · exact primitiveFullField_jointCell (seven.bThree parameters length compact lower positive (lowerHalf.trans_lt (by norm_num)) state) (lowerHalf.trans_lt (by norm_num)) radius
  · exact primitiveFullField_jointCell (SmoothLowPhysicalRow.originalPhysicalRow parameters length compact lower positive lowerHalf state seven 2) (lowerHalf.trans_lt (by norm_num)) radius
  · exact primitiveFullField_jointCell third (lowerHalf.trans_lt (by norm_num)) radius

end Grad.ActualPolarFlux
