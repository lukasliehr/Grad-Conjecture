import AKAC3ActualMatrixConjugatedRegularity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualSmoothPhysicalField
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularWeightedSmoothness Grad.AnnularGeneralSourceRegularity Grad.PhaseAlgebra Grad.AnnularCurrentLow

variable {dimension : ℕ} {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow dimension lower} (curves : SmoothLowPhysicalRow parameters lower positive row)
    (bounded : lower < 1)

def SmoothLowPhysicalRow.physicalCurve (grade : ℕ) (radius : ℝ) : CellL2 dimension :=
  inversePhaseDiagonal parameters dimension 4 radius (curves.curve (grade+4) radius)

include bounded

theorem SmoothLowPhysicalRow.physicalCurve_coefficient (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    curves.physicalCurve grade radius mode =
      (Real.exp (-radialPhase parameters radius mode.2) : ℂ) • curves.curve grade radius mode := by
  rw [SmoothLowPhysicalRow.physicalCurve,inversePhaseDiagonal_coefficient parameters dimension 4 (by omega) radius
    (positive.le.trans inside.1) inside.2,curves.shift bounded grade 4 radius inside mode,mul_smul]
  change (Real.exp (-radialPhase parameters radius mode.2) : ℂ) •
    ((annularFrequency mode.1 mode.2 : ℂ)^4)⁻¹ • ((annularFrequency mode.1 mode.2 : ℂ)^4) • curves.curve grade radius mode = _
  rw [inv_smul_smul₀ (pow_ne_zero 4 (Complex.ofReal_ne_zero.mpr (annularFrequency_pos mode).ne'))]

theorem SmoothLowPhysicalRow.physicalCurve_smooth :
    ∀ grade, ContDiffOn ℝ ∞ (curves.physicalCurve grade) (Icc lower 1) := by
  apply inversePhaseCurve_smooth_of_weighted parameters lower positive bounded curves.curve curves.physicalCurve curves.smooth
  intro grade reserve radius inside mode
  rw [curves.physicalCurve_coefficient bounded grade radius inside mode,
    curves.shift bounded grade reserve radius inside mode,Real.exp_neg,Complex.ofReal_inv,
    smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]
  rfl

theorem SmoothLowPhysicalRow.physicalCurve_actual (grade : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      curves.physicalCurve grade radius mode = (annularFrequency mode.1 mode.2 : ℂ)^grade •
        lowRhoPhysicalCoefficient parameters lower positive row radius mode := by
  filter_upwards [curves.same grade,ae_restrict_mem measurableSet_Icc] with radius same inside
  intro mode
  rw [curves.physicalCurve_coefficient bounded grade radius inside mode,same mode,Real.exp_neg,Complex.ofReal_inv,
    smul_comm ((Real.exp (radialPhase parameters radius mode.2) : ℂ)⁻¹),
    inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')]

theorem SmoothLowPhysicalRow.physicalCurve_grade (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    curves.physicalCurve grade radius mode = (annularFrequency mode.1 mode.2 : ℂ)^grade •
      curves.physicalCurve 0 radius mode := by
  rw [curves.physicalCurve_coefficient bounded grade radius inside mode,
    curves.physicalCurve_coefficient bounded 0 radius inside mode]
  have same := curves.shift bounded 0 grade radius inside mode
  simp only [zero_add] at same
  rw [same]
  exact smul_comm _ _ _

end Grad.ActualSmoothPhysicalField
