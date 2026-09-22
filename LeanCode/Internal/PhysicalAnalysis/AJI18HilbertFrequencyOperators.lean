import AJI17SamePhysicalInsertedGrades
import BL42CoefficientOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryLift

variable (parameters : PhaseParameters) (dimension : ℕ)

def boundedHilbertMultiplier (symbol : ℤ × ℤ → ℂ) (bound : ℝ)
    (nonnegative : 0 ≤ bound) (bounded : ∀ mode, ‖symbol mode‖ ≤ bound) :
    CellL2 dimension →L[ℂ] CellL2 dimension :=
  coefficientOperator parameters 0 (Equiv.refl _) (fun mode => symbol mode • ContinuousLinearMap.id ℂ (ComplexEuclidean dimension))
    nonnegative (fun mode => (ContinuousLinearMap.opNorm_smul_le _ _).trans
      ((mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_id_le : ‖ContinuousLinearMap.id ℂ (ComplexEuclidean dimension)‖ ≤ 1)
        (norm_nonneg (symbol mode))).trans (by simpa only [mul_one] using bounded mode)))

theorem boundedHilbertMultiplier_apply (symbol : ℤ × ℤ → ℂ) (bound : ℝ)
    (nonnegative : 0 ≤ bound) (bounded : ∀ mode, ‖symbol mode‖ ≤ bound)
    (field : CellL2 dimension) (mode : ℤ × ℤ) :
    boundedHilbertMultiplier parameters dimension symbol bound nonnegative bounded field mode = symbol mode • field mode := rfl

def frequencyRatioSymbol (axis : Option Bool) (mode : ℤ × ℤ) : ℂ :=
  (match axis with | none => 1 | some false => Complex.I * (mode.1 : ℂ) | some true => Complex.I * (mode.2 : ℂ)) /
    (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)

theorem frequencyRatioSymbol_bound (axis : Option Bool) (mode : ℤ × ℤ) : ‖frequencyRatioSymbol axis mode‖ ≤ 1 := by
  have positive := Grad.SourceBoundaryTrace.annularFrequency_pos mode
  have realNorm : ‖(Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)‖ =
      Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 := by
    rw [Complex.norm_real, Real.norm_of_nonneg positive.le]
  change ‖(match axis with | none => 1 | some false => Complex.I * (mode.1 : ℂ) | some true => Complex.I * (mode.2 : ℂ)) /
    (Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 : ℂ)‖ ≤ 1
  rw [norm_div, realNorm, div_le_one positive]
  cases axis with
  | none =>
    simp only [norm_one]
    change 1 ≤ 1 + |(mode.1 : ℝ)| + |(mode.2 : ℝ)|
    linarith [abs_nonneg (mode.1 : ℝ), abs_nonneg (mode.2 : ℝ)]
  | some axis =>
    cases axis <;> simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_intCast]
    all_goals
      change _ ≤ 1 + |(mode.1 : ℝ)| + |(mode.2 : ℝ)|
      norm_cast
      have first := abs_nonneg mode.1
      have second := abs_nonneg mode.2
      omega

/-- A single polynomial-grade drop, or one angular/cell derivative followed
by that drop. These act on the same Fourier coefficients. -/
def hilbertFrequencyOperator (axis : Option Bool) : CellL2 dimension →L[ℂ] CellL2 dimension :=
  boundedHilbertMultiplier parameters dimension (frequencyRatioSymbol axis) 1 zero_le_one (frequencyRatioSymbol_bound axis)

theorem hilbertFrequencyOperator_apply (axis : Option Bool) (field : CellL2 dimension) (mode : ℤ × ℤ) :
    hilbertFrequencyOperator parameters dimension axis field mode = frequencyRatioSymbol axis mode • field mode := rfl

end Grad.AnnularSmoothCore
