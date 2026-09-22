import SmoothAngularAverage
import FP17SmoothReconstruction

noncomputable section

open Set MeasureTheory
open scoped ContDiff Interval Topology

namespace Grad.Constraints

open Grad.ClosedJets Grad.CartesianState

local instance angularCharacterPeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The literal negative angular character in N1. -/
def angularCharacter (mode : ℤ) (angle : ℝ) : ℂ := cellExponential (-mode) angle

@[simp] theorem angularCharacter_zero_mode (angle : ℝ) : angularCharacter 0 angle = 1 := by
  simp [angularCharacter, cellExponential]

@[simp] theorem angularCharacter_zero_angle (mode : ℤ) : angularCharacter mode 0 = 1 := by
  simp [angularCharacter, cellExponential]

@[simp] theorem angularCharacter_norm (mode : ℤ) (angle : ℝ) :
    ‖angularCharacter mode angle‖ = 1 := cellExponential_norm _ _

theorem angularCharacter_smooth (mode : ℤ) : ContDiff ℝ ∞ (angularCharacter mode) := by
  have castSmooth : ContDiff ℝ ∞ (fun angle : ℝ => (angle : ℂ)) := Complex.ofRealCLM.contDiff
  unfold angularCharacter cellExponential
  fun_prop

theorem angularCharacter_periodic (mode : ℤ) :
    Function.Periodic (angularCharacter mode) (2 * Real.pi) := by
  intro angle
  simp only [angularCharacter, ← cellCharacter_coe, AddCircle.coe_add_period]

theorem angularCharacter_add (mode : ℤ) (first second : ℝ) :
    angularCharacter mode (first + second) =
      angularCharacter mode first * angularCharacter mode second := by
  simp only [angularCharacter, cellExponential, Complex.ofReal_add, mul_add, Complex.exp_add]

theorem angularCharacter_mul (first second : ℤ) (angle : ℝ) :
    angularCharacter first angle * angularCharacter second angle =
      angularCharacter (first + second) angle := by
  unfold angularCharacter cellExponential
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem angularCharacter_neg_angle (mode : ℤ) (angle : ℝ) :
    angularCharacter mode (-angle) = angularCharacter (-mode) angle := by
  simp [angularCharacter, cellExponential]

theorem angularCharacter_inverse_factor (mode : ℤ) (first second : ℝ) :
    angularCharacter mode (-second) * angularCharacter mode (first + second) =
      angularCharacter mode first := by
  rw [← angularCharacter_add]
  congr 1
  ring

theorem angularCharacter_normalized_integral {dimension : ℕ} (mode : ℤ)
    (value : ComplexEuclidean dimension) :
    (2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi,
      angularCharacter mode angle • value = if mode = 0 then value else 0 := by
  have orthogonality := fourierCoeff_cellCharacter_smul 0 mode value
  rw [fourierCoeff_eq_intervalIntegral _ mode 0] at orthogonality
  have integrand (angle : ℝ) :
      fourier (-mode) (angle : CellCircle) •
          (cellCharacter 0 (angle : CellCircle) • value) =
        angularCharacter mode angle • value := by
    change cellCharacter (-mode) (angle : CellCircle) •
      (cellCharacter 0 (angle : CellCircle) • value) = _
    rw [cellCharacter_coe]
    simp [cellCharacter, angularCharacter]
  simpa only [zero_add, one_div, integrand, eq_comm] using orthogonality

end Grad.Constraints
