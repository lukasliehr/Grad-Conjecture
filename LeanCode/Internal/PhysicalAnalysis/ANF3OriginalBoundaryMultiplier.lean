import ANF2OriginalScalarForcing
import ANH13LiteralMultiplier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.ActualScalarForcing
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.CircularHighWeak
variable {L sigma gamma ell : ℝ}

private theorem highBoundary_coordinate_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (mode : ℤ) (field : E) : ‖(highMultiplier mode : ℂ) • field‖ ≤ ‖field‖ := by
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (highMultiplier_nonnegative mode)]
  exact (mul_le_mul_of_nonneg_right (highMultiplier_one_le mode) (norm_nonneg _)).trans_eq (one_mul _)

/-- Literal B Ph on the original weighted AP boundary, at the same grade. -/
def boundaryBLinear (L sigma gamma ell : ℝ) (grade : ℕ) :
    APBoundaryGrade L sigma gamma ell 1 grade →ₗ[ℂ] APBoundaryGrade L sigma gamma ell 1 grade where
  toFun field := ⟨fun pair => (highMultiplier pair.1 : ℂ) • field pair,
    field.property.mono' (fun pair => highBoundary_coordinate_bound pair.1 (field pair))⟩
  map_add' first second := Subtype.ext (funext (fun pair => smul_add _ _ _))
  map_smul' scalar field := by
    apply Subtype.ext
    funext pair
    change (highMultiplier pair.1 : ℂ) • (scalar • field pair) = scalar • ((highMultiplier pair.1 : ℂ) • field pair)
    exact smul_comm _ _ _

def boundaryB (L sigma gamma ell : ℝ) (grade : ℕ) :
    APBoundaryGrade L sigma gamma ell 1 grade →L[ℂ] APBoundaryGrade L sigma gamma ell 1 grade :=
  (boundaryBLinear L sigma gamma ell grade).mkContinuous 1 (fun field => by
    rw [one_mul]
    exact lp.norm_mono (by norm_num) (fun pair => highBoundary_coordinate_bound pair.1 (field pair)))

theorem boundaryB_apply (grade : ℕ) (field : APBoundaryGrade L sigma gamma ell 1 grade) (pair : ℤ × ℤ) :
    boundaryB L sigma gamma ell grade field pair = (highMultiplier pair.1 : ℂ) • field pair := rfl

theorem boundaryB_bound (grade : ℕ) (field : APBoundaryGrade L sigma gamma ell 1 grade) :
    ‖boundaryB L sigma gamma ell grade field‖ ≤ ‖field‖ :=
  lp.norm_mono (by norm_num) (fun pair => highBoundary_coordinate_bound pair.1 (field pair))

theorem boundaryB_coefficient (grade : ℕ) (field : APBoundaryGrade L sigma gamma ell 1 grade) (pair : ℤ × ℤ) :
    apBoundaryCoefficient L sigma gamma ell grade (boundaryB L sigma gamma ell grade field) pair =
      (highMultiplier pair.1 : ℂ) • apBoundaryCoefficient L sigma gamma ell grade field pair := by
  unfold apBoundaryCoefficient
  rw [boundaryB_apply]
  exact smul_comm _ _ _

theorem boundaryB_low (grade : ℕ) (field : APBoundaryGrade L sigma gamma ell 1 grade)
    (pair : ℤ × ℤ) (low : pair.1 ∈ lowAngularModes) :
    boundaryB L sigma gamma ell grade field pair = 0 := by
  rw [boundaryB_apply, highMultiplier, if_pos low]
  simp only [Complex.ofReal_zero, zero_smul]

theorem boundaryB_high_coefficient (grade : ℕ) (field : APBoundaryGrade L sigma gamma ell 1 grade)
    (pair : ℤ × ℤ) (high : pair.1 ∉ lowAngularModes) :
    apBoundaryCoefficient L sigma gamma ell grade (boundaryB L sigma gamma ell grade field) pair =
      ((1 - 4 / (pair.1 : ℝ) ^ 2 : ℝ) : ℂ) • apBoundaryCoefficient L sigma gamma ell grade field pair := by
  rw [boundaryB_coefficient, highMultiplier_high pair.1 high]

end Grad.ActualScalarForcing
