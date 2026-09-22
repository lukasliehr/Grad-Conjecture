import ANP12RotationCommutation

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.RawCircularSectors
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
variable {L sigma gamma ell : ℝ}

/-- Uniform in the raw mode and in every original physical/AP parameter. -/
theorem apSmoothRawVector_bound (mode : ℤ) (field : APSmooth L sigma gamma ell 2) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 2 grade (apSmoothRawVector L sigma gamma ell mode field)‖ ≤
      averageGradeConstant grade * ‖apSmoothGrade L sigma gamma ell 2 grade field‖ := by
  let project := apSmoothGrade L sigma gamma ell 2 grade
  have left := (apSmoothValueMap_bound positiveHelicity
    (apSmoothAngularMode L sigma gamma ell 2 (mode + 1) field) grade).trans
      (mul_le_mul_of_nonneg_left (apSmoothAngularMode_bound (mode + 1) field grade) (norm_nonneg _))
  have right := (apSmoothValueMap_bound negativeHelicity
    (apSmoothAngularMode L sigma gamma ell 2 (mode - 1) field) grade).trans
      (mul_le_mul_of_nonneg_left (apSmoothAngularMode_bound (mode - 1) field grade) (norm_nonneg _))
  have law := project.map_add
    (apSmoothValueMap L sigma gamma ell positiveHelicity (apSmoothAngularMode L sigma gamma ell 2 (mode + 1) field))
    (apSmoothValueMap L sigma gamma ell negativeHelicity (apSmoothAngularMode L sigma gamma ell 2 (mode - 1) field))
  exact (congrArg norm law).le.trans ((norm_add_le _ _).trans
    ((add_le_add left right).trans_eq (by unfold averageGradeConstant; ring)))

theorem capSource_components_bound (grade : ℕ) (source : SmoothCapSource L sigma gamma ell) :
    ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1‖ ≤ ‖capSourceGrade grade source‖ ∧
    ‖apSmoothGrade L sigma gamma ell 1 grade source.2.1‖ ≤ ‖capSourceGrade grade source‖ ∧
    ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) source.2.2‖ ≤ ‖capSourceGrade grade source‖ := by
  have square := capSourceGrade_norm_sq grade source
  have whole := norm_nonneg (capSourceGrade grade source)
  have first := norm_nonneg (apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1)
  have second := norm_nonneg (apSmoothGrade L sigma gamma ell 1 grade source.2.1)
  have third := norm_nonneg (apSmoothGrade L sigma gamma ell 1 (grade + 1) source.2.2)
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith [sq_nonneg ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) source.1‖,
    sq_nonneg ‖apSmoothGrade L sigma gamma ell 1 grade source.2.1‖,
    sq_nonneg ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) source.2.2‖]

def rawSourceBoundConstant (grade : ℕ) : ℝ :=
  averageGradeConstant (grade + 1) + orthogonalGradeConstant grade + orthogonalGradeConstant (grade + 1)

theorem rawSourceBoundConstant_nonnegative (grade : ℕ) : 0 ≤ rawSourceBoundConstant grade :=
  add_nonneg (add_nonneg (averageGradeConstant_nonnegative _) (orthogonalGradeConstant_nonnegative _))
    (orthogonalGradeConstant_nonnegative _)

/-- The native AN8 source norm, with no analytic-width or Sobolev-grade loss. -/
theorem rawSourceProjector_bound (mode : ℤ) (source : SmoothCapSource L sigma gamma ell) (grade : ℕ) :
    ‖capSourceGrade grade (rawSourceProjector L sigma gamma ell mode source)‖ ≤
      rawSourceBoundConstant grade * ‖capSourceGrade grade source‖ := by
  have components := capSource_components_bound grade source
  have first := (apSmoothRawVector_bound mode source.1 (grade + 1)).trans
    (mul_le_mul_of_nonneg_left components.1 (averageGradeConstant_nonnegative _))
  have second := (apSmoothAngularMode_bound mode source.2.1 grade).trans
    (mul_le_mul_of_nonneg_left components.2.1 (orthogonalGradeConstant_nonnegative _))
  have third := (apSmoothAngularMode_bound mode source.2.2 (grade + 1)).trans
    (mul_le_mul_of_nonneg_left components.2.2 (orthogonalGradeConstant_nonnegative _))
  exact (capSourceGrade_norm_le grade _).trans ((add_le_add (add_le_add first second) third).trans_eq
    (by unfold rawSourceBoundConstant; ring))

theorem exceptionalComplement_bound {E F : Type*} [AddCommGroup E] [Module ℂ E]
    [NormedAddCommGroup F] [Module ℂ F] (projector : ℤ → E →ₗ[ℂ] E)
    (measure : E →ₗ[ℂ] F) (constant : ℝ) (field : E)
    (bounded : ∀ mode, ‖measure (projector mode field)‖ ≤ constant * ‖measure field‖) :
    ‖measure (exceptionalComplement projector field)‖ ≤ (1 + 3 * constant) * ‖measure field‖ := by
  change ‖measure (field - (projector 0 field + projector 2 field + projector (-2) field))‖ ≤ _
  rw [map_sub, map_add, map_add]
  have outer := norm_sub_le (measure field) (measure (projector 0 field) + measure (projector 2 field) + measure (projector (-2) field))
  have sum := norm_add_le (measure (projector 0 field) + measure (projector 2 field)) (measure (projector (-2) field))
  have pair := norm_add_le (measure (projector 0 field)) (measure (projector 2 field))
  nlinarith [bounded 0, bounded 2, bounded (-2)]

theorem rawSourceComplement_bound (source : SmoothCapSource L sigma gamma ell) (grade : ℕ) :
    ‖capSourceGrade grade (rawSourceComplement L sigma gamma ell source)‖ ≤
      (1 + 3 * rawSourceBoundConstant grade) * ‖capSourceGrade grade source‖ :=
  exceptionalComplement_bound _ (capSourceGrade grade) _ source (fun mode => rawSourceProjector_bound mode source grade)

end Grad.RawCircularSectors
