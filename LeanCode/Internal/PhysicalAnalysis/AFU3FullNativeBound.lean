import AFU2ActualFullReferenceState

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
namespace Grad.FullReferenceAssembly
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.GaugeCoefficients.Envelope
open Grad.ActualForcingSupport Grad.BoundedScalarInverse Grad.RawCircularSectors
open Grad.ExceptionalNative Grad.ActualMeanInverse Grad.ActualExceptionalInverse
open Grad.ActualReferenceAssembly Grad.ActualScalarForcing Grad.ActualNonexceptionalInverse
variable {L sigma gamma ell : ℝ}

theorem exceptionalSourceSize_cap_bound (grade : ℕ) (source : SmoothCapSource L sigma gamma ell) :
    exceptionalSourceSize L sigma gamma ell grade source ≤ 3 * ‖capSourceGrade grade source‖ := by
  have slots := capSource_components_bound grade source
  exact (add_le_add (add_le_add slots.1 slots.2.1) slots.2.2).trans_eq (by ring)

theorem exceptionalProjected_native_bound (admissible : Admissible L sigma gamma ell) (ceiling : ℝ)
    (source : SmoothCapSource L sigma gamma ell) (band : OriginalCapSourceBand admissible ceiling source)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (grade : ℕ) (large : 3 ≤ grade) :
    compensatedNorm admissible grade (exceptionalInverseLinear admissible sign
      (rawSourceProjector L sigma gamma ell (2 * sign) source)) ≤
        (3 * exceptionalNativeConstant L gamma ceiling grade * rawSourceBoundConstant grade) * ‖capSourceGrade grade source‖ := by
  have sourceBound := (exceptionalSourceSize_cap_bound grade (rawSourceProjector L sigma gamma ell (2 * sign) source)).trans
    (mul_le_mul_of_nonneg_left (rawSourceProjector_bound (2 * sign) source grade) (by norm_num))
  exact (actualExceptional_native_bound admissible ceiling grade large sign signed _
    (rawSourceProjector_sector admissible (2 * sign) source)
    (capSourceBand_exceptional admissible ceiling _ (rawSourceProjector_band admissible ceiling source band (2 * sign)))).trans
      ((mul_le_mul_of_nonneg_left sourceBound (exceptionalNativeConstant_nonnegative admissible ceiling grade)).trans_eq (by ring))

def fullReferenceNativeConstant (L gamma ceiling : ℝ) (grade : ℕ) (large : 3 ≤ grade) : ℝ :=
  rawSourceBoundConstant grade + 6 * exceptionalNativeConstant L gamma ceiling grade * rawSourceBoundConstant grade +
    nonexceptionalNativeConstant L gamma ceiling grade large * (2 + 3 * rawSourceBoundConstant grade)

private theorem collect_four (value first second third fourth source boundary a b c d e : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) (he : 0 ≤ e)
    (hs : 0 ≤ source) (ht : 0 ≤ boundary) (sum : value ≤ first + second + third + fourth)
    (one : first ≤ a * source) (two : second ≤ b * source) (three : third ≤ c * source)
    (four : fourth ≤ d * (e * source + boundary)) :
    value ≤ (a + b + c + d * (e + 1)) * (source + boundary) := by
  have total : source ≤ source + boundary := le_add_of_nonneg_right ht
  have inside : e * source + boundary ≤ (e + 1) * (source + boundary) := by nlinarith [mul_nonneg he ht]
  exact sum.trans ((add_le_add (add_le_add (add_le_add (one.trans (mul_le_mul_of_nonneg_left total ha))
    (two.trans (mul_le_mul_of_nonneg_left total hb))) (three.trans (mul_le_mul_of_nonneg_left total hc)))
      (four.trans (mul_le_mul_of_nonneg_left inside hd))).trans_eq (by ring))

/-- The actual full reference right inverse satisfies the original same-grade
five-slot estimate, including mean and both exceptional sectors. -/
theorem fullReferenceState_native_bound (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (parameters : PhaseParameters)
    (source : SmoothCapSource L sigma gamma ell) (compatible : source ∈ smoothCapSourceCore admissible)
    (band : OriginalCapSourceBand admissible ceiling source) (beta : BandSmoothBoundary L sigma gamma ell)
    (betaBand : OriginalBoundaryBand ceiling beta) (grade : ℕ) (large : 3 ≤ grade) :
    compensatedNorm admissible grade (fullReferenceState admissible ceiling parameters source beta) ≤
      fullReferenceNativeConstant L gamma ceiling grade large * (‖capSourceGrade grade source‖ + ‖beta.grade grade‖) := by
  let p := rawSourceProjector L sigma gamma ell
  have mean := (meanState_source_norm_bound admissible (p 0 source) (rawSourceProjector_preserves admissible 0 source compatible)
    (rawSource_zero_mean admissible _ (rawSourceProjector_sector admissible 0 source)) grade).trans (rawSourceProjector_bound 0 source grade)
  have positive := exceptionalProjected_native_bound admissible ceiling source band 1 (Or.inl rfl) grade large
  have negative := exceptionalProjected_native_bound admissible ceiling source band (-1) (Or.inr rfl) grade large
  have tail := (actualNonexceptional_native_bound admissible ceiling parameters (rawSourceComplement L sigma gamma ell source)
    (rawSourceComplement_preserves admissible source compatible) (rawSourceComplement_avoids admissible source)
    (rawSourceComplement_band admissible ceiling source band) beta betaBand grade large).trans
      (mul_le_mul_of_nonneg_left (add_le_add (rawSourceComplement_bound source grade) le_rfl) (by
        unfold nonexceptionalNativeConstant
        exact mul_nonneg (reconstructionConstant_nonnegative admissible grade)
          (add_nonneg (mul_nonneg (bandScalarGainConstant_nonnegative L gamma ceiling (admissible_gamma_nonnegative admissible) grade large)
            (add_nonneg (add_nonneg (forcingConstant_nonnegative admissible grade)
              (Grad.SameCellFixedMultiplication.boundaryResponseConstant_nonnegative grade)) zero_le_one)) (by norm_num))))
  let first := meanInverseLinear L sigma gamma ell (p 0 source)
  let second := exceptionalInverseLinear admissible 1 (p 2 source)
  let third := exceptionalInverseLinear admissible (-1) (p (-2) source)
  let fourth := actualNonexceptionalState admissible ceiling parameters (rawSourceComplement L sigma gamma ell source)
    (rawSourceComplement_avoids admissible source) beta
  have triangle : compensatedNorm admissible grade (fullReferenceState admissible ceiling parameters source beta) ≤
      compensatedNorm admissible grade first + compensatedNorm admissible grade second +
        compensatedNorm admissible grade third + compensatedNorm admissible grade fourth :=
    (compensatedNorm_triangle admissible grade _ _).trans
    (add_le_add ((compensatedNorm_triangle admissible grade _ _).trans
      (add_le_add (compensatedNorm_triangle admissible grade _ _) le_rfl)) le_rfl)
  have coefficient : 0 ≤ 3 * exceptionalNativeConstant L gamma ceiling grade * rawSourceBoundConstant grade :=
    mul_nonneg (mul_nonneg (by norm_num) (exceptionalNativeConstant_nonnegative admissible ceiling grade)) (rawSourceBoundConstant_nonnegative grade)
  have restCoefficient : 0 ≤ nonexceptionalNativeConstant L gamma ceiling grade large := by
    unfold nonexceptionalNativeConstant
    exact mul_nonneg (reconstructionConstant_nonnegative admissible grade)
      (add_nonneg (mul_nonneg (bandScalarGainConstant_nonnegative L gamma ceiling (admissible_gamma_nonnegative admissible) grade large)
        (add_nonneg (add_nonneg (forcingConstant_nonnegative admissible grade)
          (Grad.SameCellFixedMultiplication.boundaryResponseConstant_nonnegative grade)) zero_le_one)) (by norm_num))
  have combined := collect_four _ _ _ _ _ _ _ _ _ _ _ _ (rawSourceBoundConstant_nonnegative grade) coefficient coefficient restCoefficient
    (add_nonneg zero_le_one (mul_nonneg (by norm_num) (rawSourceBoundConstant_nonnegative grade)))
    (norm_nonneg _) (norm_nonneg _) triangle mean positive negative tail
  exact combined.trans_eq (by unfold fullReferenceNativeConstant; ring)

end Grad.FullReferenceAssembly
