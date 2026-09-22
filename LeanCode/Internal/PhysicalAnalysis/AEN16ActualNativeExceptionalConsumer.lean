import AEN15ActualStoredNormBounds

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ExceptionalNative
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualExceptionalInverse Grad.RawCircularSectors
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
variable {L sigma gamma ell : ℝ}

private theorem norm_five_le_sum (value first second third fourth fifth : ℝ)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second) (thirdNonnegative : 0 ≤ third)
    (fourthNonnegative : 0 ≤ fourth) (fifthNonnegative : 0 ≤ fifth)
    (square : value ^ 2 = first ^ 2 + second ^ 2 + third ^ 2 + fourth ^ 2 + fifth ^ 2) :
    value ≤ first + second + third + fourth + fifth := by
  nlinarith [mul_nonneg firstNonnegative secondNonnegative, mul_nonneg firstNonnegative thirdNonnegative,
    mul_nonneg firstNonnegative fourthNonnegative, mul_nonneg firstNonnegative fifthNonnegative,
    mul_nonneg secondNonnegative thirdNonnegative, mul_nonneg secondNonnegative fourthNonnegative,
    mul_nonneg secondNonnegative fifthNonnegative, mul_nonneg thirdNonnegative fourthNonnegative,
    mul_nonneg thirdNonnegative fifthNonnegative, mul_nonneg fourthNonnegative fifthNonnegative]

def exceptionalNativeConstant (L gamma ceiling : ℝ) (grade : ℕ) : ℝ :=
  exceptionalPsiConstant L gamma ceiling grade + exceptionalVectorConstant L gamma ceiling grade +
    exceptionalRotationConstant L gamma ceiling grade + 2

theorem exceptionalNativeConstant_nonnegative (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (grade : ℕ) :
    0 ≤ exceptionalNativeConstant L gamma ceiling grade := add_nonneg
  (add_nonneg (add_nonneg (exceptionalPsiConstant_nonnegative admissible _ _) (exceptionalVectorConstant_nonnegative admissible _ _))
    (exceptionalRotationConstant_nonnegative admissible _ _)) (by norm_num)

/-- AN32 on the original five-slot AP norm and original analytic width.
The single ASX inverse is used for every grade, including zero frequency.
The p ≥ 3 pinned estimate pays exactly for the s ≥ 3 range. -/
theorem actualExceptional_native_bound (admissible : Admissible L sigma gamma ell) (ceiling : ℝ)
    (grade : ℕ) (large : 3 ≤ grade) (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (source : SmoothCapSource L sigma gamma ell) (raw : IsRawSourceSector admissible (2 * sign) source)
    (band : ExceptionalSourceBand admissible ceiling source) :
    compensatedNorm admissible grade (exceptionalInverseLinear admissible sign source) ≤
      exceptionalNativeConstant L gamma ceiling grade * exceptionalSourceSize L sigma gamma ell grade source := by
  have square := compensatedNorm_sq admissible grade (exceptionalState admissible sign source)
  have sum := norm_five_le_sum _ _ _ _ _ _ (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) square
  have estimates := add_le_add (add_le_add (add_le_add (add_le_add
    (exceptionalTheta_native admissible ceiling grade sign signed source raw band)
    (exceptionalVector_native admissible ceiling grade large sign signed source raw band))
    (exceptionalRotation_native admissible ceiling grade large sign signed source raw band))
    (exceptionalScalar_native admissible grade sign signed source))
    (exceptionalScalarRotation_native admissible grade sign signed source raw)
  exact sum.trans (estimates.trans_eq (by unfold exceptionalNativeConstant; ring))

private theorem append_native {A B C D E F : Prop} (original : A ∧ B ∧ C ∧ D ∧ E) (native : F) :
    A ∧ B ∧ C ∧ D ∧ E ∧ F :=
  ⟨original.1, original.2.1, original.2.2.1, original.2.2.2.1, original.2.2.2.2, native⟩

/-- The same actual smooth inverse has all original equations, every high
trace zero, pinned uniqueness, and sharp native estimates at every s ≥ 3. -/
theorem actualExceptional_native_consumer (admissible : Admissible L sigma gamma ell) (ceiling : ℝ)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible) (raw : IsRawSourceSector admissible (2 * sign) source)
    (band : ExceptionalSourceBand admissible ceiling source) :
    exceptionalInverseLinear admissible sign source ∈ circularCompensatedCore admissible ∧
    IsRawStateSector admissible (2 * sign) (exceptionalInverseLinear admissible sign source) ∧
    circularRows admissible (exceptionalInverseLinear admissible sign source) = source ∧
    (∀ grade : ℕ, 1 ≤ grade → circularCoreTrace admissible grade (exceptionalInverseLinear admissible sign source) = 0) ∧
    (∀ state : CompensatedData L sigma gamma ell, state ∈ circularCompensatedCore admissible →
      IsRawStateSector admissible (2 * sign) state → circularRows admissible state = source →
      state = exceptionalInverseLinear admissible sign source) ∧
    (∀ grade : ℕ, 3 ≤ grade → compensatedNorm admissible grade (exceptionalInverseLinear admissible sign source) ≤
      exceptionalNativeConstant L gamma ceiling grade * exceptionalSourceSize L sigma gamma ell grade source) := by
  exact append_native (actualExceptional_consumer admissible sign signed source compatible raw)
    (fun grade large => actualExceptional_native_bound admissible ceiling grade large sign signed source raw band)

end Grad.ExceptionalNative
