import AEN13ActualExceptionalStageBounds

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ExceptionalNative
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualExceptionalInverse Grad.RawCircularSectors Grad.BoundedScalarInverse
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.RadialLedger
variable {L sigma gamma ell : ℝ}

def exceptionalForcingConstant (L gamma ceiling : ℝ) (grade : ℕ) : ℝ :=
  2 + 2 * bandFrequencySize ceiling * apLoweringConstant grade * exceptionalToroidalConstant L gamma ceiling grade +
    smoothSignedDerivativeConstant L gamma grade * exceptionalFixedConstant L gamma ceiling grade

theorem exceptionalForcingConstant_nonnegative (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (grade : ℕ) :
    0 ≤ exceptionalForcingConstant L gamma ceiling grade := by
  unfold exceptionalForcingConstant
  exact add_nonneg (add_nonneg (by norm_num) (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num)
    (zero_le_one.trans (bandFrequencySize_one_le ceiling))) (apLoweringConstant_nonnegative _))
      (exceptionalToroidalConstant_nonnegative admissible _ _)))
    (mul_nonneg (smoothSignedDerivativeConstant_nonnegative admissible _) (exceptionalFixedConstant_nonnegative admissible _ _))

theorem exceptionalFreeForcing_native (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (grade : ℕ)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) (band : ExceptionalSourceBand admissible ceiling source) :
    ‖apSmoothGrade L sigma gamma ell 1 grade (exceptionalFreeForcing admissible sign source)‖ ≤
      exceptionalForcingConstant L gamma ceiling grade * exceptionalSourceSize L sigma gamma ell grade source := by
  let project := apSmoothGrade L sigma gamma ell 1 grade
  have determinant := (linear_norm_smul_bound project (-2 : ℂ) source.2.1 2 (by norm_num)).trans
    (mul_le_mul_of_nonneg_left (exceptionalSourceSize_slots grade source).2.1 (by norm_num))
  have lower := (smoothOriginal_lower admissible (Nat.le_succ grade) (exceptionalToroidal admissible sign source)).trans
    (mul_le_mul_of_nonneg_left (exceptionalToroidal_native admissible ceiling grade sign signed source raw band) (apLoweringConstant_nonnegative _))
  have axial := (smoothAxial_band_bound admissible ceiling (exceptionalToroidal admissible sign source)
    (exceptionalToroidal_support admissible _ sign source band.1 band.2.2) grade).trans
      (mul_le_mul_of_nonneg_left lower (zero_le_one.trans (bandFrequencySize_one_le ceiling)))
  have toroidal := (linear_norm_smul_bound project (-2 : ℂ)
    (apSmoothAxial L sigma gamma ell 1 (exceptionalToroidal admissible sign source)) 2 (by norm_num)).trans
      (mul_le_mul_of_nonneg_left axial (by norm_num))
  have derivative := (smoothSignedDerivative_bound admissible sign signed (exceptionalFixedSpin admissible sign source) grade).trans
    (mul_le_mul_of_nonneg_left (exceptionalFixed_native admissible ceiling grade sign signed source raw band)
      (smoothSignedDerivativeConstant_nonnegative admissible grade))
  have sum := (linear_norm_add_bound project ((-2 : ℂ) • source.2.1)
    ((-2 : ℂ) • apSmoothAxial L sigma gamma ell 1 (exceptionalToroidal admissible sign source))).trans
      (add_le_add determinant toroidal)
  exact (linear_norm_sub_bound project _ _).trans ((add_le_add sum derivative).trans_eq (by
    unfold exceptionalForcingConstant
    ring))

def exceptionalFreeConstant (L gamma ceiling : ℝ) (grade : ℕ) : ℝ :=
  primitiveBandConstant L gamma ceiling grade (pinnedPrimitiveGainConstant grade) * exceptionalForcingConstant L gamma ceiling grade

theorem exceptionalFreeConstant_nonnegative (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (grade : ℕ) :
    0 ≤ exceptionalFreeConstant L gamma ceiling grade :=
  mul_nonneg (primitiveBandConstant_nonnegative admissible ceiling grade _ (pinnedPrimitiveGainConstant_nonnegative _))
    (exceptionalForcingConstant_nonnegative admissible _ _)

theorem exceptionalFree_native (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (grade : ℕ) (large : 3 ≤ grade)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) (band : ExceptionalSourceBand admissible ceiling source) :
    ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) (exceptionalFreeSpin admissible sign source)‖ ≤
      exceptionalFreeConstant L gamma ceiling grade * exceptionalSourceSize L sigma gamma ell grade source :=
  (pinnedSmooth_original_gain admissible ceiling grade large sign signed (exceptionalFreeForcing admissible sign source)
    (exceptionalFreeForcing_mode admissible sign signed source raw)
    (exceptionalFreeForcing_support admissible _ sign source band.1 band.2.1 band.2.2)).trans
      ((mul_le_mul_of_nonneg_left (exceptionalFreeForcing_native admissible ceiling grade sign signed source raw band)
        (primitiveBandConstant_nonnegative admissible ceiling grade _ (pinnedPrimitiveGainConstant_nonnegative grade))).trans_eq
          (mul_assoc _ _ _).symm)

end Grad.ExceptionalNative
