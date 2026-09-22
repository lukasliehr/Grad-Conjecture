import AEN14ActualPinnedStageBound

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.ExceptionalNative
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualExceptionalInverse Grad.RawCircularSectors
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
variable {L sigma gamma ell : ℝ}

def planarSpinConstant : ℝ := ‖matrixUnit (input := 1) (output := 2) 0 0‖ + ‖matrixUnit (input := 1) (output := 2) 1 0‖

theorem planarSpinConstant_nonnegative : 0 ≤ planarSpinConstant := add_nonneg (norm_nonneg _) (norm_nonneg _)

theorem smoothPlanarFromSpins_bound (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (first second : APSmooth L sigma gamma ell 1) (grade : ℕ) :
    ‖apSmoothGrade L sigma gamma ell 2 grade (smoothPlanarFromSpins L sigma gamma ell sign first second)‖ ≤
      planarSpinConstant * (‖apSmoothGrade L sigma gamma ell 1 grade first‖ + ‖apSmoothGrade L sigma gamma ell 1 grade second‖) := by
  let project := apSmoothGrade L sigma gamma ell 2 grade
  have left := (linear_norm_smul_bound project (1 / 2 : ℂ)
    (apSmoothValueMap L sigma gamma ell (matrixUnit (input := 1) (output := 2) 0 0) (first + second)) 1 (by norm_num)).trans
      ((one_mul _).le.trans ((apSmoothValueMap_bound (matrixUnit (input := 1) (output := 2) 0 0) (first + second) grade).trans
        (mul_le_mul_of_nonneg_left (linear_norm_add_bound (apSmoothGrade L sigma gamma ell 1 grade) first second) (norm_nonneg _))))
  have right := (linear_norm_smul_bound project (2 * Complex.I * (sign : ℂ))⁻¹
    (apSmoothValueMap L sigma gamma ell (matrixUnit (input := 1) (output := 2) 1 0) (first - second)) 1 (signedHalfInverse_norm sign signed)).trans
      ((one_mul _).le.trans ((apSmoothValueMap_bound (matrixUnit (input := 1) (output := 2) 1 0) (first - second) grade).trans
        (mul_le_mul_of_nonneg_left (linear_norm_sub_bound (apSmoothGrade L sigma gamma ell 1 grade) first second) (norm_nonneg _))))
  exact (linear_norm_add_bound project _ _).trans ((add_le_add left right).trans_eq (by unfold planarSpinConstant; ring))

def exceptionalVectorConstant (L gamma ceiling : ℝ) (grade : ℕ) : ℝ :=
  planarSpinConstant * (exceptionalFixedConstant L gamma ceiling grade + exceptionalFreeConstant L gamma ceiling grade) +
    gradientBoundConstant L gamma (grade + 1) * exceptionalPsiConstant L gamma ceiling grade

theorem exceptionalVectorConstant_nonnegative (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (grade : ℕ) :
    0 ≤ exceptionalVectorConstant L gamma ceiling grade :=
  add_nonneg (mul_nonneg planarSpinConstant_nonnegative (add_nonneg (exceptionalFixedConstant_nonnegative admissible _ _)
    (exceptionalFreeConstant_nonnegative admissible _ _)))
    (mul_nonneg (gradientBoundConstant_nonnegative admissible _) (exceptionalPsiConstant_nonnegative admissible _ _))

theorem exceptionalVector_native (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (grade : ℕ) (large : 3 ≤ grade)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) (band : ExceptionalSourceBand admissible ceiling source) :
    ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) (apSmoothPlanar L sigma gamma ell (exceptionalState admissible sign source).2)‖ ≤
      exceptionalVectorConstant L gamma ceiling grade * exceptionalSourceSize L sigma gamma ell grade source := by
  have planar := (smoothPlanarFromSpins_bound sign signed (exceptionalFixedSpin admissible sign source)
    (exceptionalFreeSpin admissible sign source) (grade + 1)).trans
      (mul_le_mul_of_nonneg_left (add_le_add (exceptionalFixed_native admissible ceiling grade sign signed source raw band)
        (exceptionalFree_native admissible ceiling grade large sign signed source raw band)) planarSpinConstant_nonnegative)
  have gradient := (apSmoothGradient_bound admissible (exceptionalTheta admissible sign source) (grade + 1)).trans
    (mul_le_mul_of_nonneg_left (exceptionalTheta_native admissible ceiling grade sign signed source raw band)
      (gradientBoundConstant_nonnegative admissible _))
  have literal := congrArg (fun field => ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) field‖)
    (exceptionalState_planar admissible sign source)
  exact literal.le.trans ((linear_norm_sub_bound (apSmoothGrade L sigma gamma ell 2 (grade + 1)) _ _).trans
    ((add_le_add planar gradient).trans_eq (by unfold exceptionalVectorConstant; ring)))

theorem exceptionalScalar_native (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell) :
    ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) (apSmoothScalar L sigma gamma ell (exceptionalState admissible sign source).2)‖ ≤
      exceptionalSourceSize L sigma gamma ell grade source := by
  have literal := congrArg (fun field => ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) field‖)
    (exceptionalState_scalar admissible sign source)
  exact literal.le.trans ((linear_norm_smul_bound (apSmoothGrade L sigma gamma ell 1 (grade + 1)) _ _ 1
    (signedHalfInverse_norm sign signed)).trans ((one_mul _).le.trans (exceptionalSourceSize_slots grade source).2.2))

private theorem solve_rotation {E : Type*} [AddCommGroup E] [Module ℂ E] (gradient rotation quarter forcing : E)
    (equation : (-2 : ℂ) • gradient - (rotation + quarter) = forcing) :
    rotation = (-2 : ℂ) • gradient - quarter - forcing := by
  calc rotation = (-2 : ℂ) • gradient - quarter - ((-2 : ℂ) • gradient - (rotation + quarter)) := by abel
       _ = _ := by rw [equation]

def exceptionalRotationConstant (L gamma ceiling : ℝ) (grade : ℕ) : ℝ :=
  2 * ‖quarterValueMap‖ * gradientBoundConstant L gamma (grade + 1) * exceptionalPsiConstant L gamma ceiling grade +
    ‖quarterValueMap‖ * exceptionalVectorConstant L gamma ceiling grade + 1

theorem exceptionalRotationConstant_nonnegative (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (grade : ℕ) :
    0 ≤ exceptionalRotationConstant L gamma ceiling grade :=
  add_nonneg (add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _))
    (gradientBoundConstant_nonnegative admissible _)) (exceptionalPsiConstant_nonnegative admissible _ _))
    (mul_nonneg (norm_nonneg _) (exceptionalVectorConstant_nonnegative admissible _ _))) zero_le_one

/-- The exact original force row AN5 controls Rv without losing a grade. -/
theorem exceptionalRotation_native (admissible : Admissible L sigma gamma ell) (ceiling : ℝ) (grade : ℕ) (large : 3 ≤ grade)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) (band : ExceptionalSourceBand admissible ceiling source) :
    ‖apSmoothGrade L sigma gamma ell 2 (grade + 1) (apSmoothRotation admissible 2
      (apSmoothPlanar L sigma gamma ell (exceptionalState admissible sign source).2))‖ ≤
      exceptionalRotationConstant L gamma ceiling grade * exceptionalSourceSize L sigma gamma ell grade source := by
  let vector := apSmoothPlanar L sigma gamma ell (exceptionalState admissible sign source).2
  let gradient := apSmoothQuarter L sigma gamma ell (apSmoothGradient admissible (exceptionalTheta admissible sign source))
  let project := apSmoothGrade L sigma gamma ell 2 (grade + 1)
  have equation : (-2 : ℂ) • gradient - (apSmoothRotation admissible 2 vector + apSmoothQuarter L sigma gamma ell vector) = source.1 :=
    exceptionalState_forceInner admissible sign signed source raw
  have literal := solve_rotation gradient (apSmoothRotation admissible 2 vector) (apSmoothQuarter L sigma gamma ell vector) source.1 equation
  have theta := (apSmoothGradient_bound admissible (exceptionalTheta admissible sign source) (grade + 1)).trans
    (mul_le_mul_of_nonneg_left (exceptionalTheta_native admissible ceiling grade sign signed source raw band)
      (gradientBoundConstant_nonnegative admissible _))
  have first := (linear_norm_smul_bound project (-2 : ℂ) gradient 2 (by norm_num)).trans
    (mul_le_mul_of_nonneg_left ((apSmoothValueMap_bound quarterValueMap _ (grade + 1)).trans
      (mul_le_mul_of_nonneg_left theta (norm_nonneg _))) (by norm_num))
  have second := (apSmoothValueMap_bound quarterValueMap vector (grade + 1)).trans
    (mul_le_mul_of_nonneg_left (exceptionalVector_native admissible ceiling grade large sign signed source raw band) (norm_nonneg _))
  exact (congrArg (fun value => ‖project value‖) literal).le.trans ((linear_norm_sub_bound project _ _).trans
    ((add_le_add ((linear_norm_sub_bound project _ _).trans (add_le_add first second))
      (exceptionalSourceSize_slots grade source).1).trans_eq (by unfold exceptionalRotationConstant; ring)))

theorem exceptionalScalarRotation_native (admissible : Admissible L sigma gamma ell) (grade : ℕ)
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) (apSmoothRotation admissible 1
      (apSmoothScalar L sigma gamma ell (exceptionalState admissible sign source).2))‖ ≤
      exceptionalSourceSize L sigma gamma ell grade source := by
  have literal := congrArg (fun field => ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) field‖)
    (exceptionalState_third admissible sign signed source raw)
  exact literal.le.trans (exceptionalSourceSize_slots grade source).2.2

end Grad.ExceptionalNative
