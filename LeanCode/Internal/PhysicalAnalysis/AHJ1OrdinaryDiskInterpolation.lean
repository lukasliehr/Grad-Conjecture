import AHC9ActualMultiplierConsumer
import BL24FiniteCore
import OriginalInterpolation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope
open Grad.BoundaryLift Grad.BoundaryTrace Grad.NonlinearProduct Grad.FourierInterpolation

/-- The actual Cartesian derivative row with an arbitrary frequency mass.
At mass kappa_n, evaluated on W_n u_n, this is exactly the original AP row. -/
def apMassRow {dimension : ℕ} (mass : ℝ) (grade : ℕ) (field : ClosedJet dimension) : APRow dimension grade :=
  WithLp.toLp 2 (fun index => (mass : ℂ) ^ (grade - derivativeOrder index) •
    closedDerivativeL2 (derivativeMultiIndex index) field)

theorem apRowLinear_eq_mass {dimension grade : ℕ} (L sigma gamma ell : ℝ) (cell : ℤ)
    (field : ClosedJet dimension) :
    apRowLinear (grade := grade) L sigma gamma ell cell field =
      apMassRow (scaledCellWeight L ell cell) grade (apWeightedJet sigma gamma ell cell field) := rfl

/-- An auxiliary fixed admissible phase, used only to invoke the accepted
ordinary disk interpolation through its zero-cell core. It is immediately
removed, and never changes the physical cap phase. -/
def apInterpolationPhase : PhaseParameters where
  length := 1
  sigma0 := 2
  gamma := 1 / 2
  length_pos := by norm_num
  sigma0_pos := by norm_num
  gamma_pos := by norm_num
  gamma_lt_min := by norm_num

def apOrdinaryInterpolationCore {dimension : ℕ} (field : ClosedJet dimension) : ACore apInterpolationPhase dimension :=
  singletonOriginalCore apInterpolationPhase 0 (phaseInverseWeightedJet apInterpolationPhase 0 field)

theorem apMassRow_one_original_norm {dimension : ℕ} (field : ClosedJet dimension) (grade : ℕ) :
    ‖apMassRow 1 grade field‖ = originalGradeNorm grade (apOrdinaryInterpolationCore field) := by
  have row : cellGradeRowLinear (grade := grade) apInterpolationPhase 0
      (phaseInverseWeightedJet apInterpolationPhase 0 field) = apMassRow 1 grade field := by
    apply PiLp.ext
    intro index
    rw [cellGradeRowLinear_apply, phaseWeightedJet_inverse_left]
    simp only [cellFrequency_formula, Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero, Real.sqrt_one, Complex.ofReal_one, one_pow, one_smul]
    change _ = (1 : ℂ) ^ (grade - derivativeOrder index) • closedDerivativeL2 (derivativeMultiIndex index) field
    simp only [one_pow, one_smul]
    rfl
  have squared := originalGrade_norm_sq_eq_rows (grade := grade) apInterpolationPhase (apOrdinaryInterpolationCore field)
  have sum : (∑' cell : ℤ, ‖cellGradeRowLinear (grade := grade) apInterpolationPhase cell
      ((apOrdinaryInterpolationCore field).val cell)‖ ^ 2) = ‖apMassRow 1 grade field‖ ^ 2 := by
    rw [tsum_eq_single (0 : ℤ)]
    · change ‖cellGradeRowLinear (grade := grade) apInterpolationPhase 0
        (phaseInverseWeightedJet apInterpolationPhase 0 field)‖ ^ 2 = _
      rw [row]
    · intro cell nonzero
      change ‖cellGradeRowLinear (grade := grade) apInterpolationPhase cell
        (if cell = 0 then phaseInverseWeightedJet apInterpolationPhase 0 field else 0)‖ ^ 2 = 0
      rw [if_neg nonzero, map_zero, norm_zero, zero_pow (by norm_num)]
  have equality := squared.trans sum
  change (originalGradeNorm grade (apOrdinaryInterpolationCore field)) ^ 2 = _ at equality
  nlinarith [norm_nonneg (apMassRow 1 grade field),
    originalGradeNorm_nonnegative grade (apOrdinaryInterpolationCore field)]

/-- Accepted P17 specializes to ordinary disk jets, exactly in the sum of
Cartesian L2 derivative squares. No new extension theorem is required. -/
theorem apOrdinaryRow_interpolation {dimension low middle high : ℕ}
    (lowMiddle : low < middle) (middleHigh : middle < high) (field : ClosedJet dimension) :
    ‖apMassRow 1 middle field‖ ≤ originalInterpolationConstant low middle high *
      (‖apMassRow 1 low field‖ ^ (1 - interpolationTheta low middle high) *
        ‖apMassRow 1 high field‖ ^ interpolationTheta low middle high) := by
  simp only [apMassRow_one_original_norm]
  exact original_grade_interpolation lowMiddle middleHigh (apOrdinaryInterpolationCore field)

end Grad.GaugeCoefficients.Physical.RadialLedger
