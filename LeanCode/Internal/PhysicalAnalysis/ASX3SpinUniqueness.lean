import ASX2PinnedSpinPrimitive

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.ActualCenterVolterra
open Grad.GaugeCoefficients.Radial
open Grad.NonlinearDivision (closedOrigin IsRotationInvariant laplacianJet)

theorem pure_of_covariance {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension)
    (covariant : ∀ angle point, field.value (rotatedPoint angle point) =
      angularCharacter (-mode) angle • field.value point) : angularClosedJet mode field = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [angularClosedJet_value]
  simp_rw [covariant, ← mul_smul, angularCharacter_mul, add_neg_cancel,
    angularCharacter_zero_mode, one_smul]
  rw [intervalIntegral.integral_const, sub_zero, smul_smul,
    inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_smul]

theorem powerDilation_mode {dimension : ℕ} (power : ℕ) (mode : ℤ) (field : ClosedJet dimension)
    (pure : angularClosedJet mode field = field) :
    angularClosedJet mode (powerDilationJet power field) = powerDilationJet power field := by
  apply pure_of_covariance
  intro angle point
  rw [powerDilationJet_value, powerDilationJet_value, ← integral_smul]
  apply setIntegral_congr_fun measurableSet_Icc
  intro scale inside
  have commute : dilationPoint scale inside.1 inside.2 (rotatedPoint angle point) =
      rotatedPoint angle (dilationPoint scale inside.1 inside.2 point) := by
    apply Subtype.ext
    exact (map_smul (planeRotationEquiv angle) scale point.val).symm
  have covariance := angularClosedJet_rotation_value mode field angle
    (dilationPoint scale inside.1 inside.2 point)
  rw [pure, angularCharacter_neg_angle] at covariance
  change scale ^ power • smoothClosedExtension field (dilationPoint scale inside.1 inside.2 (rotatedPoint angle point)).val =
    angularCharacter (-mode) angle • (scale ^ power • smoothClosedExtension field (dilationPoint scale inside.1 inside.2 point).val)
  rw [smoothClosedExtension_value, smoothClosedExtension_value, commute, covariance, smul_comm]

theorem pinnedSpinPrimitive_mode {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field : ClosedJet dimension) (pure : angularClosedJet (2 * sign) field = field) :
    angularClosedJet sign (pinnedSpinPrimitive sign field) = pinnedSpinPrimitive sign field := by
  have radial := radiusPower_radial 1 _ (powerDilation_radial 1 _
    (pureZero_radial _ (secondModeQuotient_mean sign signed field pure)))
  change angularClosedJet sign (coordinateMultiplyJet (sign : ℝ) _) = _
  rw [signedCoordinate_mode sign signed, sub_self, radial_angularMean _ radial]
  rfl

/-- The two literal signed first-order operators factor the Cartesian Laplacian. -/
theorem signedDerivatives_laplacian {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field : ClosedJet dimension) :
    signedLowering sign (signedLowering (-sign) field) = laplacianJet field := by
  simp only [signedLowering, centerDifferential, sub_eq_add_neg, centerPartial_add,
    centerPartial_smul, centerPartial_neg, centerPartial_commute 1 0]
  unfold laplacianJet
  have imaginarySquare : (Complex.I * (sign : ℂ)) * (Complex.I * (sign : ℂ)) = -1 := by
    rcases signed with rfl | rfl <;> norm_num
  simp only [Int.cast_neg, mul_neg, neg_smul, smul_add, smul_neg, smul_smul]
  rw [imaginarySquare]
  module

theorem signedLowering_sub {dimension : ℕ} (sign : ℤ) (first second : ClosedJet dimension) :
    signedLowering sign (first - second) = signedLowering sign first - signedLowering sign second := by
  simp only [signedLowering, centerDifferential, sub_eq_add_neg, centerPartial_add,
    centerPartial_neg, smul_add, smul_neg]
  abel

theorem signedLowering_zero (dimension : ℕ) (sign : ℤ) : signedLowering sign (0 : ClosedJet dimension) = 0 := by
  simp only [signedLowering, centerDifferential, centerPartial_zero, smul_zero, sub_self]

/-- The only smooth homogeneous signed first mode is the linear jet, which
is removed by the literal pin. The accepted zero-frequency center uniqueness
provides this statement without any singular radial ODE premise. -/
theorem pinnedSpin_unique {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (first second : ClosedJet dimension)
    (firstPure : angularClosedJet sign first = first) (secondPure : angularClosedJet sign second = second)
    (firstPinned : CenterPinned first) (secondPinned : CenterPinned second)
    (sameDerivative : signedLowering (-sign) first = signedLowering (-sign) second) : first = second := by
  have pure : angularClosedJet sign (first - second) = first - second := by
    have difference := (angularClosedJetLinear dimension sign).map_sub first second
    change angularClosedJet sign (first - second) = angularClosedJet sign first - angularClosedJet sign second at difference
    rwa [firstPure, secondPure] at difference
  have differential : signedLowering (-sign) (first - second) = 0 := by
    rw [signedLowering_sub, sameDerivative, sub_self]
  have harmonic : laplacianJet (first - second) = (0 : ℂ) • (first - second) := by
    rw [← signedDerivatives_laplacian sign signed, differential, signedLowering_zero, zero_smul]
  exact sub_eq_zero.mp (centerHomogeneous_zero sign signed 0 (first - second) pure
    (centerPinned_sub first second firstPinned secondPinned) harmonic)

end Grad.ActualExceptionalInverse
