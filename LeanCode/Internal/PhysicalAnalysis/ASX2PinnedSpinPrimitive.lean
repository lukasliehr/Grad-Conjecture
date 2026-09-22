import ASX1SignedEulerDivision

noncomputable section
set_option maxHeartbeats 2400000
set_option maxRecDepth 4000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.ActualCenterVolterra
open Grad.NonlinearDivision (closedOrigin IsRotationInvariant)

def secondModeQuotient {dimension : ℕ} (sign : ℤ) (field : ClosedJet dimension) : ClosedJet dimension :=
  signedQuotient sign 0 (signedQuotient sign 1 field)

theorem secondModeQuotient_factor {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field : ClosedJet dimension) (pure : angularClosedJet (2 * sign) field = field) :
    coordinateMultiplyJet (sign : ℝ) (coordinateMultiplyJet (sign : ℝ)
      (secondModeQuotient sign field)) = field := by
  have firstPure : angularClosedJet ((((1 : ℕ) : ℤ) + 1) * sign) field = field := by
    simpa only [Nat.cast_one, one_add_one_eq_two] using pure
  have nextPure := signedQuotient_mode sign signed 1 field firstPure
  have quotientFactor := signedQuotient_factor sign signed 0 (signedQuotient sign 1 field)
    (by simpa only [Nat.cast_zero, zero_add, Nat.cast_one, one_mul] using nextPure)
  exact (congrArg (coordinateMultiplyJet (sign : ℝ)) quotientFactor).trans
    (signedQuotient_factor sign signed 1 field firstPure)

theorem secondModeQuotient_mean {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field : ClosedJet dimension) (pure : angularClosedJet (2 * sign) field = field) :
    angularClosedJet 0 (secondModeQuotient sign field) = secondModeQuotient sign field := by
  have nextPure := signedQuotient_mode sign signed 1 field
    (by simpa only [Nat.cast_one, one_add_one_eq_two] using pure)
  simpa only [secondModeQuotient, Nat.cast_zero, zero_mul] using
    signedQuotient_mode sign signed 0 (signedQuotient sign 1 field)
      (by simpa only [Nat.cast_zero, zero_add, Nat.cast_one, one_mul] using nextPure)

theorem pureZero_radial {dimension : ℕ} (field : ClosedJet dimension)
    (pure : angularClosedJet 0 field = field) : IsRotationInvariant field := by
  intro angle point
  have covariance := angularClosedJet_rotation_value 0 field angle point
  rw [pure, angularCharacter_zero_mode, one_smul] at covariance
  convert covariance using 1
  congr 1
  apply Subtype.ext
  exact physicalRotation_eq_orthogonal angle point.val

/-- Exact Cartesian identity underlying Y37, before radiality is imposed. -/
theorem signedRaising_radialFactor {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field : ClosedJet dimension) :
    signedLowering (-sign) (coordinateMultiplyJet (sign : ℝ) (radiusPowerJet 1 field)) =
      coordinateMultiplyJet (sign : ℝ) (coordinateMultiplyJet (sign : ℝ)
        (shiftedEulerJet 1 field + (Complex.I * (sign : ℂ)) • rotationJet field)) := by
  simp only [signedLowering, centerDifferential, centerCoordinate_decomposition,
    radiusPower_one_decomposition, shiftedEulerJet, eulerJet, rotationJet, sub_eq_add_neg,
    centerPartial_add, centerPartial_smul, centerPartial_coordinate,
    centerCoordinate_add, centerCoordinate_smul, centerCoordinate_neg]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  have imaginaryCube : Complex.I ^ 3 = -Complex.I := by
    calc Complex.I ^ 3 = Complex.I ^ 2 * Complex.I := by ring
         _ = -Complex.I := by rw [Complex.I_sq]; ring
  rcases signed with rfl | rfl <;>
    simp [closedJet_value_add, closedJet_value_smul, closedJet_value_neg,
      coordinateJet_value, PiLp.add_apply, PiLp.smul_apply, PiLp.neg_apply,
      Complex.real_smul, spatialBasis] <;> ring_nf <;> simp only [Complex.I_sq, imaginaryCube] <;> ring

/-- The literal cubic-factor primitive z_sigma |y|^2 E_2 Q_1 Q_2. -/
def pinnedSpinPrimitive {dimension : ℕ} (sign : ℤ) (field : ClosedJet dimension) : ClosedJet dimension :=
  coordinateMultiplyJet (sign : ℝ) (radiusPowerJet 1 (powerDilationJet 1 (secondModeQuotient sign field)))

theorem pinnedSpinPrimitive_derivative {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (field : ClosedJet dimension) (pure : angularClosedJet (2 * sign) field = field) :
    signedLowering (-sign) (pinnedSpinPrimitive sign field) = field := by
  have radial := powerDilation_radial 1 (secondModeQuotient sign field)
    (pureZero_radial _ (secondModeQuotient_mean sign signed field pure))
  change signedLowering (-sign) (coordinateMultiplyJet (sign : ℝ) (radiusPowerJet 1 _)) = _
  rw [signedRaising_radialFactor sign signed, radial_rotation_zero _ radial,
    smul_zero, add_zero, shiftedEuler_powerDilation]
  exact secondModeQuotient_factor sign signed field pure

theorem pinnedSpinPrimitive_pinned {dimension : ℕ} (sign : ℤ) (field : ClosedJet dimension) :
    CenterPinned (pinnedSpinPrimitive sign field) := by
  apply centerSigned_pinned
  rw [radiusPowerJet_value]
  simp [radiusSquare, closedOrigin]

end Grad.ActualExceptionalInverse
