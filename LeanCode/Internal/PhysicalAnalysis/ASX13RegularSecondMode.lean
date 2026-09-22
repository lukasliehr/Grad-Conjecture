import ASX12PureModeAxis

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct Grad.NonlinearRadial
open Grad.ActualCenterVolterra Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.FlatSourceProjection
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Envelope

/-- The literal regular Y34 second-mode primitive E_2(z_sigma f). -/
def regularSecondPrimitive {dimension : ℕ} (sign : ℤ) (forcing : ClosedJet dimension) : ClosedJet dimension :=
  powerDilationJet 1 (coordinateMultiplyJet (sign : ℝ) forcing)

theorem regularSecondPrimitive_mode {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (forcing : ClosedJet dimension) (pure : angularClosedJet sign forcing = forcing) :
    angularClosedJet (2 * sign) (regularSecondPrimitive sign forcing) = regularSecondPrimitive sign forcing := by
  apply powerDilation_mode
  have shift : 2 * sign - sign = sign := by omega
  rw [signedCoordinate_mode sign signed, shift, pure]

/-- The regular Euler identity gives the genuine signed derivative everywhere,
with signed-coordinate injectivity supplying the axis without division there. -/
theorem regularSecondPrimitive_derivative {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (forcing : ClosedJet dimension) (pure : angularClosedJet sign forcing = forcing) :
    signedLowering sign (regularSecondPrimitive sign forcing) = forcing := by
  apply centerCoordinate_injective sign signed
  have mode := regularSecondPrimitive_mode sign signed forcing pure
  have euler := signedMode_euler sign signed 1 (regularSecondPrimitive sign forcing)
    (by simpa only [Nat.cast_one, one_add_one_eq_two] using mode)
  exact euler.trans (shiftedEuler_powerDilation 1 (coordinateMultiplyJet (sign : ℝ) forcing))

theorem regularSecondPrimitive_pinned {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (forcing : ClosedJet dimension) (pure : angularClosedJet sign forcing = forcing) :
    CenterPinned (regularSecondPrimitive sign forcing) := by
  apply pureMode_pinned (2 * sign) (by rcases signed with rfl | rfl <;> norm_num)
    (by rcases signed with rfl | rfl <;> norm_num) (by rcases signed with rfl | rfl <;> norm_num)
  exact regularSecondPrimitive_mode sign signed forcing pure

theorem regularSecondMode_unique {dimension : ℕ} (sign : ℤ) (signed : sign = 1 ∨ sign = -1)
    (first second : ClosedJet dimension)
    (firstPure : angularClosedJet (2 * sign) first = first) (secondPure : angularClosedJet (2 * sign) second = second)
    (sameDerivative : signedLowering sign first = signedLowering sign second) : first = second := by
  have firstEuler := signedMode_euler sign signed 1 first
    (by simpa only [Nat.cast_one, one_add_one_eq_two] using firstPure)
  have secondEuler := signedMode_euler sign signed 1 second
    (by simpa only [Nat.cast_one, one_add_one_eq_two] using secondPure)
  have equalEuler := firstEuler.symm.trans ((congrArg (coordinateMultiplyJet (sign : ℝ)) sameDerivative).trans secondEuler)
  exact (powerDilation_shiftedEuler 1 first).symm.trans
    ((congrArg (powerDilationJet 1) equalEuler).trans (powerDilation_shiftedEuler 1 second))

theorem exceptionalPsi_jet {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (sign : ℤ) (source : SmoothCapSource L sigma gamma ell) (cell : ℤ) :
    apSmoothJet admissible 1 cell (exceptionalPsi admissible sign source) =
      regularSecondPrimitive sign (valueMapJet (spinValue ((-sign : ℤ) : ℂ)) (apSmoothJet admissible 2 cell source.1)) := by
  have spin := apSmoothValueMap_jet admissible (spinValue ((-sign : ℤ) : ℂ)) source.1 cell
  have coordinate := (smoothSignedCoordinate_jet admissible sign (smoothSpin L sigma gamma ell (-sign) source.1) cell).trans
    (congrArg (coordinateMultiplyJet (sign : ℝ)) spin)
  exact (originalPowerSmooth_jet admissible 0
    (smoothSignedCoordinate admissible 1 sign (smoothSpin L sigma gamma ell (-sign) source.1)) cell).trans
      (congrArg (powerDilationJet 1) coordinate)

end Grad.ActualExceptionalInverse
