import ASX18ExceptionalBoundary

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualCenterVolterra
open Grad.NonlinearRange Grad.NonlinearRadial Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.RadialLedger
variable {L sigma gamma ell : ℝ}

/-- A shorthand for literal angular projection equality of every original AP jet. -/
def HasSmoothMode (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (mode : ℤ) (field : APSmooth L sigma gamma ell dimension) : Prop :=
  ∀ cell, angularClosedJet mode (apSmoothJet admissible dimension cell field) = apSmoothJet admissible dimension cell field

theorem smoothMode_smul (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (mode : ℤ) (scalar : ℂ) (field : APSmooth L sigma gamma ell dimension) (pure : HasSmoothMode admissible mode field) :
    HasSmoothMode admissible mode (scalar • field) := by
  intro cell
  have law := (apSmoothJet admissible dimension cell).map_smul scalar field
  rw [law, angularClosedJet_smul, pure cell]

theorem smoothMode_add (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (mode : ℤ) (first second : APSmooth L sigma gamma ell dimension)
    (firstPure : HasSmoothMode admissible mode first) (secondPure : HasSmoothMode admissible mode second) :
    HasSmoothMode admissible mode (first + second) := by
  intro cell
  have law := (apSmoothJet admissible dimension cell).map_add first second
  exact (congrArg (angularClosedJet mode) law).trans
    ((angularClosedJet_add mode _ _).trans
      ((congrArg₂ (fun first second : ClosedJet dimension => first + second) (firstPure cell) (secondPure cell)).trans law.symm))

theorem smoothMode_sub (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (mode : ℤ) (first second : APSmooth L sigma gamma ell dimension)
    (firstPure : HasSmoothMode admissible mode first) (secondPure : HasSmoothMode admissible mode second) :
    HasSmoothMode admissible mode (first - second) := by
  intro cell
  have law := (apSmoothJet admissible dimension cell).map_sub first second
  have projected := (angularClosedJetLinear dimension mode).map_sub
    (apSmoothJet admissible dimension cell first) (apSmoothJet admissible dimension cell second)
  exact (congrArg (angularClosedJet mode) law).trans
    (projected.trans ((congrArg₂ (fun first second : ClosedJet dimension => first - second)
      (firstPure cell) (secondPure cell)).trans law.symm))

theorem smoothMode_axial (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (mode : ℤ) (field : APSmooth L sigma gamma ell dimension) (pure : HasSmoothMode admissible mode field) :
    HasSmoothMode admissible mode (apSmoothAxial L sigma gamma ell dimension field) := by
  intro cell
  rw [apSmoothAxial_jet, angularClosedJet_smul, pure cell]

theorem smoothMode_rotation (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (mode : ℤ) (field : APSmooth L sigma gamma ell dimension) (pure : HasSmoothMode admissible mode field) :
    apSmoothRotation admissible dimension field = (Complex.I * (mode : ℂ)) • field := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (apSmoothRotation_jet admissible field cell).trans
    ((pureMode_rotation mode _ (pure cell)).trans ((apSmoothJet admissible dimension cell).map_smul _ field).symm)

theorem smoothMode_meanZero (admissible : Admissible L sigma gamma ell) (mode : ℤ) (nonzero : mode ≠ 0)
    (field : APSmooth L sigma gamma ell 1) (pure : HasSmoothMode admissible mode field) :
    APSmoothMeanZero admissible field :=
  fun cell => pureMode_mean_zero mode nonzero _ (pure cell)

theorem smoothPinned_iff (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (field : APSmooth L sigma gamma ell dimension) :
    APSmoothAxisFirstJetZero admissible field ↔ ∀ cell, CenterPinned (apSmoothJet admissible dimension cell field) := by
  constructor
  · intro flat cell
    simpa only [CenterPinned, ClosedFirstJetZero, originalPartial_eq] using
      (apSmoothAxisFirstJetZero_closed admissible field flat cell)
  · intro flat
    apply apSmoothAxisFirstJetZero_of_closed admissible
    intro cell
    simpa only [CenterPinned, ClosedFirstJetZero, originalPartial_eq] using flat cell

theorem smoothMode_pinned (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (mode : ℤ) (nonzero : mode ≠ 0) (notPositive : mode ≠ 1) (notNegative : mode ≠ -1)
    (field : APSmooth L sigma gamma ell dimension) (pure : HasSmoothMode admissible mode field) :
    APSmoothAxisFirstJetZero admissible field :=
  (smoothPinned_iff admissible field).mpr (fun cell => pureMode_pinned mode nonzero notPositive notNegative _ (pure cell))

theorem smoothMode_power (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (mode : ℤ) (power : ℕ) (field : APSmooth L sigma gamma ell dimension) (pure : HasSmoothMode admissible mode field) :
    HasSmoothMode admissible mode (originalPowerSmooth admissible power field) := by
  intro cell
  rw [originalPowerSmooth_jet]
  exact powerDilation_mode (power + 1) mode _ (pure cell)

theorem smoothMode_signedCoordinate (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (mode : ℤ)
    (field : APSmooth L sigma gamma ell dimension) (pure : HasSmoothMode admissible mode field) :
    HasSmoothMode admissible (mode + sign) (smoothSignedCoordinate admissible dimension sign field) := by
  intro cell
  rw [smoothSignedCoordinate_jet, signedCoordinate_mode sign signed, add_sub_cancel_right, pure cell]

theorem smoothMode_pinnedPrimitive (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : APSmooth L sigma gamma ell dimension)
    (pure : HasSmoothMode admissible (2 * sign) field) :
    HasSmoothMode admissible sign (smoothPinnedPrimitive admissible dimension sign field) := by
  intro cell
  rw [smoothPinnedPrimitive_jet]
  exact pinnedSpinPrimitive_mode sign signed _ (pure cell)

theorem smoothPinnedPrimitive_equation (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (field : APSmooth L sigma gamma ell dimension)
    (pure : HasSmoothMode admissible (2 * sign) field) :
    smoothSignedDerivative admissible dimension (-sign) (smoothPinnedPrimitive admissible dimension sign field) = field := by
  apply apSmoothJet_ext admissible
  intro cell
  exact (smoothSignedDerivative_jet admissible (-sign) (smoothPinnedPrimitive admissible dimension sign field) cell).trans
    ((congrArg (signedLowering (-sign)) (smoothPinnedPrimitive_jet admissible sign field cell)).trans
      (pinnedSpinPrimitive_derivative sign signed _ (pure cell)))

theorem smoothPinnedPrimitive_pinned (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (sign : ℤ) (field : APSmooth L sigma gamma ell dimension) :
    APSmoothAxisFirstJetZero admissible (smoothPinnedPrimitive admissible dimension sign field) := by
  apply (smoothPinned_iff admissible _).mpr
  intro cell
  rw [smoothPinnedPrimitive_jet]
  exact pinnedSpinPrimitive_pinned sign _

end Grad.ActualExceptionalInverse
