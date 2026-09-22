import ASX19OriginalSmoothModes
import ANP4RawVectorAndSource

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.ActualCenterVolterra
open Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.RawCircularSectors Grad.FlatSourceProjection
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.RadialLedger
variable {L sigma gamma ell : ℝ}

theorem smoothMode_signedDerivative (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (sign : ℤ) (signed : sign = 1 ∨ sign = -1) (mode : ℤ)
    (field : APSmooth L sigma gamma ell dimension) (pure : HasSmoothMode admissible mode field) :
    HasSmoothMode admissible (mode - sign) (smoothSignedDerivative admissible dimension sign field) := by
  intro cell
  rw [smoothSignedDerivative_jet]
  exact centerDifferential_pure sign signed mode _ (pure cell)

theorem rawSource_smoothSpin (admissible : Admissible L sigma gamma ell) (mode sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible mode source) :
    HasSmoothMode admissible (mode + sign) (smoothSpin L sigma gamma ell sign source.1) := by
  intro cell
  rw [smoothSpin_jet]
  exact rawSourceSector_spin admissible mode sign signed source raw cell

theorem exceptionalPsi_mode (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    HasSmoothMode admissible (2 * sign) (exceptionalPsi admissible sign source) := by
  have spin : HasSmoothMode admissible sign (smoothSpin L sigma gamma ell (-sign) source.1) := by
    simpa only [show 2 * sign + -sign = sign by omega] using
      rawSource_smoothSpin admissible (2 * sign) (-sign) (by omega) source raw
  have result := smoothMode_power admissible (sign + sign) 0 _
    (smoothMode_signedCoordinate admissible sign signed sign _ spin)
  simpa only [exceptionalPsi, show sign + sign = 2 * sign by omega] using result

theorem exceptionalTheta_mode (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    HasSmoothMode admissible (2 * sign) (exceptionalTheta admissible sign source) :=
  smoothMode_smul admissible (2 * sign) _ _ (exceptionalPsi_mode admissible sign signed source raw)

theorem exceptionalFixedSpin_mode (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    HasSmoothMode admissible (3 * sign) (exceptionalFixedSpin admissible sign source) := by
  have derivative : HasSmoothMode admissible (3 * sign)
      (smoothSignedDerivative admissible 1 (-sign) (exceptionalPsi admissible sign source)) := by
    simpa only [show 2 * sign - -sign = 3 * sign by omega] using
      smoothMode_signedDerivative admissible (-sign) (by omega) (2 * sign) _
        (exceptionalPsi_mode admissible sign signed source raw)
  have spin : HasSmoothMode admissible (3 * sign) (smoothSpin L sigma gamma ell sign source.1) := by
    simpa only [show 2 * sign + sign = 3 * sign by omega] using
      rawSource_smoothSpin admissible (2 * sign) sign signed source raw
  exact smoothMode_smul admissible (3 * sign) _ _ (smoothMode_sub admissible (3 * sign) _ _ derivative spin)

theorem exceptionalToroidal_mode (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    HasSmoothMode admissible (2 * sign) (exceptionalToroidal admissible sign source) :=
  smoothMode_smul admissible (2 * sign) _ _ (smoothMode_add admissible (2 * sign) _ _ raw.2.2
    (smoothMode_axial admissible (2 * sign) _ (exceptionalPsi_mode admissible sign signed source raw)))

/-- The forcing compatibility of the pinned first-order equation follows from the actual raw source,
including its axis behavior; it is not supplied as an independent assumption. -/
theorem exceptionalFreeForcing_mode (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    HasSmoothMode admissible (2 * sign) (exceptionalFreeForcing admissible sign source) := by
  have derivative : HasSmoothMode admissible (2 * sign)
      (smoothSignedDerivative admissible 1 sign (exceptionalFixedSpin admissible sign source)) := by
    simpa only [show 3 * sign - sign = 2 * sign by omega] using
      smoothMode_signedDerivative admissible sign signed (3 * sign) _
        (exceptionalFixedSpin_mode admissible sign signed source raw)
  exact smoothMode_sub admissible (2 * sign) _ _
    (smoothMode_add admissible (2 * sign) _ _ (smoothMode_smul admissible (2 * sign) (-2) _ raw.2.1)
      (smoothMode_smul admissible (2 * sign) (-2) _
        (smoothMode_axial admissible (2 * sign) _ (exceptionalToroidal_mode admissible sign signed source raw)))) derivative

theorem exceptionalFreeSpin_mode (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    HasSmoothMode admissible sign (exceptionalFreeSpin admissible sign source) :=
  smoothMode_pinnedPrimitive admissible sign signed _ (exceptionalFreeForcing_mode admissible sign signed source raw)

theorem exceptionalFreeSpin_equation (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    smoothSignedDerivative admissible 1 (-sign) (exceptionalFreeSpin admissible sign source) =
      exceptionalFreeForcing admissible sign source :=
  smoothPinnedPrimitive_equation admissible sign signed _ (exceptionalFreeForcing_mode admissible sign signed source raw)

theorem exceptionalPsi_equation (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (raw : IsRawSourceSector admissible (2 * sign) source) :
    smoothSignedDerivative admissible 1 sign (exceptionalPsi admissible sign source) =
      smoothSpin L sigma gamma ell (-sign) source.1 := by
  apply apSmoothJet_ext admissible
  intro cell
  have pure : angularClosedJet sign (valueMapJet (spinValue ((-sign : ℤ) : ℂ)) (apSmoothJet admissible 2 cell source.1)) =
      valueMapJet (spinValue ((-sign : ℤ) : ℂ)) (apSmoothJet admissible 2 cell source.1) := by
    simpa only [show 2 * sign + -sign = sign by omega] using
      rawSourceSector_spin admissible (2 * sign) (-sign) (by omega) source raw cell
  exact (smoothSignedDerivative_jet admissible sign (exceptionalPsi admissible sign source) cell).trans
    ((congrArg (signedLowering sign) (exceptionalPsi_jet admissible sign source cell)).trans
      ((regularSecondPrimitive_derivative sign signed _ pure).trans (smoothSpin_jet admissible (-sign) source.1 cell).symm))

end Grad.ActualExceptionalInverse
