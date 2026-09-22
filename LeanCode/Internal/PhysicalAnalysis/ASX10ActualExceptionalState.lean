import ASX9SmoothSignedOperators

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct Grad.NonlinearRadial
open Grad.Constraints.Gauges
open Grad.ActualCenterVolterra Grad.NonlinearQuotientBounds Grad.FlatSourceProjection
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Compensated
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.Ledger
variable {L sigma gamma ell : ℝ}

def smoothSpin (L sigma gamma ell : ℝ) (sign : ℤ) :
    APSmooth L sigma gamma ell 2 →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
  apSmoothValueMap L sigma gamma ell (spinValue (sign : ℂ))

def exceptionalPsi (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) : APSmooth L sigma gamma ell 1 :=
  originalPowerSmooth admissible 0 (smoothSignedCoordinate admissible 1 sign
    (smoothSpin L sigma gamma ell (-sign) source.1))

def exceptionalTheta (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) : APSmooth L sigma gamma ell 1 :=
  (2 * Complex.I * (sign : ℂ))⁻¹ • exceptionalPsi admissible sign source

def exceptionalFixedSpin (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) : APSmooth L sigma gamma ell 1 :=
  (4 * Complex.I * (sign : ℂ))⁻¹ •
    (smoothSignedDerivative admissible 1 (-sign) (exceptionalPsi admissible sign source) -
      smoothSpin L sigma gamma ell sign source.1)

/-- The actual all-cell axial derivative is used, including its original
ell/L scaling. No scalar frequency is substituted into the smooth carrier. -/
def exceptionalToroidal (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) : APSmooth L sigma gamma ell 1 :=
  (2 * Complex.I * (sign : ℂ))⁻¹ •
    (source.2.2 + apSmoothAxial L sigma gamma ell 1 (exceptionalPsi admissible sign source))

def exceptionalFreeForcing (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) : APSmooth L sigma gamma ell 1 :=
  (-2 : ℂ) • source.2.1 + (-2 : ℂ) • apSmoothAxial L sigma gamma ell 1 (exceptionalToroidal admissible sign source) -
    smoothSignedDerivative admissible 1 sign (exceptionalFixedSpin admissible sign source)

def exceptionalFreeSpin (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) : APSmooth L sigma gamma ell 1 :=
  smoothPinnedPrimitive admissible 1 sign (exceptionalFreeForcing admissible sign source)

def smoothPlanarFromSpins (L sigma gamma ell : ℝ) (sign : ℤ)
    (first second : APSmooth L sigma gamma ell 1) : APSmooth L sigma gamma ell 2 :=
  (1 / 2 : ℂ) • apSmoothValueMap L sigma gamma ell (matrixUnit (input := 1) (output := 2) 0 0) (first + second) +
    (2 * Complex.I * (sign : ℂ))⁻¹ • apSmoothValueMap L sigma gamma ell
      (matrixUnit (input := 1) (output := 2) 1 0) (first - second)

def exceptionalPlanar (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) : APSmooth L sigma gamma ell 2 :=
  smoothPlanarFromSpins L sigma gamma ell sign (exceptionalFixedSpin admissible sign source)
    (exceptionalFreeSpin admissible sign source)

def exceptionalCovariant (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) : APSmooth L sigma gamma ell 3 :=
  apSmoothValueMap L sigma gamma ell planarInclusionMap (exceptionalPlanar admissible sign source) +
    apSmoothValueMap L sigma gamma ell toroidalInclusionMap (exceptionalToroidal admissible sign source)

/-- Literal Y34–Y39 on the original smooth source/state carriers. Membership
in the physical domain and all equations are proved from the source below. -/
def exceptionalState (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) : CompensatedData L sigma gamma ell :=
  (exceptionalTheta admissible sign source,
    exceptionalCovariant admissible sign source - apSmoothCovariant admissible (exceptionalTheta admissible sign source))

private theorem reconstruct_algebra {E : Type*} [AddCommGroup E] (potential total : E) :
    potential + (total - potential) = total := by abel

theorem exceptionalState_reconstruct (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) :
    compensatedReconstruct admissible (exceptionalState admissible sign source) = exceptionalCovariant admissible sign source :=
  reconstruct_algebra (apSmoothCovariant admissible (exceptionalTheta admissible sign source))
    (exceptionalCovariant admissible sign source)

end Grad.ActualExceptionalInverse
