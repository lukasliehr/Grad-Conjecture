import ASX25ExceptionalKernel

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.ActualExceptionalInverse
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.RawCircularSectors
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.RadialLedger
variable {L sigma gamma ell : ℝ}

/-- The literal exceptional formula is complex linear on the unchanged original smooth source carrier. -/
def exceptionalInverseLinear (admissible : Admissible L sigma gamma ell) (sign : ℤ) :
    SmoothCapSource L sigma gamma ell →ₗ[ℂ] CompensatedData L sigma gamma ell :=
  let force : SmoothCapSource L sigma gamma ell →ₗ[ℂ] APSmooth L sigma gamma ell 2 := LinearMap.fst ℂ _ _
  let determinant : SmoothCapSource L sigma gamma ell →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
    (LinearMap.fst ℂ _ _).comp (LinearMap.snd ℂ _ _)
  let third : SmoothCapSource L sigma gamma ell →ₗ[ℂ] APSmooth L sigma gamma ell 1 :=
    (LinearMap.snd ℂ _ _).comp (LinearMap.snd ℂ _ _)
  let psi := (originalPowerSmoothLinear admissible 1 0).comp
    ((smoothSignedCoordinate admissible 1 sign).comp ((smoothSpin L sigma gamma ell (-sign)).comp force))
  let theta := (2 * Complex.I * (sign : ℂ))⁻¹ • psi
  let fixed := (4 * Complex.I * (sign : ℂ))⁻¹ •
    ((smoothSignedDerivative admissible 1 (-sign)).comp psi - (smoothSpin L sigma gamma ell sign).comp force)
  let toroidal := (2 * Complex.I * (sign : ℂ))⁻¹ • (third + (apSmoothAxial L sigma gamma ell 1).comp psi)
  let forcing := (-2 : ℂ) • determinant + (-2 : ℂ) • (apSmoothAxial L sigma gamma ell 1).comp toroidal -
    (smoothSignedDerivative admissible 1 sign).comp fixed
  let free := (smoothPinnedPrimitive admissible 1 sign).comp forcing
  let planar := (1 / 2 : ℂ) • (apSmoothValueMap L sigma gamma ell (matrixUnit (input := 1) (output := 2) 0 0)).comp (fixed + free) +
    (2 * Complex.I * (sign : ℂ))⁻¹ • (apSmoothValueMap L sigma gamma ell (matrixUnit (input := 1) (output := 2) 1 0)).comp (fixed - free)
  let total := (apSmoothValueMap L sigma gamma ell planarInclusionMap).comp planar +
    (apSmoothValueMap L sigma gamma ell toroidalInclusionMap).comp toroidal
  theta.prod (total - (apSmoothCovariant admissible).comp theta)

theorem exceptionalInverseLinear_apply (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (source : SmoothCapSource L sigma gamma ell) :
    exceptionalInverseLinear admissible sign source = exceptionalState admissible sign source := rfl

/-- AN9/AN31: both actual raw exceptional signs, on the original smooth source and domain,
with every original circular row, all high boundary traces and genuine pinned uniqueness.
No native derivative-gain estimate is asserted by this qualitative construction. -/
theorem actualExceptional_consumer (admissible : Admissible L sigma gamma ell) (sign : ℤ)
    (signed : sign = 1 ∨ sign = -1) (source : SmoothCapSource L sigma gamma ell)
    (compatible : source ∈ smoothCapSourceCore admissible) (raw : IsRawSourceSector admissible (2 * sign) source) :
    exceptionalInverseLinear admissible sign source ∈ circularCompensatedCore admissible ∧
    IsRawStateSector admissible (2 * sign) (exceptionalInverseLinear admissible sign source) ∧
    circularRows admissible (exceptionalInverseLinear admissible sign source) = source ∧
    (∀ grade : ℕ, 1 ≤ grade → circularCoreTrace admissible grade (exceptionalInverseLinear admissible sign source) = 0) ∧
    (∀ state : CompensatedData L sigma gamma ell, state ∈ circularCompensatedCore admissible →
      IsRawStateSector admissible (2 * sign) state → circularRows admissible state = source →
      state = exceptionalInverseLinear admissible sign source) := by
  change exceptionalState admissible sign source ∈ circularCompensatedCore admissible ∧
    IsRawStateSector admissible (2 * sign) (exceptionalState admissible sign source) ∧
    circularRows admissible (exceptionalState admissible sign source) = source ∧
    (∀ grade : ℕ, 1 ≤ grade → circularCoreTrace admissible grade (exceptionalState admissible sign source) = 0) ∧
    (∀ state : CompensatedData L sigma gamma ell, state ∈ circularCompensatedCore admissible →
      IsRawStateSector admissible (2 * sign) state → circularRows admissible state = source →
      state = exceptionalState admissible sign source)
  have domain := exceptionalState_circularCore admissible sign signed source raw
  have sector := exceptionalState_sector admissible sign signed source raw
  have rows := exceptionalState_rows admissible sign signed source compatible raw
  refine ⟨domain, sector, rows, exceptionalState_highBoundary admissible sign signed source raw, ?_⟩
  intro state stateDomain stateRaw stateRows
  exact exceptionalState_sameRows_unique admissible sign signed state (exceptionalState admissible sign source)
    stateDomain domain stateRaw sector (stateRows.trans rows.symm)

end Grad.ActualExceptionalInverse
