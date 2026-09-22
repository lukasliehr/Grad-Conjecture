import AKDV9ActualProductPrincipalAbsorption
import AKDV10CanonicalCompactCellPacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
open Set
open scoped ContDiff

namespace Grad.OriginalMainConsumer
open Grad.CartesianState Grad.Constraints Grad.Q24Realization Grad.RealFixedRanges
open Grad.PhysicalCoordinates Grad.FinitePhysicalJetLift Grad.OriginalCoreRealization
open Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalInverseNeighborhood
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit
open Grad.OriginalCartesianTameEstimate
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianStartup Grad.SourceCollarCoefficients

variable (parameters : PhaseParameters) (positive : 0 < parameters.length)
  (reference : Seed.Parameters) (inside : reference ∈ Seed.parameterDomain)
  (center : Seed.Parameters) (insideC : center ∈ Seed.parameterDomain) (zeroC : center 0=0)
  (outer : Spatial → ℝ) (smooth : ContDiff ℝ ∞ outer) (compact : HasCompactSupport outer)

local notation "principalProduct" => actualPrincipalProduct parameters positive reference inside center insideC zeroC outer smooth compact

/-- The faithful unit ledger has literally the original product budget. -/
theorem actualPrincipalUnitState_budget (higher : ℕ) (higherLarge : 24 ≤ higher)
    (finite : OriginalFiniteParameter) (member : finite ∈ (principalProduct).neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside higher 0 state ≤ 2*(principalProduct).neighborhood.radius)
    (grade : ℕ) :
    let unit := actualPrincipalUnitState parameters positive reference inside center insideC zeroC outer smooth compact
      higher higherLarge finite member state low
    physicalBudget parameters unit.field unit.rho unit.epsilon grade =
      physicalBudget parameters
        (actualFiniteCurrentField parameters reference inside finite.1
          ((principalProduct).neighborhood.patchInside ((principalProduct).neighborhood.seedInside finite member)) (finite.2,state))
        (finite.1 0) finite.2 grade := rfl

/-- The literal remaining current identity for the SAME compact and
covariant cores, on the actual physical-length product. -/
def ActualPrincipalCompactCurrent
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length))
    (higher : ℕ) (higherLarge : 24 ≤ higher) : Prop :=
  ∀ finite (member : finite ∈ (principalProduct).neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside higher 0 state ≤ 2*(principalProduct).neighborhood.radius)
    (source : OriginalFlatSource parameters parameters.length),
    let unit := actualPrincipalUnitState parameters positive reference inside center insideC zeroC outer smooth compact
      higher higherLarge finite member state low
    originalSourceFieldLinear parameters
      (canonicalProductRecovery principalProduct widthHalf widthLength higher higherLarge finite member state low source).covariant =
    originalCurrentKernel (unitDiskAdmissible parameters) unit.data.gaugeDeviation
      (unit.coherent (by positivity)).2.2.2.1 (unit.inverseCoherent (by positivity))
      (originalSourceFieldLinear parameters
        (canonicalProductCompactCore principalProduct widthHalf widthLength higher higherLarge finite member state low source))

end Grad.OriginalMainConsumer
