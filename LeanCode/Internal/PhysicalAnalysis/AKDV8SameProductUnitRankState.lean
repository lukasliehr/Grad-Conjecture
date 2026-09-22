import AKDV7FixedCoefficientProduct
import AKDS31OriginalUnitRankState

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set

namespace Grad.OriginalMainConsumer
open Grad.CartesianState Grad.Constraints Grad.Q24Realization Grad.RealFixedRanges
open Grad.PhysicalCoordinates Grad.FinitePhysicalJetLift Grad.OriginalCoreRealization
open Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalInverseNeighborhood
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit

variable (parameters : PhaseParameters) (positive : 0 < parameters.length)
  (reference : Seed.Parameters) (inside : reference ∈ Seed.parameterDomain)
  (center : Seed.Parameters) (insideC : center ∈ Seed.parameterDomain) (zeroC : center 0=0)
  (threshold : ℝ) (thresholdPositive : 0 < threshold)
  (thresholdSmall : threshold ≤ originalUnitRankRadius parameters parameters.length (1+‖center‖))

local notation "fixedProduct" => actualOriginalProductBelow parameters positive reference inside center insideC zeroC threshold thresholdPositive

/-- Every state on the one fixed product gives the faithful physical-length
unit-disk ledger state. The original field and all finite parameters are retained. -/
def actualProduct_unitRankState (higher : ℕ) (higherLarge : 24 ≤ higher)
    (finite : OriginalFiniteParameter) (member : finite ∈ (fixedProduct).neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside higher 0 state ≤ 2*(fixedProduct).neighborhood.radius) :
    OriginalUnitRankState parameters parameters.length (1+‖center‖) := by
  let product := fixedProduct
  let field := actualFiniteCurrentField parameters reference inside finite.1
    (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)
  have low24 := product.neighborhood.raiseBase_low higher higherLarge state low
  have below := actualOriginalProductBelow_budget parameters positive reference inside center insideC zeroC
    threshold thresholdPositive finite member state low24
  have bounded := (actualProduct_recovery_smallness product higher higherLarge finite member state low).2.1
  have coefficient := actualOriginalProductBelow_coefficient parameters positive reference inside center insideC zeroC threshold thresholdPositive
  refine ⟨(finite.1 0,finite.1 1,finite.1 2,finite.1 3,finite.2,field), ?_, ?_, ?_, ?_, ?_⟩
  · exact (product.seedBound finite member 1).trans_eq coefficient
  · exact (product.seedBound finite member 2).trans_eq coefficient
  · exact (product.seedBound finite member 3).trans_eq coefficient
  · exact (physicalBudget_monotone parameters field (finite.1 0) finite.2 (by norm_num : 12 ≤ 20)).trans bounded
  · exact (physicalBudget_monotone parameters field (finite.1 0) finite.2 (by norm_num : 6 ≤ 24)).trans
      (below.le.trans thresholdSmall)

end Grad.OriginalMainConsumer
