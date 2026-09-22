import AKDS23ActualJetFullRecovery
import AKDS25ActualFlatReferenceOneHigh

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set

namespace Grad.OriginalMainConsumer
open Grad.CartesianStartup
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.Q24Realization
open Grad.PhysicalCoordinates Grad.OriginalCoreRealization Grad.FinitePhysicalJetLift
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit
open Grad.OriginalInverseNeighborhood Grad.GaugeCoefficients.Physical.Allocation

/-- Every low-threshold premise of the actual DS23 recovery follows from
this SAME already constructed original product, before the source is chosen. -/
theorem actualProduct_recovery_smallness
    {parameters : PhaseParameters} {positive : 0 < parameters.length}
    {reference : Seed.Parameters} {inside : reference ∈ Seed.parameterDomain} {center : Seed.Parameters}
    (product : OriginalPhysicalProduct parameters positive reference inside center)
    (higher : ℕ) (higherLarge : 24 ≤ higher)
    (finite : OriginalFiniteParameter) (member : finite ∈ product.neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside higher 0 state ≤ 2*product.neighborhood.radius) :
    let field := actualFiniteCurrentField parameters reference inside finite.1
      (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)
    physicalBudget parameters field (finite.1 0) finite.2 8 ≤
        actualJetExhaustionRadius parameters parameters.length product.coefficientBound ∧
      physicalBudget parameters field (finite.1 0) finite.2 20 ≤ 1 ∧
      physicalBudget parameters field (finite.1 0) finite.2 10 <
        actualNativeAllOrderRadius parameters parameters.length product.coefficientBound positive product.nonnegative := by
  have stateSmall := product.neighborhood.raiseBase_low higher higherLarge state low
  have budget := product.budget finite member state stateSmall
  have radius := actualOriginalInverseRadius_bounds parameters product.coefficientBound positive product.nonnegative
  refine ⟨?_, ?_, ?_⟩
  · exact (physicalBudget_monotone parameters _ _ _ (by norm_num : 8 ≤ 24)).trans
      (budget.le.trans ((min_le_right _ _).trans radius.2.1))
  · exact (physicalBudget_monotone parameters _ _ _ (by norm_num : 20 ≤ 24)).trans
      (budget.le.trans (min_le_left _ _))
  · exact (physicalBudget_monotone parameters _ _ _ (by norm_num : 10 ≤ 24)).trans_lt
      (budget.trans_le ((min_le_right _ _).trans radius.2.2))

end Grad.OriginalMainConsumer
