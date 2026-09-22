import AKDV1ActualProductRecoverySmallness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
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

/-- The same DJ7 construction, with its literal coefficient bound exposed.
This permits a compact-dependent quantitative radius to be fixed first. -/
def actualOriginalProductBelow : OriginalPhysicalProduct parameters positive reference inside center := by
  let coefficientBound := 1+‖center‖
  have nonnegative : 0 ≤ coefficientBound := by dsimp only [coefficientBound]; positivity
  let target := min threshold (min 1 (actualOriginalInverseRadius parameters coefficientBound positive nonnegative))
  have targetPositive : 0 < target := lt_min thresholdPositive
    (lt_min zero_lt_one (actualOriginalInverseRadius_positive parameters coefficientBound positive nonnegative))
  let result := actualNewton_product_neighborhood parameters reference inside center insideC zeroC target targetPositive
  exact {
    neighborhood := result.choose
    openDomain := result.choose_spec.1
    centerMember := result.choose_spec.2.1
    coefficientBound := coefficientBound
    nonnegative := nonnegative
    seedBound := result.choose_spec.2.2.1
    budget := fun finite member state low =>
      (result.choose_spec.2.2.2 finite member state low).trans_le (min_le_right _ _) }

theorem actualOriginalProductBelow_coefficient :
    (actualOriginalProductBelow parameters positive reference inside center insideC zeroC threshold thresholdPositive).coefficientBound =
      1+‖center‖ := rfl

/-- The additional low radius holds uniformly on the constructed product,
before the finite parameter, state, source and derivative order. -/
theorem actualOriginalProductBelow_budget :
    let product := actualOriginalProductBelow parameters positive reference inside center insideC zeroC threshold thresholdPositive
    ∀ finite (member : finite ∈ product.neighborhood.parameterDomain)
      (state : stateSmoothRange parameters reference inside),
      stateSize parameters reference inside 24 0 state ≤ 2*product.neighborhood.radius →
      physicalBudget parameters (actualFiniteCurrentField parameters reference inside finite.1
        (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state))
        (finite.1 0) finite.2 24 < threshold := by
  let coefficientBound := 1+‖center‖
  have nonnegative : 0 ≤ coefficientBound := by dsimp only [coefficientBound]; positivity
  let target := min threshold (min 1 (actualOriginalInverseRadius parameters coefficientBound positive nonnegative))
  have targetPositive : 0 < target := lt_min thresholdPositive
    (lt_min zero_lt_one (actualOriginalInverseRadius_positive parameters coefficientBound positive nonnegative))
  let result := actualNewton_product_neighborhood parameters reference inside center insideC zeroC target targetPositive
  dsimp only
  intro finite member state low
  exact (result.choose_spec.2.2.2 finite member state low).trans_le (min_le_left _ _)

end Grad.OriginalMainConsumer
