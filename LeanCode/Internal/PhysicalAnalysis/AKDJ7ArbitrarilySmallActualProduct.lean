import AKDJ6ActualGoodSeedNeighborhood
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3500
open Set
namespace Grad.OriginalInverseNeighborhood
open Grad.CartesianState Grad.Constraints Grad.Q24Realization Grad.RealFixedRanges
open Grad.FinitePhysicalJetLift Grad.OriginalCoreRealization Grad.GaugeCoefficients.Physical.Allocation
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit

/-- The actual product can simultaneously meet any further fixed positive
physical threshold. This permits the quantitative principal absorption
radius to be selected once before all states and derivative orders. -/
theorem exists_actualPhysicalProduct_below (parameters : PhaseParameters) (positive : 0 < parameters.length)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (center : Seed.Parameters) (insideC : center ∈ Seed.parameterDomain) (zeroC : center 0=0)
    (threshold : ℝ) (thresholdPositive : 0 < threshold) :
    ∃ product : OriginalPhysicalProduct parameters positive reference insideR center,
      ∀ finite (member : finite ∈ product.neighborhood.parameterDomain)
        (state : stateSmoothRange parameters reference insideR),
        stateSize parameters reference insideR 24 0 state ≤ 2*product.neighborhood.radius →
        physicalBudget parameters
          (actualFiniteCurrentField parameters reference insideR finite.1
            (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state))
          (finite.1 0) finite.2 24 < threshold := by
  let coefficientBound := 1+‖center‖
  have nonnegative : 0 ≤ coefficientBound := by dsimp only [coefficientBound]; positivity
  let target := min threshold (min 1 (actualOriginalInverseRadius parameters coefficientBound positive nonnegative))
  have targetPositive : 0 < target := lt_min thresholdPositive
    (lt_min zero_lt_one (actualOriginalInverseRadius_positive parameters coefficientBound positive nonnegative))
  let result := actualNewton_product_neighborhood parameters reference insideR center insideC zeroC target targetPositive
  let product : OriginalPhysicalProduct parameters positive reference insideR center := {
    neighborhood := result.choose
    openDomain := result.choose_spec.1
    centerMember := result.choose_spec.2.1
    coefficientBound := coefficientBound
    nonnegative := nonnegative
    seedBound := result.choose_spec.2.2.1
    budget := fun finite member state small => (result.choose_spec.2.2.2 finite member state small).trans_le (min_le_right _ _) }
  exact ⟨product,fun finite member state small => (result.choose_spec.2.2.2 finite member state small).trans_le (min_le_left _ _)⟩

end Grad.OriginalInverseNeighborhood
