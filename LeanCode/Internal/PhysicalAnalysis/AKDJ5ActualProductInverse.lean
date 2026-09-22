import AKDJ4ActualNewtonProductNeighborhood
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
open Set
namespace Grad.OriginalInverseNeighborhood
open Grad.CartesianState Grad.Constraints Grad.Q24Realization Grad.PhysicalCoordinates
open Grad.NonlinearQuotientBounds Grad.RealFixedRanges Grad.FinitePhysicalJetLift
open Grad.GaugeCoefficients.Physical.Allocation Grad.OriginalCoreRealization
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit

/-- The actual parameter/state product supporting the original inverse.
Its physical B24 bound is proved from finite-grade continuity. -/
structure OriginalPhysicalProduct (parameters : PhaseParameters) (positive : 0 < parameters.length)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain) (center : Seed.Parameters) where
  neighborhood : OriginalNewtonNeighborhood parameters reference insideR 24
  openDomain : IsOpen neighborhood.parameterDomain
  centerMember : (center,0) ∈ neighborhood.parameterDomain
  coefficientBound : ℝ
  nonnegative : 0 ≤ coefficientBound
  seedBound : ∀ finite ∈ neighborhood.parameterDomain, ∀ coordinate : Fin 4,
    |finite.1 coordinate| ≤ coefficientBound
  budget : ∀ finite (member : finite ∈ neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference insideR),
    stateSize parameters reference insideR 24 0 state ≤ 2*neighborhood.radius →
    physicalBudget parameters
      (actualFiniteCurrentField parameters reference insideR finite.1
        (neighborhood.patchInside (neighborhood.seedInside finite member)) (finite.2,state))
      (finite.1 0) finite.2 24 < min 1 (actualOriginalInverseRadius parameters coefficientBound positive nonnegative)

/-- Constructed from the zero-eccentricity original seed; no analytic
neighborhood or small-chart bound is an assumption. -/
def actualOriginalPhysicalProduct (parameters : PhaseParameters) (positive : 0 < parameters.length)
    (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
    (center : Seed.Parameters) (insideC : center ∈ Seed.parameterDomain) (zeroC : center 0=0) :
    OriginalPhysicalProduct parameters positive reference insideR center := by
  let coefficientBound := 1+‖center‖
  have nonnegative : 0 ≤ coefficientBound := by dsimp only [coefficientBound]; positivity
  let target := min 1 (actualOriginalInverseRadius parameters coefficientBound positive nonnegative)
  have targetPositive : 0 < target := lt_min zero_lt_one
    (actualOriginalInverseRadius_positive parameters coefficientBound positive nonnegative)
  let result := actualNewton_product_neighborhood parameters reference insideR center insideC zeroC target targetPositive
  exact {
    neighborhood := result.choose
    openDomain := result.choose_spec.1
    centerMember := result.choose_spec.2.1
    coefficientBound := coefficientBound
    nonnegative := nonnegative
    seedBound := result.choose_spec.2.2.1
    budget := result.choose_spec.2.2.2 }

namespace OriginalPhysicalProduct
variable {parameters : PhaseParameters} {positive : 0 < parameters.length}
    {reference : Seed.Parameters} {insideR : reference ∈ Seed.parameterDomain} {center : Seed.Parameters}
    (product : OriginalPhysicalProduct parameters positive reference insideR center)
    (widthHalf : parameters.gamma ≤ 1/2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length))

include widthHalf widthLength

/-- All states in the one actual low product have a bijective literal
original derivative, with the same source/state spaces. -/
theorem bijective (finite : OriginalFiniteParameter) (member : finite ∈ product.neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference insideR)
    (small : stateSize parameters reference insideR 24 0 state ≤ 2*product.neighborhood.radius) :
    Function.Bijective (literalPhysicalSmoothForward parameters parameters.length reference insideR finite.1
      (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)
      (product.neighborhood.axis state small)) := by
  have budget := product.budget finite member state small
  have low : physicalBudget parameters
      (actualFiniteCurrentField parameters reference insideR finite.1
        (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state))
      (finite.1 0) finite.2 10 < actualOriginalInverseRadius parameters product.coefficientBound positive product.nonnegative :=
    (physicalBudget_monotone parameters _ _ _ (by norm_num : 10 ≤ 24)).trans_lt (budget.trans_le (min_le_right _ _))
  exact actualOriginalForward_bijective_onBall parameters product.coefficientBound positive widthHalf widthLength
    reference insideR finite.1 (product.neighborhood.patchInside (product.neighborhood.seedInside finite member))
    (finite.2,state) (product.neighborhood.axis state small) product.nonnegative
    (product.seedBound finite member 1) (product.seedBound finite member 2) (product.seedBound finite member 3) low

/-- The actual original inverse on the fixed product, extended by zero
elsewhere only to give the total map requested by the Newton interface. -/
def inverseMap (finite : OriginalFiniteParameter) (state : stateSmoothRange parameters reference insideR) :
    sourceSmoothRange parameters →ₗ[ℝ] stateSmoothRange parameters reference insideR := by
  classical
  exact if valid : finite ∈ product.neighborhood.parameterDomain ∧
      stateSize parameters reference insideR 24 0 state ≤ 2*product.neighborhood.radius then
    (LinearEquiv.ofBijective
      (literalPhysicalSmoothForward parameters parameters.length reference insideR finite.1
        (product.neighborhood.patchInside (product.neighborhood.seedInside finite valid.1)) (finite.2,state)
        (product.neighborhood.axis state valid.2))
      (product.bijective widthHalf widthLength finite valid.1 state valid.2)).symm.toLinearMap else 0

theorem inverseMap_right (finite : OriginalFiniteParameter) (member : finite ∈ product.neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference insideR)
    (small : stateSize parameters reference insideR 24 0 state ≤ 2*product.neighborhood.radius)
    (source : sourceSmoothRange parameters) :
    literalPhysicalSmoothForward parameters parameters.length reference insideR finite.1
      (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)
      (product.neighborhood.axis state small) (product.inverseMap widthHalf widthLength finite state source) = source := by
  classical
  rw [inverseMap,dif_pos ⟨member,small⟩]
  exact (LinearEquiv.ofBijective _ (product.bijective widthHalf widthLength finite member state small)).apply_symm_apply source

theorem inverseMap_left (finite : OriginalFiniteParameter) (member : finite ∈ product.neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference insideR)
    (small : stateSize parameters reference insideR 24 0 state ≤ 2*product.neighborhood.radius)
    (direction : stateSmoothRange parameters reference insideR) :
    product.inverseMap widthHalf widthLength finite state
      (literalPhysicalSmoothForward parameters parameters.length reference insideR finite.1
        (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)
        (product.neighborhood.axis state small) direction) = direction := by
  classical
  rw [inverseMap,dif_pos ⟨member,small⟩]
  exact (LinearEquiv.ofBijective _ (product.bijective widthHalf widthLength finite member state small)).symm_apply_apply direction

end OriginalPhysicalProduct
end Grad.OriginalInverseNeighborhood
