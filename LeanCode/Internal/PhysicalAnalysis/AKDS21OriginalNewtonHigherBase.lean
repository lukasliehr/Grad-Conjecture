import AKDS20ProjectedSourceOneHigh
import AKDJ7ArbitrarilySmallActualProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4000
namespace Grad.NashMoser.OriginalIteration
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.Q24Realization Grad.SmoothingFamily
open Grad.OriginalCoreRealization Grad.NonlinearQuotientBounds Grad.PhysicalCoordinates

namespace OriginalNewtonNeighborhood
variable {parameters : PhaseParameters} {reference : Seed.Parameters}
  {inside : reference ∈ Seed.parameterDomain} {base : ℕ}

/-- Raising the one fixed low grade preserves the parameter product and
radius. This reuses the existing neighborhood and all original norms. -/
def raiseBase (neighborhood : OriginalNewtonNeighborhood parameters reference inside base)
    (higher : ℕ) (ordered : base≤higher) : OriginalNewtonNeighborhood parameters reference inside higher where
  baseLarge := neighborhood.baseLarge.trans ordered
  parameterDomain := neighborhood.parameterDomain
  seedPatch := neighborhood.seedPatch
  compact := neighborhood.compact
  patchInside := neighborhood.patchInside
  curvatureBound := neighborhood.curvatureBound
  seedInside := neighborhood.seedInside
  curvature := neighborhood.curvature
  radius := neighborhood.radius
  radiusPositive := neighborhood.radiusPositive
  radiusSmall := neighborhood.radiusSmall
  axis := fun state low => neighborhood.axis state
    ((referenceState_norm_mono parameters (Nat.add_le_add_right ordered 0) state.val).trans low)

theorem raiseBase_low (neighborhood : OriginalNewtonNeighborhood parameters reference inside base)
    (higher : ℕ) (ordered : base≤higher) (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside higher 0 state ≤ 2*(neighborhood.raiseBase higher ordered).radius) :
    stateSize parameters reference inside base 0 state ≤ 2*neighborhood.radius :=
  (referenceState_norm_mono parameters (Nat.add_le_add_right ordered 0) state.val).trans low

end OriginalNewtonNeighborhood
end Grad.NashMoser.OriginalIteration

namespace Grad.OriginalInverseNeighborhood.OriginalPhysicalProduct
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.Q24Realization Grad.PhysicalCoordinates
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit
open Grad.NonlinearQuotientBounds Grad.OriginalCoreRealization
variable {parameters : PhaseParameters} {positive : 0<parameters.length}
  {reference : Seed.Parameters} {insideR : reference ∈ Seed.parameterDomain} {center : Seed.Parameters}
  (product : OriginalPhysicalProduct parameters positive reference insideR center)
  (widthHalf : parameters.gamma≤1/2) (widthLength : parameters.gamma≤Real.sqrt 5/(6*parameters.length))

/-- The SAME already constructed inverse satisfies its right law on every
higher fixed base product; no inverse map is reconstructed. -/
theorem inverseMap_higher_right (higher : ℕ) (ordered : 24≤higher)
    (finite : OriginalFiniteParameter) (member : finite∈product.neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference insideR)
    (low : stateSize parameters reference insideR higher 0 state ≤
      2*(product.neighborhood.raiseBase higher ordered).radius) (source : sourceSmoothRange parameters) :
    literalPhysicalSmoothForward parameters parameters.length reference insideR finite.1
      (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)
      ((product.neighborhood.raiseBase higher ordered).axis state low)
      (product.inverseMap widthHalf widthLength finite state source)=source :=
  product.inverseMap_right widthHalf widthLength finite member state
    (product.neighborhood.raiseBase_low higher ordered state low) source

theorem inverseMap_higher_left (higher : ℕ) (ordered : 24≤higher)
    (finite : OriginalFiniteParameter) (member : finite∈product.neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference insideR)
    (low : stateSize parameters reference insideR higher 0 state ≤
      2*(product.neighborhood.raiseBase higher ordered).radius)
    (direction : stateSmoothRange parameters reference insideR) :
    product.inverseMap widthHalf widthLength finite state
      (literalPhysicalSmoothForward parameters parameters.length reference insideR finite.1
        (product.neighborhood.patchInside (product.neighborhood.seedInside finite member)) (finite.2,state)
        ((product.neighborhood.raiseBase higher ordered).axis state low) direction)=direction :=
  product.inverseMap_left widthHalf widthLength finite member state
    (product.neighborhood.raiseBase_low higher ordered state low) direction

end Grad.OriginalInverseNeighborhood.OriginalPhysicalProduct
