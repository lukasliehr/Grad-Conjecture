import AKDU4ExactMainAnalyticConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set

namespace Grad.OriginalMainConsumer
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.Q24Realization Grad.PhysicalFamily
open Grad.PhysicalCoordinates Grad.OriginalCoreRealization
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit
open Grad.OriginalInverseNeighborhood Grad.OriginalCellFamily

variable {parameters : PhaseParameters} {positive : 0 < parameters.length}
  {reference : Seed.Parameters} {inside : reference ∈ Seed.parameterDomain} {center : Seed.Parameters}
  {product : OriginalPhysicalProduct parameters positive reference inside center}
  (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length))
  {base loss : ℕ} (baseLarge : 24 ≤ base)
  (inverse : OriginalNewtonInverse (product.neighborhood.raiseBase base baseLarge) parameters.length loss)

/-- Any typed right inverse on this actual product equals the SAME already
constructed original inverse there, by the proved actual left identity. -/
theorem typedInverse_same_actualMap (finite : OriginalFiniteParameter)
    (member : finite ∈ product.neighborhood.parameterDomain)
    (state : stateSmoothRange parameters reference inside)
    (low : stateSize parameters reference inside base 0 state ≤ 2*product.neighborhood.radius)
    (source : sourceSmoothRange parameters) :
    inverse.map finite state source = product.inverseMap widthHalf widthLength finite state source := by
  have right := inverse.right finite member state low source
  have left := product.inverseMap_higher_left widthHalf widthLength base baseLarge
    finite member state low (inverse.map finite state source)
  rw [right] at left
  exact left.symm

include widthHalf widthLength

/-- The typed quantitative right inverse automatically has the required
left law on the original product; this is not an additional analytic premise. -/
theorem typedInverse_leftLaw : inverse.LeftLaw := by
  constructor
  intro finite member state low direction
  rw [typedInverse_same_actualMap widthHalf widthLength baseLarge inverse finite member state low]
  exact product.inverseMap_higher_left widthHalf widthLength base baseLarge finite member state low direction

/-- A typed OriginalNewtonInverse alone suffices on the actual good-center
product. Its left law, good seed and scale are all supplied here. -/
theorem actual_cell_family_of_typed_product_inverse
    {product : OriginalPhysicalProduct parameters positive reference inside originalSeedCenter}
    (inverse : OriginalNewtonInverse (product.neighborhood.raiseBase base baseLarge) parameters.length loss)
    (lossLarge : 6 ≤ loss) : Nonempty (CellSolutionFamily parameters.length) := by
  obtain ⟨rho, rhoPositive, rhoSmall, member⟩ := product.exists_goodSeed
  exact actualOriginalCellFamily_exists (inverse.chosenScale lossLarge)
    (typedInverse_leftLaw widthHalf widthLength baseLarge inverse) rho (Real.pi/4) (1/4) (1/4)
    rhoPositive rhoSmall (by norm_num) originalSeedAlpha_nonresonant (by norm_num) (by norm_num) member

end Grad.OriginalMainConsumer
