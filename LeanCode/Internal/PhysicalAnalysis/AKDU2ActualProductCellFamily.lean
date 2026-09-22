import AKDU1ActualProductNewtonInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set

namespace Grad.OriginalMainConsumer
open Grad.CartesianState Grad.Constraints Grad.RealFixedRanges Grad.Q24Realization Grad.PhysicalFamily
open Grad.NashMoser.OriginalIteration Grad.NashMoser.OriginalLimit
open Grad.OriginalInverseNeighborhood Grad.OriginalCellFamily

/-- The actual original product supplies its good seed by openness. The
scale, original zero branch, all parameter smoothness and literal cell laws
are constructed by the accepted CY/DC/DE consumers. -/
theorem actual_cell_family_of_product_oneHigh
    {parameters : PhaseParameters} {positive : 0 < parameters.length}
    {reference : Seed.Parameters} {inside : reference ∈ Seed.parameterDomain}
    {product : OriginalPhysicalProduct parameters positive reference inside originalSeedCenter}
    {widthHalf : parameters.gamma ≤ 1/2} {widthLength : parameters.gamma ≤ Real.sqrt 5/(6*parameters.length)}
    {base loss : ℕ} (estimate : ActualProductOneHigh product widthHalf widthLength base loss)
    (lossLarge : 6 ≤ loss) : Nonempty (CellSolutionFamily parameters.length) := by
  obtain ⟨rho, rhoPositive, rhoSmall, member⟩ := product.exists_goodSeed
  exact actualOriginalCellFamily_exists (estimate.toNewtonInverse.chosenScale lossLarge)
    estimate.toNewtonInverse_leftLaw rho (Real.pi/4) (1/4) (1/4)
    rhoPositive rhoSmall (by norm_num) originalSeedAlpha_nonresonant (by norm_num) (by norm_num) member

end Grad.OriginalMainConsumer
