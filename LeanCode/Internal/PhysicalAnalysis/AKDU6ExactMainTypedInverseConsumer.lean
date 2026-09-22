import AKDU5TypedInverseSameOriginalMap

noncomputable section
set_option autoImplicit false
open Set

namespace Grad.OriginalMainConsumer
open Grad.CartesianState Grad.Constraints Grad.PhysicalFamily Grad.PhysicalGeometry
open Grad.OriginalInverseNeighborhood Grad.NashMoser.OriginalIteration

/-- Alternate exact endpoint consuming the typed original quantitative
inverse. Its actual product and both inverse laws determine the same original
map, and no separate left-law, seed, scale, family or geometry input remains. -/
theorem exact_main_of_typed_original_inverse
    (analytic : ∀ (length : ℝ) (positive : 0 < length),
      let parameters := mainPhaseParameters length positive
      ∃ (product : OriginalPhysicalProduct parameters parameters.length_pos originalSeedCenter
          originalSeedCenter_inside originalSeedCenter) (base loss : ℕ) (baseLarge : 24 ≤ base),
        6 ≤ loss ∧ Nonempty (OriginalNewtonInverse (product.neighborhood.raiseBase base baseLarge) parameters.length loss)) :
    Grad.MainTarget.mainTheoremStatement := by
  apply exact_main_of_actual_cell_families
  intro length positive
  have family : Nonempty (CellSolutionFamily length) := by
    obtain ⟨product, base, loss, baseLarge, lossLarge, ⟨inverse⟩⟩ := analytic length positive
    exact actual_cell_family_of_typed_product_inverse (mainPhaseParameters_widthHalf length positive)
      (mainPhaseParameters_widthLength length positive) baseLarge inverse lossLarge
  exact Classical.choice family

end Grad.OriginalMainConsumer
