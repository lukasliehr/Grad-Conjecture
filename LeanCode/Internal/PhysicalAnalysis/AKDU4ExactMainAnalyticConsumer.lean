import AKDU3FixedOriginalPhaseParameters
import AKDT34ExactMainFromActualCellFamilies

noncomputable section
set_option autoImplicit false
open Set

namespace Grad.OriginalMainConsumer
open Grad.CartesianState Grad.Constraints Grad.PhysicalFamily Grad.PhysicalGeometry
open Grad.OriginalInverseNeighborhood

/-- Exact Main from the single still-visible analytic obligation: the actual
original inverse's uniform one-high estimate on an actual good-center product.
The base and loss are arbitrary fixed finite indices. Every seed, scale,
nonlinear branch, real cell family, sampled field and geometric clause is
constructed by checked predecessors. -/
theorem exact_main_of_original_oneHigh
    (analytic : ∀ (length : ℝ) (positive : 0 < length),
      let parameters := mainPhaseParameters length positive
      ∃ (product : OriginalPhysicalProduct parameters parameters.length_pos originalSeedCenter
          originalSeedCenter_inside originalSeedCenter) (base loss : ℕ),
        6 ≤ loss ∧ Nonempty (ActualProductOneHigh product
          (mainPhaseParameters_widthHalf length positive) (mainPhaseParameters_widthLength length positive) base loss)) :
    Grad.MainTarget.mainTheoremStatement := by
  apply exact_main_of_actual_cell_families
  intro length positive
  have family : Nonempty (CellSolutionFamily length) := by
    obtain ⟨product, base, loss, lossLarge, ⟨estimate⟩⟩ := analytic length positive
    exact actual_cell_family_of_product_oneHigh estimate lossLarge
  exact Classical.choice family

end Grad.OriginalMainConsumer
