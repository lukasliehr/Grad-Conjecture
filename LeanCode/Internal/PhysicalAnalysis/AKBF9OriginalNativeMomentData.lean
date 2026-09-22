import AKBF6OriginalFixedCellMoments
import AKBF4SameCovariantXiNativeMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState

/-- Both fields come from the SAME compatible native solution and retain the
literal original Cartesian analytic weight. -/
structure OriginalNativeMoments (parameters : PhaseParameters)
    (covariantRaw : ℤ → Spatial → PhysicalValue 3) (xiOverRadiusRaw : ℤ → Spatial → PhysicalValue 1) where
  covariant : StartupMoments 3
  xiOverRadius : StartupMoments 1
  covariant_same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
    covariant.field point cell = cartesianWeight parameters cell point • covariantRaw cell point
  xiOverRadius_same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
    xiOverRadius.field point cell = cartesianWeight parameters cell point • xiOverRadiusRaw cell point

theorem StartupMoments.finite_bound {dimension : ℕ} (family : StartupMoments dimension) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ grade : Fin 3, ‖family.moment grade‖ ≤ constant := by
  refine ⟨∑ grade : Fin 3, ‖family.moment grade‖,Finset.sum_nonneg (fun _ _ => norm_nonneg _),?_⟩
  intro grade
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ grade)

end Grad.CartesianStartup
