import AKEH10ActualOriginalPlanarEstimate
import AKDV18ExactMainFromCompactPlanar

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4000
namespace Grad.OriginalMainConsumer
open Grad.CartesianState Grad.Constraints Grad.PhysicalFamily Grad.PhysicalGeometry
open Grad.OriginalInverseNeighborhood Grad.PDEBootstrap Grad.CartesianStartup

/-- The unchanged exact Main statement, from the actual original inverse,
its uniform one-high estimate, the actual Newton branch, and full geometry. -/
theorem actualOriginal_mainTheorem : Grad.MainTarget.mainTheoremStatement := by
  apply exact_main_of_actual_compact_planar
  intro length positive
  refine ⟨actualNativeOuterCutoff,actualNativeOuterCutoff_smooth,actualNativeOuterCutoff_compact,
    40,0,32,by norm_num,by norm_num,by norm_num,?_⟩
  exact ⟨actualPrincipal_compactPlanarEstimate (mainPhaseParameters length positive)
    (mainPhaseParameters length positive).length_pos originalSeedCenter originalSeedCenter_inside
    originalSeedCenter originalSeedCenter_inside originalSeedCenter_zero
    (mainPhaseParameters_widthHalf length positive) (mainPhaseParameters_widthLength length positive)
    40 (by norm_num)⟩

end Grad.OriginalMainConsumer
