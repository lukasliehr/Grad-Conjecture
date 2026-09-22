import AKDX12SameOriginalCutoffPlanarNorm
import AKCX59FixedNativeRadialCutoffs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.OriginalCollarNorm
open Grad.Constraints Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup
open Grad.OriginalCoreRealization Grad.ActualOriginalSourceMoments Grad.OriginalCartesianTameEstimate
open Grad.BoundaryTrace Grad.BoundaryLift

theorem actualNativeAnnularCutoff_zero_inner (point : SpatialPlane) (inside : ‖point‖<2*(1/8:ℝ)) :
    actualNativeAnnularCutoff point=0 := by
  by_contra nonzero
  have supported := actualNativeAnnularCutoff_support (subset_tsupport _ nonzero)
  have small : ‖point‖^2<(1/16:ℝ) := by nlinarith [norm_nonneg point]
  exact (not_lt_of_ge supported.1) small

/-- The existing fixed native annular cutoff is controlled on the fixed
radius-one-eighth collar, with a constant chosen before the physical data. -/
theorem actualAnnular_planarNorm (grade : ℕ) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (parameters : PhaseParameters) (core image : ACore parameters 3),
      (originalSourceMoments parameters image).field=
        startupCutoffL2 actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth
          actualNativeAnnularCutoff_compact (originalSourceMoments parameters core).field →
      ∀ payment : ℝ,0≤payment →
      (∀ cells : Finset ℤ,(∑ cell∈cells,fixedCollarIntegral (1/8)
        (polarJetSquaredDensity
          (smoothClosedExtension (phaseWeightedJet parameters cell (core.val cell)) ∘ collarPlane) grade))≤payment^2) →
      originalPlanarNorm parameters grade image≤constant*payment :=
  sameOriginalCutoff_planarNorm (1/8) (by norm_num) (by norm_num)
    actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact
    actualNativeAnnularCutoff_zero_inner grade

end Grad.OriginalCollarNorm
