import AKDW18FixedGraphBoundedAction
import AKDP62OriginalCutoffMixedNorm
import AKCO18SamePuncturedSignedFirst
import AKCX59FixedNativeRadialCutoffs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.CartesianStartup
open Grad.WeightedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.CartesianState
open Grad.ActualOriginalSourceFirst Grad.OriginalCoreRealization Grad.ActualOriginalSourceMoments Grad.NonlinearProduct
open Grad.OriginalCartesianTameEstimate

/-- The fixed circle operator controls the SAME ordinary planar norm at
the same order, with its constant chosen before the phase or original core. -/
theorem startupOriginalCircle_planarNorm (grade : ℕ) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (parameters : PhaseParameters) (core image : ACore parameters 3),
      originalSourceFieldLinear parameters image=originalCircleKernel (originalSourceFieldLinear parameters core) →
      originalPlanarNorm parameters grade image≤constant*originalPlanarNorm parameters grade core := by
  let action := startupPreservedGraphCLM originalCircleKernel originalCircle_preservesGraph grade 0
  refine ⟨‖action‖,norm_nonneg action,?_⟩
  intro parameters core image same
  let graph := originalSourceSpatialGraph parameters core grade
  have graphSame := originalSourceSpatialGraph_base parameters core grade
  have imageSame : base 3 grade openUnitDisk (fun _ => 0) (action graph)=
      (originalSourceMoments parameters image).field := by
    rw [startupPreservedGraphCLM_same,graphSame]
    exact same.symm
  rw [startupOriginalPlanarNorm_eq_graph parameters image (action graph) imageSame,
    startupOriginalPlanarNorm_eq_graph parameters core graph graphSame]
  exact action.le_opNorm graph

/-- The fixed radial annular cutoff commutes with the literal circle
projection. This transfers the actual covariant collar estimate to w. -/
theorem startupSameAnnularCircle_planarNorm (grade : ℕ) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (parameters : PhaseParameters)
      (covariant circle annularCovariant annularCircle : ACore parameters 3),
      originalSourceFieldLinear parameters circle=originalCircleKernel (originalSourceFieldLinear parameters covariant) →
      originalSourceFieldLinear parameters annularCovariant=
        startupCutoffL2 actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact
          (originalSourceFieldLinear parameters covariant) →
      originalSourceFieldLinear parameters annularCircle=
        startupCutoffL2 actualNativeAnnularCutoff actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact
          (originalSourceFieldLinear parameters circle) →
      originalPlanarNorm parameters grade annularCircle≤constant*originalPlanarNorm parameters grade annularCovariant := by
  obtain ⟨constant,nonnegative,bounded⟩ := startupOriginalCircle_planarNorm grade
  refine ⟨constant,nonnegative,?_⟩
  intro parameters covariant circle annularCovariant annularCircle circleSame covariantCut circleCut
  apply bounded parameters annularCovariant annularCircle
  rw [circleCut,circleSame,covariantCut,startupCircle_cutoff actualNativeAnnularCutoff
    actualNativeAnnularCutoff_smooth actualNativeAnnularCutoff_compact actualNativeAnnularCutoff_radial]

end Grad.CartesianStartup
