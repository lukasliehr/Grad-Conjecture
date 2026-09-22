import ANG17FirstCompletedDerivative

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open scoped BigOperators Topology
namespace Grad.CircularHighWeak
open Grad.CartesianState

theorem diskFourier_adjoint_leftInverse (field : DiskL2 1) : diskFourier.adjoint (diskFourier field) = field := by
  apply ext_inner_right ℂ
  intro test
  exact (ContinuousLinearMap.adjoint_inner_left diskFourier test (diskFourier field)).trans
    (diskFourierIsometry.inner_map_map field test)

theorem diskFourier_adjoint_mode (mode : ℤ) (field : DiskL2 1) :
    diskFourier.adjoint (lp.single 2 mode (diskMode mode field)) = diskMode mode field := by
  exact (congrArg diskFourier.adjoint (diskFourier_mode mode field)).symm.trans
    (diskFourier_adjoint_leftInverse (diskMode mode field))

theorem diskModes_hasSum (field : DiskL2 1) : HasSum (fun mode : ℤ => diskMode mode field) field := by
  have original := lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) (diskFourier field)
  have mapped := original.mapL diskFourier.adjoint
  have equal (mode : ℤ) : diskFourier.adjoint (lp.single 2 mode (diskFourier field mode)) = diskMode mode field :=
    diskFourier_adjoint_mode mode field
  simpa only [equal, diskFourier_adjoint_leftInverse] using mapped

theorem diskSelectedModes_tendsto (field : DiskL2 1) :
    Filter.Tendsto (fun modes : Finset ℤ => diskSelectedModes modes field) Filter.atTop (𝓝 field) := by
  have series := diskModes_hasSum field
  change Filter.Tendsto (fun modes : Finset ℤ => ∑ mode ∈ modes, diskMode mode field) Filter.atTop (𝓝 field) at series
  exact series.congr' (Filter.Eventually.of_forall (fun modes => (diskSelectedModes_apply modes field).symm))

theorem finiteAngularSolution_tendsto (parameter : ℝ) (source : highDiskL2) :
    Filter.Tendsto (fun modes : Finset ℤ => highFiniteRotation modes (highRobinWeakInverse parameter source))
      Filter.atTop (𝓝 (firstAngularWeakSolution parameter source)) := by
  have series := (firstAngularSeries_summable parameter source).hasSum
  exact series.congr' (Filter.Eventually.of_forall (fun modes =>
    (highFiniteRotation_apply modes (highRobinWeakInverse parameter source)).symm))

end Grad.CircularHighWeak
