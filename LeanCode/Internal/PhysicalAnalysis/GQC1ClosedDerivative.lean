import GQ17ClosedJetConsumer
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

noncomputable section

set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra

theorem closedLift_value {Value : Type*} [Zero Value]
    (field : ClosedDisk → Value) (point : SpatialPlane) (inside : point ∈ openUnitDisk) :
    closedDiskLift field point = field ⟨point, openDiskMembershipClosed point inside⟩ := by
  simp only [closedDiskLift, dif_pos (openDiskMembershipClosed point inside)]

theorem closedLift_uniform {Value : Type*} [NormedAddCommGroup Value]
    {family : ℕ → C(ClosedDisk, Value)} {limit : C(ClosedDisk, Value)}
    (converges : Tendsto family atTop (𝓝 limit)) :
    TendstoUniformlyOn (fun index => closedDiskLift (family index))
      (closedDiskLift limit) atTop openUnitDisk := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro tolerance positive
  filter_upwards [Metric.tendsto_nhds.mp converges tolerance positive] with index small
  intro point inside
  rw [closedLift_value _ point inside, closedLift_value _ point inside]
  exact (ContinuousMap.dist_apply_le_dist _).trans_lt (by simpa only [dist_comm] using small)

theorem closedLift_pointwise {Value : Type*} [NormedAddCommGroup Value]
    {family : ℕ → C(ClosedDisk, Value)} {limit : C(ClosedDisk, Value)}
    (converges : Tendsto family atTop (𝓝 limit)) (point : SpatialPlane) (inside : point ∈ openUnitDisk) :
    Tendsto (fun index => closedDiskLift (family index) point) atTop (𝓝 (closedDiskLift limit point)) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance positive
  filter_upwards [Metric.tendsto_nhds.mp converges tolerance positive] with index small
  rw [closedLift_value _ point inside, closedLift_value _ point inside]
  exact (ContinuousMap.dist_apply_le_dist _).trans_lt small

/-- Uniform closure of the genuine first-derivative graph, on the actual
closed disk. This prohibits independently chosen derivative coordinates. -/
theorem closedDerivativeGraph_isClosed {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value] :
    IsClosed {pair : C(ClosedDisk, Value) × C(ClosedDisk, SpatialPlane →L[ℝ] Value) |
      ∀ point : SpatialPlane, point ∈ openUnitDisk →
        HasFDerivAt (closedDiskLift pair.1) (closedDiskLift pair.2 point) point} := by
  let : MetricSpace C(ClosedDisk, Value) := inferInstance
  let : MetricSpace C(ClosedDisk, SpatialPlane →L[ℝ] Value) := inferInstance
  apply isClosed_of_closure_subset
  intro pair membership
  obtain ⟨sequence, compatible, converges⟩ := mem_closure_iff_seq_limit.mp membership
  have values := continuous_fst.tendsto pair |>.comp converges
  have derivatives := continuous_snd.tendsto pair |>.comp converges
  intro point inside
  exact hasFDerivAt_of_tendstoUniformlyOn openUnitDisk_isOpen
    (closedLift_uniform derivatives) compatible
    (fun point inside => closedLift_pointwise values point inside) inside

end Grad.GaugeCoefficients.Physical.Compensated
