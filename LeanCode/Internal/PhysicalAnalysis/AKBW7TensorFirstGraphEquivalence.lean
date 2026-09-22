import AKBW6TensorFirstGraphIdentification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open MeasureTheory Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.WeightedJets Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

def startupTensorFirstSeparate {dimension rank : ℕ}
    (field : StartupFirst (startupTensorDimension dimension rank)) : StartupTensorFirst dimension rank :=
  WithLp.toLp 2 (fun word => startupFirstGraph
    ((startupTensorFieldEquiv dimension rank).symm (startupFirstValue field) word)
    (fun direction => (startupTensorFieldEquiv dimension rank).symm (startupFirstDirection field direction) word)
    (fun direction => (startupTensorField_weak_iff dimension rank 1 (startupFirstWord direction)
      ((startupTensorFieldEquiv dimension rank).symm (startupFirstValue field))
      ((startupTensorFieldEquiv dimension rank).symm (startupFirstDirection field direction))).mp
      (by simpa only [LinearIsometryEquiv.apply_symm_apply] using startupFirstDirection_weak field direction) word))

theorem startupTensorFirstSeparate_base {dimension rank : ℕ}
    (field : StartupFirst (startupTensorDimension dimension rank)) (word : DerivativeIndex rank) :
    startupFirstValue (startupTensorFirstSeparate field word) =
      (startupTensorFieldEquiv dimension rank).symm (startupFirstValue field) word :=
by
  simp only [startupTensorFirstSeparate, startupFirstValue, WithLp.ofLp_toLp, startupFirstGraph_base]

theorem startupTensorFirstSeparate_collect {dimension rank : ℕ} (fields : StartupTensorFirst dimension rank) :
    startupTensorFirstSeparate (startupTensorFirstCollect fields) = fields := by
  apply PiLp.ext
  intro word
  apply base_injective dimension 1 openUnitDisk openUnitDisk_isOpen (fun _ => 0)
  change startupFirstValue (startupTensorFirstSeparate (startupTensorFirstCollect fields) word) = _
  rw [startupTensorFirstSeparate_base, startupTensorFirstCollect_base, LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem startupTensorFirstCollect_separate {dimension rank : ℕ}
    (field : StartupFirst (startupTensorDimension dimension rank)) :
    startupTensorFirstCollect (startupTensorFirstSeparate field) = field := by
  apply base_injective (startupTensorDimension dimension rank) 1 openUnitDisk openUnitDisk_isOpen (fun _ => 0)
  change startupFirstValue (startupTensorFirstCollect (startupTensorFirstSeparate field)) = _
  rw [startupTensorFirstCollect_base]
  have same : startupTensorFirstValues (startupTensorFirstSeparate field) =
      (startupTensorFieldEquiv dimension rank).symm (startupFirstValue field) := by
    apply PiLp.ext
    intro word
    exact startupTensorFirstSeparate_base field word
  rw [same, LinearIsometryEquiv.apply_symm_apply]
  rfl

def startupTensorFirstEquiv (dimension rank : ℕ) :
    StartupTensorFirst dimension rank ≃ₗᵢ[ℂ] StartupFirst (startupTensorDimension dimension rank) where
  toFun := startupTensorFirstCollect
  invFun := startupTensorFirstSeparate
  left_inv := startupTensorFirstSeparate_collect
  right_inv := startupTensorFirstCollect_separate
  map_add' fields other := by
    apply base_injective (startupTensorDimension dimension rank) 1 openUnitDisk openUnitDisk_isOpen (fun _ => 0)
    change startupFirstValue (startupTensorFirstCollect (fields + other)) = _
    rw [map_add]
    change startupFirstValue (startupTensorFirstCollect (fields + other)) =
      startupFirstValue (startupTensorFirstCollect fields) + startupFirstValue (startupTensorFirstCollect other)
    rw [startupTensorFirstCollect_base, startupTensorFirstCollect_base, startupTensorFirstCollect_base, ← map_add]
    apply congrArg (startupTensorFieldEquiv dimension rank)
    apply PiLp.ext
    intro word
    change base dimension 1 openUnitDisk (fun _ => 0) (fields word + other word) = _
    exact map_add _ _ _
  map_smul' scalar fields := by
    apply base_injective (startupTensorDimension dimension rank) 1 openUnitDisk openUnitDisk_isOpen (fun _ => 0)
    change startupFirstValue (startupTensorFirstCollect (scalar • fields)) = _
    rw [map_smul]
    change startupFirstValue (startupTensorFirstCollect (scalar • fields)) =
      scalar • startupFirstValue (startupTensorFirstCollect fields)
    rw [startupTensorFirstCollect_base, startupTensorFirstCollect_base, ← map_smul]
    apply congrArg (startupTensorFieldEquiv dimension rank)
    apply PiLp.ext
    intro word
    change base dimension 1 openUnitDisk (fun _ => 0) (scalar • fields word) = _
    exact map_smul _ _ _
  norm_map' := startupTensorFirstCollect_norm

theorem startupTensorFirstEquiv_base (dimension rank : ℕ) (fields : StartupTensorFirst dimension rank) :
    startupFirstValue (startupTensorFirstEquiv dimension rank fields) =
      startupTensorFieldEquiv dimension rank (startupTensorFirstValues fields) :=
  startupTensorFirstCollect_base fields

end Grad.CartesianStartup
