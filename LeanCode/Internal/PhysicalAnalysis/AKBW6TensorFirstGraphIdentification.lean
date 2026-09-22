import AKBW5TensorWeakDerivativeIdentification

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CartesianStartup
open MeasureTheory Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.TensorBootstrap
open Grad.WeightedJets Grad.WeightedJets.Ordered Grad.WeakTesting.Commutation

abbrev StartupTensorFirst (dimension rank : ℕ) := Tensor rank (StartupFirst dimension)

def startupFirstValue {dimension : ℕ} (field : StartupFirst dimension) : StartupL2 dimension :=
  base dimension 1 openUnitDisk (fun _ => 0) field

def startupFirstDirection {dimension : ℕ} (field : StartupFirst dimension) (direction : Fin 2) : StartupL2 dimension :=
  orderedDerivative dimension 1 1 openUnitDisk (fun _ => 0) le_rfl field (startupFirstWord direction)

theorem startupFirstDirection_weak {dimension : ℕ} (field : StartupFirst dimension) (direction : Fin 2) :
    HasWeakOrderedDerivative dimension openUnitDisk 1 (startupFirstWord direction)
      (startupFirstValue field) (startupFirstDirection field direction) :=
  orderedDerivative_hasWeak dimension 1 1 openUnitDisk (fun _ => 0) le_rfl field (startupFirstWord direction)

theorem startupFirst_norm_sq {dimension : ℕ} (field : StartupFirst dimension) :
    ‖field‖ ^ 2 = ‖startupFirstValue field‖ ^ 2 +
      ‖startupFirstDirection field 0‖ ^ 2 + ‖startupFirstDirection field 1‖ ^ 2 := by
  have same : startupFirstGraph (startupFirstValue field) (startupFirstDirection field)
      (startupFirstDirection_weak field) = field := by
    apply base_injective dimension 1 openUnitDisk openUnitDisk_isOpen (fun _ => 0)
    exact startupFirstGraph_base _ _ _
  exact (congrArg (fun value : StartupFirst dimension => ‖value‖ ^ 2) same).symm.trans
    (startupFirstGraph_norm_sq (startupFirstValue field) (startupFirstDirection field) (startupFirstDirection_weak field))

def startupTensorFirstValues {dimension rank : ℕ} (fields : StartupTensorFirst dimension rank) :
    Tensor rank (StartupL2 dimension) := WithLp.toLp 2 (fun word => startupFirstValue (fields word))

def startupTensorFirstDirections {dimension rank : ℕ} (fields : StartupTensorFirst dimension rank) (direction : Fin 2) :
    Tensor rank (StartupL2 dimension) := WithLp.toLp 2 (fun word => startupFirstDirection (fields word) direction)

def startupTensorFirstCollect {dimension rank : ℕ} (fields : StartupTensorFirst dimension rank) :
    StartupFirst (startupTensorDimension dimension rank) :=
  startupFirstGraph
    (startupTensorFieldEquiv dimension rank (startupTensorFirstValues fields))
    (fun direction => startupTensorFieldEquiv dimension rank (startupTensorFirstDirections fields direction))
    (fun direction => (startupTensorField_weak_iff dimension rank 1 (startupFirstWord direction)
      (startupTensorFirstValues fields) (startupTensorFirstDirections fields direction)).mpr
        (fun word => startupFirstDirection_weak (fields word) direction))

theorem startupTensorFirstCollect_base {dimension rank : ℕ} (fields : StartupTensorFirst dimension rank) :
    startupFirstValue (startupTensorFirstCollect fields) =
      startupTensorFieldEquiv dimension rank (startupTensorFirstValues fields) :=
  startupFirstGraph_base _ _ _

theorem startupTensorFirstCollect_norm {dimension rank : ℕ} (fields : StartupTensorFirst dimension rank) :
    ‖startupTensorFirstCollect fields‖ = ‖fields‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change ‖startupFirstGraph _ _ _‖ ^ 2 = _
  rw [startupFirstGraph_norm_sq]
  simp only [LinearIsometryEquiv.norm_map, PiLp.norm_sq_eq_of_L2]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun word _ => (startupFirst_norm_sq (fields word)).symm)

end Grad.CartesianStartup
