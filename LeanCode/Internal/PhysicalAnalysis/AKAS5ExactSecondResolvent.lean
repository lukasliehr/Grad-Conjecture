import TensorResolvent

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.TensorBootstrap

/-- Isometric insertion into the actual four-entry tensor Hilbert norm. -/
def startupTensorSingle {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (index : TensorIndex) : Value →ₗᵢ[ℂ] PiLp 2 (fun _ : TensorIndex => Value) := by
  classical
  exact {
    toFun := fun field : Value => PiLp.single (β := fun _ : TensorIndex => Value) 2 index field
    map_add' := fun first second => PiLp.single_add 2 index
    map_smul' := by
      intro scalar field
      apply PiLp.ext
      intro coordinate
      exact congrFun (Pi.single_smul (f := fun _ : TensorIndex => Value) index scalar field) coordinate
    norm_map' := fun field => PiLp.norm_single 2 (fun _ : TensorIndex => Value) index field }

attribute [local instance] tensorH1NormedSpace

def startupSecondL2 (index : TensorIndex) : FieldL2 →L[ℂ] FieldL2 :=
  tensorL2Resolvent.comp (startupTensorSingle index).toContinuousLinearMap

def startupSecondH1 (index : TensorIndex) : FieldH1 →L[ℂ] FieldH1 :=
  tensorH1Resolvent.comp (startupTensorSingle index).toContinuousLinearMap

theorem startupSecondL2_norm (index : TensorIndex) (field : FieldL2) :
    ‖startupSecondL2 index field‖ ≤ ‖field‖ :=
  (tensorL2Resolvent_norm_le (startupTensorSingle index field)).trans_eq
    ((startupTensorSingle index).norm_map field)

theorem startupSecondH1_norm (index : TensorIndex) (field : FieldH1) :
    ‖startupSecondH1 index field‖ ≤ ‖field‖ :=
  (tensorH1Resolvent_norm_le (startupTensorSingle index field)).trans_eq
    ((startupTensorSingle index).norm_map field)

theorem startupTensorSingle_value (index : TensorIndex) (field : FieldH1) :
    tensorValueInclusion (startupTensorSingle index field) =
      startupTensorSingle index (valueInclusion field) := by
  apply PiLp.ext
  intro coordinate
  rw [tensorValueInclusion_apply]
  change valueInclusion (PiLp.single (β := fun _ : TensorIndex => FieldH1) 2 index field coordinate) =
    PiLp.single (β := fun _ : TensorIndex => FieldL2) 2 index (valueInclusion field) coordinate
  by_cases same : index = coordinate
  · subst coordinate
    simp only [PiLp.single_eq_same]
  · simp only [PiLp.single_eq_of_ne' 2 same, map_zero]

theorem startupSecond_compatible (index : TensorIndex) (field : FieldH1) :
    valueInclusion (startupSecondH1 index field) = startupSecondL2 index (valueInclusion field) := by
  change valueInclusion (tensorH1Resolvent (startupTensorSingle index field)) = _
  rw [tensorH1Resolvent_value, startupTensorSingle_value]
  rfl

end Grad.CartesianStartup
