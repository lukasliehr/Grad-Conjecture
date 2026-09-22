import AKAG8CompactFirstToWholePlaneH1
import AKAG6H1ToFirstGraph

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option maxRecDepth 2000

namespace Grad.CartesianStartup
open Grad.PDEBootstrap

/-- A bounded injective inclusion uniquely determines every lift. The
 construction stays abstract so canonical measure transports never enter
 kernel normalization of the chosen linear map. -/
theorem startupBoundedLift {Input Fine Coarse : Type*}
    [NormedAddCommGroup Input] [NormedSpace ℂ Input]
    [NormedAddCommGroup Fine] [NormedSpace ℂ Fine]
    [NormedAddCommGroup Coarse] [NormedSpace ℂ Coarse]
    (inclusion : Fine →L[ℂ] Coarse) (injective : Function.Injective inclusion)
    (mapping : Input →L[ℂ] Coarse) (bound : ℝ) (boundNonnegative : 0 ≤ bound)
    (realized : ∀ field : Input, ∃ output : Fine,
      inclusion output = mapping field ∧ ‖output‖ ≤ bound * ‖field‖) :
    ∃ lift : Input →L[ℂ] Fine,
      (∀ field, inclusion (lift field) = mapping field) ∧ ‖lift‖ ≤ bound := by
  let lifted (field : Input) : Fine := (realized field).choose
  have represented (field : Input) : inclusion (lifted field) = mapping field :=
    (realized field).choose_spec.1
  have bounded (field : Input) : ‖lifted field‖ ≤ bound * ‖field‖ :=
    (realized field).choose_spec.2
  let linear : Input →ₗ[ℂ] Fine := {
    toFun := lifted
    map_add' := by
      intro first second
      apply injective
      rw [represented, map_add, map_add, represented, represented]
    map_smul' := by
      intro scalar field
      apply injective
      rw [represented, map_smul, map_smul, represented]
      rfl
  }
  let lift := linear.mkContinuous bound bounded
  refine ⟨lift, represented, ?_⟩
  exact ContinuousLinearMap.opNorm_le_bound lift boundNonnegative bounded

/-- Specialize the abstract construction to the actual SAME-field H1
 projection, preserving the original graph norm. -/
theorem startupH1_bounded_lift (mapping : FieldH1 →L[ℂ] FieldL2) (bound : ℝ)
    (boundNonnegative : 0 ≤ bound)
    (realized : ∀ field : FieldH1, ∃ output : FieldH1,
      valueInclusion output = mapping field ∧ ‖output‖ ≤ bound * ‖field‖) :
    ∃ lift : FieldH1 →L[ℂ] FieldH1,
      (∀ field, valueInclusion (lift field) = mapping field) ∧ ‖lift‖ ≤ bound :=
  startupBoundedLift valueInclusion valueInclusion_injective mapping bound boundNonnegative realized

end Grad.CartesianStartup
