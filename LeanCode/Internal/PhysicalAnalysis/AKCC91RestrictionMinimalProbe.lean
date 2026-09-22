import AKAP3ActualCutoffOperator
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 1500
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.WeightedJets
private theorem restrictionTwoMaps
    {Input Fine Coarse Middle : Type*}
    [NormedAddCommGroup Input] [NormedSpace ℂ Input]
    [NormedAddCommGroup Fine] [NormedSpace ℂ Fine]
    [NormedAddCommGroup Coarse] [NormedSpace ℂ Coarse]
    [NormedAddCommGroup Middle] [NormedSpace ℂ Middle]
    (inclusion : Fine →L[ℂ] Coarse) (injective : Function.Injective inclusion)
    (restriction : Middle →L[ℂ] Coarse) (value : Input →L[ℂ] Middle)
    (realized : ∀ field : Input, ∃ graph : Fine,
      inclusion graph = restriction (value field) ∧ ‖graph‖ ≤ ‖field‖) :
    ∃ lift : Input →L[ℂ] Fine,
      (∀ field, inclusion (lift field) = restriction (value field)) ∧ ‖lift‖ ≤ 1 := by
  refine startupBoundedLift inclusion injective (restriction.comp value) 1 zero_le_one ?_
  intro field
  obtain ⟨graph, same, bounded⟩ := realized field
  exact ⟨graph, same, by simpa only [one_mul] using bounded⟩
theorem restrictionMinimalProbe :
    ∃ restriction : FieldH1 →L[ℂ] StartupFirst 3,
      (∀ field, base 3 1 openUnitDisk (fun _ => 0) (restriction field) = startupPlaneRestriction (valueInclusion field)) ∧ ‖restriction‖ ≤ 1 :=
  restrictionTwoMaps (base 3 1 openUnitDisk (fun _ => 0))
    (base_injective 3 1 openUnitDisk openUnitDisk_isOpen (fun _ => 0))
    startupPlaneRestriction valueInclusion startupH1_diskGraph_exists
end Grad.CartesianStartup
