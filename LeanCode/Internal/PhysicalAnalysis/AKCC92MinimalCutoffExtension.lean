import AKAP3ActualCutoffOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 1800
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.WeightedJets

private theorem startupRankExtensionFor
    {Input InputBase Output OutputBase : Type*}
    [NormedAddCommGroup Input] [NormedSpace ℂ Input]
    [NormedAddCommGroup InputBase] [NormedSpace ℂ InputBase]
    [NormedAddCommGroup Output] [NormedSpace ℂ Output]
    [NormedAddCommGroup OutputBase] [NormedSpace ℂ OutputBase]
    (value : Output →L[ℂ] OutputBase) (injective : Function.Injective value)
    (baseMap : Input →L[ℂ] InputBase)
    (extension : InputBase →L[ℂ] OutputBase)
    (cutoff : InputBase →L[ℂ] InputBase) (cutoffFine : Input →L[ℂ] Input)
    (compatible : ∀ graph, baseMap (cutoffFine graph) = cutoff (baseMap graph))
    (realized : ∀ graph : Input, ∃ regular : Output,
      value regular = extension (baseMap (cutoffFine graph)) ∧ ‖regular‖ = ‖cutoffFine graph‖) :
    ∃ lift : Input →L[ℂ] Output,
      (∀ graph, value (lift graph) = extension (cutoff (baseMap graph))) ∧
      ‖lift‖ ≤ ‖cutoffFine‖ := by
  refine startupBoundedLift value injective (extension.comp (cutoff.comp baseMap))
    ‖cutoffFine‖ (norm_nonneg cutoffFine) ?_
  intro graph
  obtain ⟨regular, same, bounded⟩ := realized graph
  refine ⟨regular, ?_, bounded.le.trans (cutoffFine.le_opNorm graph)⟩
  exact same.trans (congrArg extension (compatible graph))

theorem extensionMinimalExistence (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (compact : HasCompactSupport scalar) (included : tsupport scalar ⊆ openUnitDisk) :
    ∃ extension : StartupFirst 3 →L[ℂ] FieldH1,
      (∀ field, valueInclusion (extension field) =
        startupPlaneExtension (startupCutoffL2 scalar smooth compact (base 3 1 openUnitDisk (fun _ => 0) field))) ∧
      ‖extension‖ ≤ ‖startupCutoffFirst scalar smooth compact‖ :=
  startupRankExtensionFor valueInclusion valueInclusion_injective
    (base 3 1 openUnitDisk (fun _ => 0)) startupPlaneExtension
    (startupCutoffL2 scalar smooth compact) (startupCutoffFirst scalar smooth compact)
    (startupCutoffFirst_compatible scalar smooth compact)
    (startupCutoff_h1_realization scalar smooth compact included)

end Grad.CartesianStartup
