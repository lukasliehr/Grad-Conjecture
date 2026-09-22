import AKBS3OriginalSourceFirstWeak
import DIL1Jet

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 850000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualOriginalSourceFirst
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers
open Grad.CartesianStartup Grad.ActualOriginalSourceMoments Grad.ActualScalarWeakEquations
open Grad.WeightedJets Grad.SpatialDilation

/-- Existing jet dilation and restriction preserve the same base carrier. -/
theorem startupFirst_dilate_exists {dimension : ℕ} (scale : Scale) (field : StartupFirst dimension) :
    ∃ dilated : StartupFirst dimension,
      base dimension 1 openUnitDisk (fun _ => 0) dilated =
        startupMomentDilation scale (base dimension 1 openUnitDisk (fun _ => 0) field) ∧
      ‖dilated‖ ≤ scale.val⁻¹ * ‖field‖ := by
  have onDisk : ∀ input : GraphGrade dimension 1 0 (disk 1),
      ∃ output : GraphGrade dimension 1 0 (disk 1),
        (∀ᵐ point ∂volume.restrict (disk 1),
          base dimension 1 (disk 1) (fun _ => 0) output point =
            base dimension 1 (disk 1) (fun _ => 0) input (scale.val • point)) ∧
        ‖output‖ ≤ scale.val⁻¹ * ‖input‖ := by
    intro input
    let expanded := jetDilation dimension 1 1 scale (fun _ => 0) input
    refine ⟨restrictExpanded dimension 1 1 scale (fun _ => 0) expanded, ?_, ?_⟩
    · rw [restrictExpanded,Restriction.restriction_base,jetDilation_base]
      exact (Restriction.fieldRestriction_ae (CellValues dimension) (disk_subset_expanded 1 scale)
        (rawValue dimension (disk 1) Metric.isOpen_ball.measurableSet scale
          (base dimension 1 (disk 1) (fun _ => 0) input))).trans
        (ae_restrict_of_ae_restrict_of_subset (disk_subset_expanded 1 scale)
          (rawValue_ae dimension (disk 1) Metric.isOpen_ball.measurableSet scale
            (base dimension 1 (disk 1) (fun _ => 0) input)))
    · exact (Restriction.restriction_norm_le dimension 1 (disk_subset_expanded 1 scale)
        (expandedDisk_open 1 scale).measurableSet (fun _ => 0) expanded).trans
          (jetDilation_norm_le dimension 1 1 scale (fun _ => 0) input)
  have unit : disk 1 = openUnitDisk := openUnitDisk_eq_ball.symm
  rw [unit] at onDisk
  obtain ⟨output,same,bound⟩ := onDisk field
  refine ⟨output,?_,bound⟩
  apply Lp.ext
  filter_upwards [same,startupMomentDilation_ae scale
    (base dimension 1 openUnitDisk (fun _ => 0) field)] with point first second
  exact first.trans second.symm

variable {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)

/-- The actual original weighted source in the scaled first weak graph, without a regularity premise. -/
def scaledOriginalSourceFirst (scale : Scale) : StartupFirst dimension :=
  Classical.choose (startupFirst_dilate_exists scale (originalSourceFirst parameters field))

theorem scaledOriginalSourceFirst_base (scale : Scale) :
    base dimension 1 openUnitDisk (fun _ => 0) (scaledOriginalSourceFirst parameters field scale) =
      ((originalSourceMoments parameters field).dilate scale).field := by
  exact (Classical.choose_spec (startupFirst_dilate_exists scale (originalSourceFirst parameters field))).1.trans
    (congrArg (startupMomentDilation scale) (originalSourceFirst_base parameters field))

theorem scaledOriginalSourceFirst_norm (scale : Scale) :
    ‖scaledOriginalSourceFirst parameters field scale‖ ≤ scale.val⁻¹ * ‖originalSourceFirst parameters field‖ :=
  (Classical.choose_spec (startupFirst_dilate_exists scale (originalSourceFirst parameters field))).2

/-- Literal original phase at ell, same source and every signed cell; sigma and gamma are unchanged. -/
theorem scaledOriginalSourceFirst_same (scale : Scale) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      base dimension 1 openUnitDisk (fun _ => 0) (scaledOriginalSourceFirst parameters field scale) point cell =
        Grad.AnalyticWeights.Calculus.physicalWeight parameters.sigma0 parameters.gamma scale.val cell point •
          originalCoreCell parameters field cell (scale.val • point) := by
  rw [scaledOriginalSourceFirst_base]
  exact startupMomentDilation_weighted_same parameters.sigma0 parameters.gamma scale
    (originalCoreCell parameters field) (originalSourceMoments parameters field).field
    (originalSourceMoments_same parameters field)

end Grad.ActualOriginalSourceFirst
