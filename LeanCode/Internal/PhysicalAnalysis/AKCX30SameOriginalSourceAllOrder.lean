import AKCX29ActualSourceAllSpatialGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualOriginalSourceFirst
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers
open Grad.CartesianStartup Grad.ActualOriginalSourceMoments Grad.ActualScalarWeakEquations
open Grad.WeightedJets Grad.SpatialDilation

/-- Existing jet dilation and restriction preserve every spatial grade and the SAME base carrier. -/
theorem startupSpatialGraph_dilate_exists {dimension order : ℕ} (scale : Scale) (field : GraphGrade dimension order 0 openUnitDisk) :
    ∃ dilated : GraphGrade dimension order 0 openUnitDisk,
      base dimension order openUnitDisk (fun _ => 0) dilated =
        startupMomentDilation scale (base dimension order openUnitDisk (fun _ => 0) field) ∧
      ‖dilated‖ ≤ scale.val⁻¹ * ‖field‖ := by
  have onDisk : ∀ input : GraphGrade dimension order 0 (disk 1),
      ∃ output : GraphGrade dimension order 0 (disk 1),
        (∀ᵐ point ∂volume.restrict (disk 1),
          base dimension order (disk 1) (fun _ => 0) output point =
            base dimension order (disk 1) (fun _ => 0) input (scale.val • point)) ∧
        ‖output‖ ≤ scale.val⁻¹ * ‖input‖ := by
    intro input
    let expanded := jetDilation dimension order 1 scale (fun _ => 0) input
    refine ⟨restrictExpanded dimension order 1 scale (fun _ => 0) expanded, ?_, ?_⟩
    · rw [restrictExpanded,Restriction.restriction_base,jetDilation_base]
      exact (Restriction.fieldRestriction_ae (CellValues dimension) (disk_subset_expanded 1 scale)
        (rawValue dimension (disk 1) Metric.isOpen_ball.measurableSet scale
          (base dimension order (disk 1) (fun _ => 0) input))).trans
        (ae_restrict_of_ae_restrict_of_subset (disk_subset_expanded 1 scale)
          (rawValue_ae dimension (disk 1) Metric.isOpen_ball.measurableSet scale
            (base dimension order (disk 1) (fun _ => 0) input)))
    · exact (Restriction.restriction_norm_le dimension order (disk_subset_expanded 1 scale)
        (expandedDisk_open 1 scale).measurableSet (fun _ => 0) expanded).trans
          (jetDilation_norm_le dimension order 1 scale (fun _ => 0) input)
  have unit : disk 1 = openUnitDisk := openUnitDisk_eq_ball.symm
  rw [unit] at onDisk
  obtain ⟨output,same,bound⟩ := onDisk field
  refine ⟨output,?_,bound⟩
  apply Lp.ext
  filter_upwards [same,startupMomentDilation_ae scale
    (base dimension order openUnitDisk (fun _ => 0) field)] with point first second
  exact first.trans second.symm

variable {dimension : ℕ} (parameters : PhaseParameters) (field : ACore parameters dimension)

def scaledOriginalSourceSpatialGraph (scale : Scale) (order : ℕ) : GraphGrade dimension order 0 openUnitDisk :=
  (startupSpatialGraph_dilate_exists scale (originalSourceSpatialGraph parameters field order)).choose

theorem scaledOriginalSourceSpatialGraph_base (scale : Scale) (order : ℕ) :
    base dimension order openUnitDisk (fun _ => 0) (scaledOriginalSourceSpatialGraph parameters field scale order) =
      ((originalSourceMoments parameters field).dilate scale).field := by
  exact (startupSpatialGraph_dilate_exists scale (originalSourceSpatialGraph parameters field order)).choose_spec.1.trans
    (congrArg (startupMomentDilation scale) (originalSourceSpatialGraph_base parameters field order))

end Grad.ActualOriginalSourceFirst

namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.ActualOriginalSourceFirst Grad.SpatialDilation

/-- Every signed spatial source graph comes from the SAME original core and physical scale. -/
theorem StartupSignedFirstFamily.source_allSpatialGrade {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (length : ℝ) (lengthNonzero : length ≠ 0) (scale : Scale) (order : ℕ) :
    (StartupSignedFirstFamily.source parameters field length scale).toStartupSignedFamily.HasSpatialGrade order := by
  apply StartupSignedFamily.hasSpatialGrade_of_zero _ lengthNonzero (ne_of_gt scale.property.1)
  intro power
  refine ⟨scaledOriginalSourceSpatialGraph parameters (originalSignedAxialCore parameters field length scale.val power) scale order, ?_⟩
  rw [scaledOriginalSourceSpatialGraph_base]
  exact (scaledOriginalSourceFirst_base parameters (originalSignedAxialCore parameters field length scale.val power) scale).symm

end Grad.CartesianStartup
