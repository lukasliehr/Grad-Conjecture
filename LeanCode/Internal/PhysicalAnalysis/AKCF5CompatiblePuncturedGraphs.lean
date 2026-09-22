import AKCF4SameAnnularCutoffGraphs
import AKBV18SameCompatibleNativeOriginalCore

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators
namespace Grad.NativePuncturedGraph
open Grad.ClosedJets Grad.CartesianState Grad.CartesianCoreRecovery Grad.SourceCollarDivision
open Grad.ActualSmoothPhysicalField Grad.Constraints Grad.DiskExtension.Operator Grad.SourceCollarFullSource
open Grad.ActualCartesianDescent
open Grad.PDEBootstrap Grad.GenericCarriers Grad.CartesianStartup Grad.WeightedJets Grad.ActualPuncturedFamily

variable (lower : ℕ→ℝ) (cofinal : Tendsto lower atTop (𝓝 0))
    (scale : ℝ) (cutoff : SpatialPlane→ℝ) (compact : HasCompactSupport cutoff)
    (punctured : tsupport cutoff⊆{point | 0<‖scale • point‖ ∧ ‖scale • point‖<1})

include cofinal compact punctured in
/-- A compact punctured cutoff lies inside one of the existing strict collars. -/
theorem puncturedCutoff_collar : ∃ index : ℕ, tsupport cutoff⊆{point | ‖scale • point‖∈Ioo (lower index) 1} := by
  by_cases nonempty : (tsupport cutoff).Nonempty
  · obtain ⟨point,member,least⟩ := compact.exists_isMinOn nonempty (continuous_const_smul scale).norm.continuousOn
    let index := selectedInnerCollar lower cofinal ‖scale • point‖ (punctured member).1
    refine ⟨index,fun query inside => ⟨?_,(punctured inside).2⟩⟩
    exact (selectedInnerCollar_lt lower cofinal ‖scale • point‖ (punctured member).1).trans_le (least inside)
  · exact ⟨0,fun point inside => False.elim (nonempty ⟨point,inside⟩)⟩

variable {dimension : ℕ} (parameters : PhaseParameters)
    (positive : ∀ index,0<lower index) (bounded : ∀ index,lower index<1) (decreasing : Antitone lower)
    (rows : ∀ index,DivisionRow dimension (lower index))
    (curves : ∀ index,SmoothLowPhysicalRow parameters (lower index) (positive index) (rows index))
    (compatible : ∀ first second (ordered : first≤second),
      Grad.AnnularRestriction.originalBulkRestriction dimension (lower second) (lower first) (decreasing ordered) (rows second)=rows first)
    (smooth : ContDiff ℝ ∞ cutoff)

/-- SAME compatible native reconstruction, localized by any smooth compact
punctured cutoff, with arbitrary spatial order and arbitrary cell weight. -/
def compatibleNativeCutoffGraph (order weight : ℕ) : GraphGrade dimension order weight openUnitDisk :=
  let index := (puncturedCutoff_collar lower cofinal scale cutoff compact punctured).choose
  nativeAnnularCutoffGraph (curves index) (bounded index) scale cutoff smooth
    (puncturedCutoff_collar lower cofinal scale cutoff compact punctured).choose_spec order weight

include compatible in
theorem compatibleNativeCutoffGraph_same (order weight : ℕ) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      base dimension order openUnitDisk (fun _ => weight)
        (compatibleNativeCutoffGraph lower cofinal scale cutoff compact punctured parameters positive bounded rows curves smooth order weight) point cell=
      cutoff point • (cartesianWeight parameters cell (scale • point) •
        gluedCartesianCellField parameters lower positive bounded cofinal rows curves cell (scale • point)) := by
  let index := (puncturedCutoff_collar lower cofinal scale cutoff compact punctured).choose
  have supported := (puncturedCutoff_collar lower cofinal scale cutoff compact punctured).choose_spec
  filter_upwards [nativeAnnularCutoffGraph_same (curves index) (bounded index) scale cutoff smooth supported order weight]
    with point same
  intro cell
  apply (same cell).trans
  by_cases zero : cutoff point=0
  · simp only [zero,zero_smul]
  · have inside : ‖scale • point‖∈Icc (lower index) 1 :=
      ⟨(supported (subset_closure zero)).1.le,(supported (subset_closure zero)).2.le⟩
    rw [compatibleNativeCell_collar parameters lower positive bounded cofinal decreasing rows curves compatible index _ inside cell]

end Grad.NativePuncturedGraph
