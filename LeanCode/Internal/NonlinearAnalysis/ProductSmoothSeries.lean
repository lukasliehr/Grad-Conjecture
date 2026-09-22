import ProductWeightedCell
import Mathlib.Analysis.Calculus.SmoothSeries

noncomputable section

open Set Filter
open scoped BigOperators ContDiff Topology

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState

theorem allOrderDerivative_hasFDerivAt {Source Value : Type}
    [NormedAddCommGroup Source] [NormedSpace ℝ Source]
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : Source → Value) (smooth : ContDiff ℝ ∞ field) (order : ℕ) (point : Source) :
    HasFDerivAt (iteratedFDeriv ℝ order field)
      (iteratedFDeriv ℝ (order + 1) field point).curryLeft point := by
  have derivative := (smooth.contDiffAt (x := point) |>.differentiableAt_iteratedFDeriv
    (ENat.natCast_lt_of_coe_top_le_withTop le_rfl order)).hasFDerivAt
  rw [fderiv_iteratedFDeriv, Function.comp_apply] at derivative
  have curryEquality (form : Source [×(order + 1)]→L[ℝ] Value) :
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (order + 1) => Source) Value) form =
        form.curryLeft := by
    ext direction directions
    rfl
  rw [curryEquality] at derivative
  exact derivative

theorem disk_operator_series_taylor {Index Value : Type}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]
    (fields : Index → SpatialPlane → Value) (smooth : ∀ index, ContDiff ℝ ∞ (fields index))
    (majorant : ℕ → Index → ℝ) (summable : ∀ order, Summable (majorant order))
    (bounded : ∀ order index point, point ∈ closedUnitDisk →
      ‖iteratedFDeriv ℝ order (fields index) point‖ ≤ majorant order index) :
    HasFTaylorSeriesUpToOn ∞ (fun point => ∑' index, fields index point)
      (fun point order => ∑' index, iteratedFDeriv ℝ order (fields index) point) openUnitDisk := by
  have pointSummable (order : ℕ) (point : SpatialPlane) (pointIn : point ∈ closedUnitDisk) :
      Summable (fun index => iteratedFDeriv ℝ order (fields index) point) :=
    Summable.of_norm_bounded (summable order) (fun index => bounded order index point pointIn)
  have originIn : (0 : SpatialPlane) ∈ openUnitDisk := by simp [openUnitDisk]
  have diskConnected : IsPreconnected openUnitDisk := by
    rw [openUnitDisk_eq_ball]
    exact (convex_ball (0 : SpatialPlane) 1).isPreconnected
  refine ⟨?_, ?_, ?_⟩
  · intro point pointIn
    change (continuousMultilinearCurryFin0 ℝ SpatialPlane Value)
      (∑' index, iteratedFDeriv ℝ 0 (fields index) point) = _
    calc
      _ = ∑' index, (continuousMultilinearCurryFin0 ℝ SpatialPlane Value)
          (iteratedFDeriv ℝ 0 (fields index) point) :=
        (continuousMultilinearCurryFin0 ℝ SpatialPlane Value).toContinuousLinearEquiv.map_tsum
      _ = _ := by
        apply tsum_congr
        intro index
        simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply,
          LinearIsometryEquiv.apply_symm_apply]
  · intro order _ point pointIn
    have eachDerivative (index : Index) (source : SpatialPlane) :
        HasFDerivAt (iteratedFDeriv ℝ order (fields index))
          (iteratedFDeriv ℝ (order + 1) (fields index) source).curryLeft source :=
      allOrderDerivative_hasFDerivAt (fields index) (smooth index) order source
    have seriesDerivative := hasFDerivAt_tsum_of_isPreconnected (summable (order + 1))
      openUnitDisk_isOpen diskConnected
      (fun index source _ => eachDerivative index source)
      (fun index source sourceIn => by
        rw [ContinuousMultilinearMap.curryLeft_norm]
        exact bounded (order + 1) index source (openDiskMembershipClosed source sourceIn))
      originIn (pointSummable order 0 (openDiskMembershipClosed 0 originIn)) pointIn
    have currySum : (∑' index, iteratedFDeriv ℝ (order + 1) (fields index) point).curryLeft =
        ∑' index, (iteratedFDeriv ℝ (order + 1) (fields index) point).curryLeft := by
      exact (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (order + 1) => SpatialPlane) Value).toContinuousLinearEquiv.map_tsum
    rw [currySum]
    exact seriesDerivative.hasFDerivWithinAt
  · intro order _
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun point : OpenDisk => ∑' index, iteratedFDeriv ℝ order (fields index) point.val)
    apply continuous_tsum
      (fun index => ((smooth index).continuous_iteratedFDeriv
        (by exact_mod_cast le_top)).comp continuous_subtype_val) (summable order)
    intro index point
    exact bounded order index point.val (openDiskMembershipClosed point.val point.property)

theorem disk_operator_series_smooth {Index Value : Type}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]
    (fields : Index → SpatialPlane → Value) (smooth : ∀ index, ContDiff ℝ ∞ (fields index))
    (majorant : ℕ → Index → ℝ) (summable : ∀ order, Summable (majorant order))
    (bounded : ∀ order index point, point ∈ closedUnitDisk →
      ‖iteratedFDeriv ℝ order (fields index) point‖ ≤ majorant order index) :
    ContDiffOn ℝ ∞ (fun point => ∑' index, fields index point) openUnitDisk :=
  (disk_operator_series_taylor fields smooth majorant summable bounded).contDiffOn

end Grad.NonlinearProduct
