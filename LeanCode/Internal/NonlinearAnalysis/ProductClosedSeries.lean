import ProductSmoothSeries

noncomputable section

open Set Filter
open scoped BigOperators ContDiff Topology

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState Grad.Constraints

def closedOperatorTerm {Index Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (fields : Index → SpatialPlane → Value) (smooth : ∀ index, ContDiff ℝ ∞ (fields index))
    (order : ℕ) (index : Index) : C(ClosedDisk, SpatialPlane [×order]→L[ℝ] Value) where
  toFun point := iteratedFDeriv ℝ order (fields index) point.val
  continuous_toFun := ((smooth index).continuous_iteratedFDeriv
    (by exact_mod_cast le_top)).comp continuous_subtype_val

theorem closedOperatorTerm_summable {Index Value : Type}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]
    (fields : Index → SpatialPlane → Value) (smooth : ∀ index, ContDiff ℝ ∞ (fields index))
    (majorant : ℕ → Index → ℝ) (summable : ∀ order, Summable (majorant order))
    (bounded : ∀ order index point, point ∈ closedUnitDisk →
      ‖iteratedFDeriv ℝ order (fields index) point‖ ≤ majorant order index) (order : ℕ) :
    Summable (closedOperatorTerm fields smooth order) := by
  have normBound (index : Index) : ‖closedOperatorTerm fields smooth order index‖ ≤ majorant order index := by
    have nonnegative : 0 ≤ majorant order index :=
      (norm_nonneg (iteratedFDeriv ℝ order (fields index) (0 : SpatialPlane))).trans
        (bounded order index 0 (by simp [closedUnitDisk]))
    apply (ContinuousMap.norm_le (closedOperatorTerm fields smooth order index) nonnegative).2
    intro point
    exact bounded order index point.val point.property
  exact Summable.of_norm_bounded (f := closedOperatorTerm fields smooth order) (summable order) normBound

def closedOperatorSeries {Index Value : Type} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (fields : Index → SpatialPlane → Value) (smooth : ∀ index, ContDiff ℝ ∞ (fields index))
    (order : ℕ) : C(ClosedDisk, SpatialPlane [×order]→L[ℝ] Value) :=
  ∑' index, closedOperatorTerm fields smooth order index

theorem closedOperatorSeries_value {Index Value : Type}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value] [CompleteSpace Value]
    (fields : Index → SpatialPlane → Value) (smooth : ∀ index, ContDiff ℝ ∞ (fields index))
    (majorant : ℕ → Index → ℝ) (summable : ∀ order, Summable (majorant order))
    (bounded : ∀ order index point, point ∈ closedUnitDisk →
      ‖iteratedFDeriv ℝ order (fields index) point‖ ≤ majorant order index)
    (order : ℕ) (point : ClosedDisk) :
    closedOperatorSeries fields smooth order point =
      ∑' index, iteratedFDeriv ℝ order (fields index) point.val := by
  exact (ContinuousMap.tsum_apply
    (closedOperatorTerm_summable fields smooth majorant summable bounded order) point).symm

def smoothSeriesValue {Index : Type} {dimension : ℕ}
    (fields : Index → SpatialPlane → ComplexEuclidean dimension)
    (smooth : ∀ index, ContDiff ℝ ∞ (fields index)) : C(ClosedDisk, ComplexEuclidean dimension) :=
  ⟨fun point => (closedOperatorSeries fields smooth 0 point).curry0,
    (continuousMultilinearCurryFin0 ℝ SpatialPlane (ComplexEuclidean dimension)).continuous.comp
      (closedOperatorSeries fields smooth 0).continuous⟩

theorem smoothSeriesValue_apply {Index : Type} {dimension : ℕ}
    (fields : Index → SpatialPlane → ComplexEuclidean dimension)
    (smooth : ∀ index, ContDiff ℝ ∞ (fields index))
    (majorant : ℕ → Index → ℝ) (summable : ∀ order, Summable (majorant order))
    (bounded : ∀ order index point, point ∈ closedUnitDisk →
      ‖iteratedFDeriv ℝ order (fields index) point‖ ≤ majorant order index)
    (point : ClosedDisk) : smoothSeriesValue fields smooth point = ∑' index, fields index point.val := by
  change (continuousMultilinearCurryFin0 ℝ SpatialPlane (ComplexEuclidean dimension))
    (closedOperatorSeries fields smooth 0 point) = _
  rw [closedOperatorSeries_value fields smooth majorant summable bounded]
  calc
    _ = ∑' index, (continuousMultilinearCurryFin0 ℝ SpatialPlane (ComplexEuclidean dimension))
        (iteratedFDeriv ℝ 0 (fields index) point.val) :=
      (continuousMultilinearCurryFin0 ℝ SpatialPlane (ComplexEuclidean dimension)).toContinuousLinearEquiv.map_tsum
    _ = _ := by
      apply tsum_congr
      intro index
      simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply, LinearIsometryEquiv.apply_symm_apply]

theorem smoothSeriesValue_lift {Index : Type} {dimension : ℕ}
    (fields : Index → SpatialPlane → ComplexEuclidean dimension)
    (smooth : ∀ index, ContDiff ℝ ∞ (fields index))
    (majorant : ℕ → Index → ℝ) (summable : ∀ order, Summable (majorant order))
    (bounded : ∀ order index point, point ∈ closedUnitDisk →
      ‖iteratedFDeriv ℝ order (fields index) point‖ ≤ majorant order index) :
    EqOn (closedDiskLift (smoothSeriesValue fields smooth)) (fun point => ∑' index, fields index point)
      openUnitDisk := by
  intro point pointIn
  simp only [closedDiskLift, openDiskMembershipClosed point pointIn, dite_true]
  exact smoothSeriesValue_apply fields smooth majorant summable bounded _

def smoothSeriesDerivative {Index : Type} {dimension order : ℕ}
    (fields : Index → SpatialPlane → ComplexEuclidean dimension)
    (smooth : ∀ index, ContDiff ℝ ∞ (fields index)) (word : CartesianWord order) :
    C(ClosedDisk, ComplexEuclidean dimension) :=
  ⟨fun point => closedOperatorSeries fields smooth order point (fun position => spatialBasis (word position)),
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => SpatialPlane)
      (ComplexEuclidean dimension) (fun position => spatialBasis (word position))).continuous.comp
        (closedOperatorSeries fields smooth order).continuous⟩

theorem smoothSeriesDerivative_spec {Index : Type} {dimension order : ℕ}
    (fields : Index → SpatialPlane → ComplexEuclidean dimension)
    (smooth : ∀ index, ContDiff ℝ ∞ (fields index))
    (majorant : ℕ → Index → ℝ) (summable : ∀ order, Summable (majorant order))
    (bounded : ∀ order index point, point ∈ closedUnitDisk →
      ‖iteratedFDeriv ℝ order (fields index) point‖ ≤ majorant order index)
    (word : CartesianWord order) :
    IsCartesianExtension (smoothSeriesValue fields smooth) order word (smoothSeriesDerivative fields smooth word) := by
  intro point pointIn
  have localEquality : closedDiskLift (smoothSeriesValue fields smooth) =ᶠ[𝓝 point.val]
      (fun source => ∑' index, fields index source) := by
    filter_upwards [openUnitDisk_isOpen.mem_nhds pointIn] with source sourceIn
    exact smoothSeriesValue_lift fields smooth majorant summable bounded sourceIn
  have taylor := disk_operator_series_taylor fields smooth majorant summable bounded
  have coefficient := taylor.eq_iteratedFDerivWithin_of_uniqueDiffOn
    (m := order) (by exact_mod_cast le_top) openUnitDisk_isOpen.uniqueDiffOn pointIn
  rw [iteratedFDerivWithin_of_isOpen order openUnitDisk_isOpen pointIn] at coefficient
  change closedOperatorSeries fields smooth order point (fun position => spatialBasis (word position)) = _
  rw [closedOperatorSeries_value fields smooth majorant summable bounded]
  unfold cartesianDerivative
  rw [(localEquality.iteratedFDeriv ℝ order).eq_of_nhds, ← coefficient]

/-- A genuine closed jet of the uniformly controlled smooth series. -/
def smoothSeriesClosedJet {Index : Type} {dimension : ℕ}
    (fields : Index → SpatialPlane → ComplexEuclidean dimension)
    (smooth : ∀ index, ContDiff ℝ ∞ (fields index))
    (majorant : ℕ → Index → ℝ) (summable : ∀ order, Summable (majorant order))
    (bounded : ∀ order index point, point ∈ closedUnitDisk →
      ‖iteratedFDeriv ℝ order (fields index) point‖ ≤ majorant order index) : ClosedJet dimension where
  value := smoothSeriesValue fields smooth
  smoothInterior := (disk_operator_series_smooth fields smooth majorant summable bounded).congr
    (smoothSeriesValue_lift fields smooth majorant summable bounded)
  derivativeExists order word :=
    ⟨smoothSeriesDerivative fields smooth word,
      smoothSeriesDerivative_spec (order := order) fields smooth majorant summable bounded word⟩

theorem smoothSeriesClosedJet_value {Index : Type} {dimension : ℕ}
    (fields : Index → SpatialPlane → ComplexEuclidean dimension)
    (smooth : ∀ index, ContDiff ℝ ∞ (fields index))
    (majorant : ℕ → Index → ℝ) (summable : ∀ order, Summable (majorant order))
    (bounded : ∀ order index point, point ∈ closedUnitDisk →
      ‖iteratedFDeriv ℝ order (fields index) point‖ ≤ majorant order index) (point : ClosedDisk) :
    (smoothSeriesClosedJet fields smooth majorant summable bounded).value point =
      ∑' index, fields index point.val :=
  smoothSeriesValue_apply fields smooth majorant summable bounded point

theorem smoothSeriesClosedJet_derivative {Index : Type} {dimension order : ℕ}
    (fields : Index → SpatialPlane → ComplexEuclidean dimension)
    (smooth : ∀ index, ContDiff ℝ ∞ (fields index))
    (majorant : ℕ → Index → ℝ) (summable : ∀ order, Summable (majorant order))
    (bounded : ∀ order index point, point ∈ closedUnitDisk →
      ‖iteratedFDeriv ℝ order (fields index) point‖ ≤ majorant order index) (word : CartesianWord order) :
    closedDerivative (smoothSeriesClosedJet fields smooth majorant summable bounded) order word =
      smoothSeriesDerivative fields smooth word := by
  exact (cartesianExtension_unique _ order word _
    (smoothSeriesDerivative_spec fields smooth majorant summable bounded word)).symm

end Grad.NonlinearProduct
