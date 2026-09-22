import AJH5ClosedIntervalSeriesCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 300000
open Set Filter
open scoped BigOperators ENNReal Topology ContDiff
namespace Grad.AnnularWeightedSmoothness

section Series
variable {Index E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (lower upper : ℝ) (ordered : lower < upper) (order : ℕ)
    (family : ℕ → Index → ℝ → E)
    (continuous : ∀ rank ≤ order, ∀ index, ContinuousOn (family rank index) (Icc lower upper))
    (derivative : ∀ rank < order, ∀ index radius, radius ∈ Ioo lower upper →
      HasDerivAt (family rank index) (family (rank + 1) index radius) radius)
    (majorant : ℕ → Index → ℝ)
    (summable : ∀ rank ≤ order, Summable (majorant rank))
    (bound : ∀ rank ≤ order, ∀ index radius, radius ∈ Icc lower upper →
      ‖family rank index radius‖ ≤ majorant rank index)

include continuous summable bound

omit [NormedSpace ℝ E] in
theorem finiteIntervalSeries_continuousOn (rank : ℕ) (valid : rank ≤ order) :
    ContinuousOn (fun radius => ∑' index, family rank index radius) (Icc lower upper) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun radius : Icc lower upper => ∑' index, family rank index radius.val)
  exact continuous_tsum
    (fun index => continuousOn_iff_continuous_domRestrict.mp (continuous rank valid index))
    (summable rank valid) (fun index radius => bound rank valid index radius.val radius.property)

include ordered derivative

omit continuous in
theorem finiteIntervalSeries_hasDerivAt (rank : ℕ) (valid : rank < order)
    (radius : ℝ) (inside : radius ∈ Ioo lower upper) :
    HasDerivAt (fun point => ∑' index, family rank index point)
      (∑' index, family (rank + 1) index radius) radius := by
  have midpoint : (lower + upper) / 2 ∈ Ioo lower upper := by constructor <;> linarith
  exact hasDerivAt_tsum_of_isPreconnected (summable (rank + 1) valid) isOpen_Ioo (convex_Ioo lower upper).isPreconnected
    (fun index point h => derivative rank valid index point h)
    (fun index point h => bound (rank + 1) valid index point (Ioo_subset_Icc_self h)) midpoint
    (Summable.of_norm_bounded (summable rank valid.le) (fun index => bound rank valid.le index _ (Ioo_subset_Icc_self midpoint))) inside

theorem finiteIntervalSeries_hasFDerivWithinAt (rank : ℕ) (valid : rank < order)
    (radius : ℝ) (inside : radius ∈ Icc lower upper) :
    HasFDerivWithinAt (fun point => ∑' index, family rank index point)
      (ContinuousLinearMap.toSpanSingleton ℝ (∑' index, family (rank + 1) index radius)) (Icc lower upper) radius := by
  have seriesContinuous := finiteIntervalSeries_continuousOn lower upper order family continuous majorant summable bound rank valid.le
  have gradientContinuous : ContinuousOn (fun point => ContinuousLinearMap.toSpanSingleton ℝ
      (∑' index, family (rank + 1) index point)) (Icc lower upper) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.comp_continuousOn
      (finiteIntervalSeries_continuousOn lower upper order family continuous majorant summable bound (rank + 1) valid)
  rw [← closure_Ioo ordered.ne]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun point h => (finiteIntervalSeries_hasDerivAt lower upper ordered order family derivative majorant summable bound rank valid point h).differentiableAt.differentiableWithinAt)
    (convex_Ioo lower upper) isOpen_Ioo
    (fun point h => (seriesContinuous point (by simpa only [closure_Ioo ordered.ne] using h)).mono Ioo_subset_Icc_self)
  have equality : (fun point => fderiv ℝ (fun location => ∑' index, family rank index location) point) =ᶠ[𝓝[Ioo lower upper] radius]
      (fun point => ContinuousLinearMap.toSpanSingleton ℝ (∑' index, family (rank + 1) index point)) := by
    filter_upwards [self_mem_nhdsWithin] with point h
    exact (finiteIntervalSeries_hasDerivAt lower upper ordered order family derivative majorant summable bound rank valid point h).hasFDerivAt.fderiv
  exact (tendsto_congr' equality).mpr ((gradientContinuous radius inside).mono Ioo_subset_Icc_self).tendsto

theorem finiteIntervalSeries_contDiffOn (rank regularity : ℕ) (valid : rank + regularity ≤ order) :
    ContDiffOn ℝ regularity (fun radius => ∑' index, family rank index radius) (Icc lower upper) := by
  induction regularity generalizing rank with
  | zero => exact contDiffOn_zero.mpr (finiteIntervalSeries_continuousOn lower upper order family continuous majorant summable bound rank (by simpa using valid))
  | succ regularity previous =>
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (uniqueDiffOn_Icc ordered)]
      refine ⟨by simp, (fun point => ContinuousLinearMap.toSpanSingleton ℝ (∑' index, family (rank + 1) index point)), ?_, ?_⟩
      · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ E).toContinuousLinearEquiv.contDiff :
          ContDiff ℝ regularity (ContinuousLinearMap.toSpanSingletonLIE ℝ E)).comp_contDiffOn (previous (rank + 1) (by omega))
      · intro point h
        exact finiteIntervalSeries_hasFDerivWithinAt lower upper ordered order family continuous derivative majorant summable bound rank (by omega) point h

/-- Exactly finitely many uniform summable jet bounds suffice at the original
closed interval. No bound on any higher radial derivative is required. -/
theorem intervalSeries_contDiffOn_order :
    ContDiffOn ℝ order (fun radius => ∑' index, family 0 index radius) (Icc lower upper) :=
  finiteIntervalSeries_contDiffOn lower upper ordered order family continuous derivative majorant summable bound 0 order (by omega)

end Series
end Grad.AnnularWeightedSmoothness
