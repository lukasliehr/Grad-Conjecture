import AJH1PolynomialKernelAction
import Mathlib.Analysis.Calculus.FDeriv.Extend

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter
open scoped BigOperators ENNReal Topology ContDiff
namespace Grad.AnnularRadialSmoothness

section Series
variable {Index E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (lower upper : ℝ) (ordered : lower < upper)
    (family : ℕ → Index → ℝ → E)
    (derivative : ∀ order index radius, HasDerivAt (family order index) (family (order + 1) index radius) radius)
    (majorant : ℕ → Index → ℝ) (summable : ∀ order, Summable (majorant order))
    (bound : ∀ order index radius, radius ∈ Icc lower upper → ‖family order index radius‖ ≤ majorant order index)

include derivative summable bound

/-- Uniform summable derivative bounds on the actual closed collar suffice;
no control of the Fourier family outside the original domain is requested. -/
theorem intervalSeries_continuousOn (order : ℕ) :
    ContinuousOn (fun radius => ∑' index, family order index radius) (Icc lower upper) := by
  rw [continuousOn_iff_continuous_domRestrict]
  change Continuous (fun radius : Icc lower upper => ∑' index, family order index radius.val)
  exact continuous_tsum
    (fun index => (continuous_iff_continuousAt.mpr (fun radius => (derivative order index radius).continuousAt)).comp continuous_subtype_val)
    (summable order) (fun index radius => bound order index radius.val radius.property)

include ordered

theorem intervalSeries_hasDerivAt (order : ℕ) (radius : ℝ) (inside : radius ∈ Ioo lower upper) :
    HasDerivAt (fun point => ∑' index, family order index point) (∑' index, family (order + 1) index radius) radius := by
  have midpoint : (lower + upper) / 2 ∈ Ioo lower upper := by constructor <;> linarith
  exact hasDerivAt_tsum_of_isPreconnected (summable (order + 1)) isOpen_Ioo (convex_Ioo lower upper).isPreconnected
    (fun index point _ => derivative order index point)
    (fun index point h => bound (order + 1) index point (Ioo_subset_Icc_self h)) midpoint
    (Summable.of_norm_bounded (summable order) (fun index => bound order index _ (Ioo_subset_Icc_self midpoint))) inside

/-- The derivative extends through both endpoints using the accepted closure
of derivative theorem and the continuous limits of the actual next series. -/
theorem intervalSeries_hasFDerivWithinAt (order : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower upper) :
    HasFDerivWithinAt (fun point => ∑' index, family order index point)
      (ContinuousLinearMap.toSpanSingleton ℝ (∑' index, family (order + 1) index radius)) (Icc lower upper) radius := by
  have continuous := intervalSeries_continuousOn lower upper family derivative majorant summable bound order
  have gradientContinuous : ContinuousOn (fun point => ContinuousLinearMap.toSpanSingleton ℝ
      (∑' index, family (order + 1) index point)) (Icc lower upper) :=
    (ContinuousLinearMap.toSpanSingletonLIE ℝ E).continuous.comp_continuousOn
      (intervalSeries_continuousOn lower upper family derivative majorant summable bound (order + 1))
  rw [← closure_Ioo ordered.ne]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun point h => (intervalSeries_hasDerivAt lower upper ordered family derivative majorant summable bound order point h).differentiableAt.differentiableWithinAt)
    (convex_Ioo lower upper) isOpen_Ioo
    (fun point h => (continuous point (by simpa only [closure_Ioo ordered.ne] using h)).mono Ioo_subset_Icc_self)
  have equality : (fun point => fderiv ℝ (fun location => ∑' index, family order index location) point) =ᶠ[𝓝[Ioo lower upper] radius]
      (fun point => ContinuousLinearMap.toSpanSingleton ℝ (∑' index, family (order + 1) index point)) := by
    filter_upwards [self_mem_nhdsWithin] with point h
    exact (intervalSeries_hasDerivAt lower upper ordered family derivative majorant summable bound order point h).hasFDerivAt.fderiv
  exact (tendsto_congr' equality).mpr ((gradientContinuous radius inside).mono Ioo_subset_Icc_self).tendsto

theorem intervalSeries_contDiffOn (order regularity : ℕ) :
    ContDiffOn ℝ regularity (fun radius => ∑' index, family order index radius) (Icc lower upper) := by
  induction regularity generalizing order with
  | zero => exact contDiffOn_zero.mpr (intervalSeries_continuousOn lower upper family derivative majorant summable bound order)
  | succ regularity previous =>
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn (uniqueDiffOn_Icc ordered)]
      refine ⟨by simp, (fun point => ContinuousLinearMap.toSpanSingleton ℝ (∑' index, family (order + 1) index point)), ?_, ?_⟩
      · exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ E).toContinuousLinearEquiv.contDiff :
          ContDiff ℝ regularity (ContinuousLinearMap.toSpanSingletonLIE ℝ E)).comp_contDiffOn (previous (order + 1))
      · intro point h
        exact intervalSeries_hasFDerivWithinAt lower upper ordered family derivative majorant summable bound order point h

/-- Complete radial smoothness on the original closed positive collar. -/
theorem intervalSeries_smooth (order : ℕ) :
    ContDiffOn ℝ ∞ (fun radius => ∑' index, family order index radius) (Icc lower upper) :=
  contDiffOn_infty.mpr (fun regularity => intervalSeries_contDiffOn lower upper ordered family derivative majorant summable bound order regularity)

end Series
end Grad.AnnularRadialSmoothness
