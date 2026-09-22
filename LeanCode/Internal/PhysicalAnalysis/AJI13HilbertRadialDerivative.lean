import AJI12ActualFullPhysicalRowsSmooth
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace Grad.AnnularSmoothCore

variable {Index E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedSpace ℝ E] [CompleteSpace E]

/-- The genuine continuous Hilbert-valued right-hand side upgrades every
coordinate weak derivative to a derivative in the full Hilbert norm. -/
theorem hilbertDerivative_of_coordinates (lower : ℝ)
    (field derivative : ℝ → lp (fun _ : Index => E) 2)
    (continuous : ContinuousOn field (Icc lower 1))
    (derivativeContinuous : Continuous derivative)
    (law : ∀ index radius, radius ∈ Icc lower 1 →
      HasDerivWithinAt (fun point => field point index) (derivative radius index) (Icc lower 1) radius)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    HasDerivWithinAt field (derivative radius) (Icc lower 1) radius := by
  let primitive : ℝ → lp (fun _ : Index => E) 2 :=
    fun point => field lower + ∫ value in lower..point, derivative value
  have equality (point : ℝ) (member : point ∈ Icc lower 1) : field point = primitive point := by
    apply lp.ext
    funext index
    let projection := lp.evalCLM ℂ (fun _ : Index => E) 2 index
    have coefficientContinuous : ContinuousOn (fun value => field value index) (Icc lower point) :=
      (projection.continuous.comp_continuousOn continuous).mono (Icc_subset_Icc le_rfl member.2)
    have derivativeIntegrable : IntervalIntegrable (fun value => derivative value index) volume lower point :=
      (projection.continuous.comp derivativeContinuous).intervalIntegrable lower point
    have fundamental := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le member.1 coefficientContinuous
      (fun value interval => (law index value ⟨interval.1.le, interval.2.le.trans member.2⟩).hasDerivAt
        (Icc_mem_nhds interval.1 (interval.2.trans_le member.2))) derivativeIntegrable
    change field point index = field lower index + projection (∫ value in lower..point, derivative value)
    rw [← projection.intervalIntegral_comp_comm (derivativeContinuous.intervalIntegrable lower point)]
    change field point index = field lower index + ∫ value in lower..point, derivative value index
    rw [fundamental]
    abel
  have differentiated : HasDerivAt primitive (derivative radius) radius :=
    (intervalIntegral.integral_hasDerivAt_right
      (derivativeContinuous.intervalIntegrable lower radius)
      derivativeContinuous.stronglyMeasurable.stronglyMeasurableAtFilter
      derivativeContinuous.continuousAt).const_add (field lower)
  exact differentiated.hasDerivWithinAt.congr equality (equality radius inside)

end Grad.AnnularSmoothCore
