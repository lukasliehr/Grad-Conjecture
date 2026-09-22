import NonlinearQuotientInterface

noncomputable section

open Set MeasureTheory
open scoped Interval Topology

namespace Grad.NonlinearQuotient

theorem negMulLog_eq_radialKernel (scale : ℝ) :
    Real.negMulLog scale = scale * Real.log (1 / scale) := by
  rw [one_div, Real.log_inv]
  simp [Real.negMulLog]

/-- The log-weighted fundamental theorem for the radial ODE. The primitive
uses the continuous function t log t, so the origin is an actual endpoint. -/
theorem radial_ode_integral
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    [CompleteSpace Target]
    (value first second forcing : ℝ → Target)
    (valueContinuous : ContinuousOn value (Icc 0 1))
    (firstContinuous : ContinuousOn first (Icc 0 1))
    (forcingContinuous : ContinuousOn forcing (Icc 0 1))
    (valueDerivative : ∀ scale ∈ Ioo (0 : ℝ) 1,
      HasDerivAt value (first scale) scale)
    (firstDerivative : ∀ scale ∈ Ioo (0 : ℝ) 1,
      HasDerivAt first (second scale) scale)
    (radialEquation : ∀ scale ∈ Ioo (0 : ℝ) 1,
      first scale + scale • second scale = scale • forcing scale) :
    (∫ scale in (0 : ℝ)..1, Real.negMulLog scale • forcing scale) = value 1 - value 0 := by
  let primitive : ℝ → Target := fun scale =>
    value scale - (scale * Real.log scale) • first scale
  have primitiveContinuous : ContinuousOn primitive (Icc 0 1) :=
    valueContinuous.sub (Real.continuous_mul_log.continuousOn.smul firstContinuous)
  have integrable : IntervalIntegrable
      (fun scale => Real.negMulLog scale • forcing scale) volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le zero_le_one]
    intro scale scaleIn
    exact Real.continuous_negMulLog.continuousAt.continuousWithinAt.smul
      (forcingContinuous scale scaleIn)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := primitive) zero_lt_one ?_ integrable ?_ ?_
  · intro scale scaleIn
    have derivative := (valueDerivative scale scaleIn).sub
      ((Real.hasDerivAt_mul_log scaleIn.1.ne').smul (firstDerivative scale scaleIn))
    convert derivative using 1
    · rfl
    · calc
        Real.negMulLog scale • forcing scale =
            (-Real.log scale) • (scale • forcing scale) := by
          rw [smul_smul]
          congr 1
          dsimp [Real.negMulLog]
          ring
        _ = (-Real.log scale) • (first scale + scale • second scale) := by
          rw [radialEquation scale scaleIn]
        _ = first scale -
            ((scale * Real.log scale) • second scale + (Real.log scale + 1) • first scale) := by
          module
  · have endpoint := (primitiveContinuous 0 (by simp)).tendsto.mono_left
      (nhdsWithin_mono 0 Ioo_subset_Icc_self)
    simpa [primitive] using endpoint
  · have endpoint := (primitiveContinuous 1 (by simp)).tendsto.mono_left
      (nhdsWithin_mono 1 Ioo_subset_Icc_self)
    simpa [primitive] using endpoint

theorem integral_radialKernel :
    (∫ scale in (0 : ℝ)..1, Real.negMulLog scale) = 1 / 4 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := fun scale : ℝ =>
      -(scale * (scale * Real.log scale) / 2) + scale ^ 2 / 4)
    (fa := 0) (fb := (1 : ℝ) / 4)
    (hint := Real.continuous_negMulLog.intervalIntegrable 0 1)]
  · ring
  · norm_num
  · intro scale membership
    have derivative := (((hasDerivAt_id scale).mul
      (Real.hasDerivAt_mul_log membership.1.ne')).div_const 2).neg.add
        (((hasDerivAt_id scale).pow 2).div_const 4)
    convert derivative using 1
    · rfl
    · dsimp [Real.negMulLog]
      ring
  · have primitiveContinuous : Continuous (fun scale : ℝ =>
        -(scale * (scale * Real.log scale) / 2) + scale ^ 2 / 4) := by
      exact ((continuous_id.mul Real.continuous_mul_log).div_const 2).neg.add
        ((continuous_id.pow 2).div_const 4)
    convert tendsto_nhdsWithin_of_tendsto_nhds primitiveContinuous.continuousAt using 1
    norm_num
  · have primitiveContinuous : Continuous (fun scale : ℝ =>
        -(scale * (scale * Real.log scale) / 2) + scale ^ 2 / 4) := by
      exact ((continuous_id.mul Real.continuous_mul_log).div_const 2).neg.add
        ((continuous_id.pow 2).div_const 4)
    convert tendsto_nhdsWithin_of_tendsto_nhds primitiveContinuous.continuousAt using 1
    norm_num

end Grad.NonlinearQuotient
