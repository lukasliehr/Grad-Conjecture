import MP1BridgeInterface

noncomputable section

open MeasureTheory Grad.PDEBootstrap

namespace Grad.Mollifier.Pointwise.Bridge

universe valueUniverse parameterUniverse

theorem finiteSetIntegral_apply (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] [CompleteSpace Value] (region : Set Spatial)
    (measurableRegion : MeasurableSet region) (finiteRegion : volume region ≠ ⊤)
    (field : VolumeL2 Value) :
    finiteSetIntegral Value region measurableRegion finiteRegion field =
      ∫ point in region, field point := by
  rw [finiteSetIntegral, ContinuousLinearMap.lpPairing_eq_integral,
    ← integral_indicator measurableRegion]
  apply integral_congr_ae
  filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := measurableRegion)
    (hμs := finiteRegion) (c := (1 : ℂ))] with point same
  by_cases member : point ∈ region <;> simp [same, member]

theorem integral_norm_le_sqrt_volume (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] (region : Set Spatial)
    (measurableRegion : MeasurableSet region) (finiteRegion : volume region ≠ ⊤)
    (field : VolumeL2 Value) :
    (∫ point in region, ‖field point‖) ≤ Real.sqrt (volume.real region) * ‖field‖ := by
  let normField : VolumeL2 ℝ := (Lp.memLp field).norm.toLp (fun point => ‖field point‖)
  have represented : normField =ᵐ[volume] fun point => ‖field point‖ :=
    MemLp.coeFn_toLp (Lp.memLp field).norm
  have normEquality : ‖normField‖ = ‖field‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae represented, eLpNorm_norm, Lp.norm_def]
  have setIntegralEquality : (∫ point in region, ‖field point‖) =
      inner ℝ (indicatorConstLp 2 measurableRegion finiteRegion (1 : ℝ)) normField := by
    rw [L2.inner_indicatorConstLp_one measurableRegion finiteRegion]
    exact integral_congr_ae (ae_restrict_of_ae represented.symm)
  rw [setIntegralEquality]
  calc
    _ ≤ ‖indicatorConstLp 2 measurableRegion finiteRegion (1 : ℝ)‖ * ‖normField‖ :=
      real_inner_le_norm _ _
    _ = Real.sqrt (volume.real region) * ‖field‖ := by
      rw [norm_indicatorConstLp (by norm_num) (by norm_num), normEquality]
      simp [Real.sqrt_eq_rpow]

theorem finiteSetIntegralGoal : FiniteSetIntegralGoal := by
  intro Value _normed _inner _complete region measurableRegion finiteRegion field
  exact ⟨finiteSetIntegral_apply Value region measurableRegion finiteRegion field,
    integral_norm_le_sqrt_volume Value region measurableRegion finiteRegion field⟩

theorem localProductGoal : LocalProductGoal := by
  intro Value _normed _inner _complete Parameter _measurable parameterMeasure _sigma
    family representative integrableFamily jointlyMeasurable represented region
    measurableRegion finiteRegion
  have restrictedMeasurable : AEStronglyMeasurable (Function.uncurry representative)
      (parameterMeasure.prod (volume.restrict region)) :=
    jointlyMeasurable.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
  apply (integrable_prod_iff restrictedMeasurable).2
  constructor
  · filter_upwards [represented] with parameter same
    exact (integrableOn_Lp_of_measure_ne_top (family parameter) (by norm_num) finiteRegion).congr
      (ae_restrict_of_ae same)
  · apply (integrableFamily.norm.const_mul (Real.sqrt (volume.real region))).mono'
      restrictedMeasurable.norm.integral_prod_right'
    filter_upwards [represented] with parameter same
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    calc
      (∫ point in region, ‖representative parameter point‖) =
          ∫ point in region, ‖family parameter point‖ :=
        integral_congr_ae (ae_restrict_of_ae (same.symm.fun_comp norm))
      _ ≤ Real.sqrt (volume.real region) * ‖family parameter‖ :=
        integral_norm_le_sqrt_volume Value region measurableRegion finiteRegion (family parameter)

theorem localFubiniGoal : LocalFubiniGoal := by
  intro Value _normed _inner _complete Parameter _measurable parameterMeasure _sigma
    family representative integrableFamily jointlyMeasurable represented region
    measurableRegion finiteRegion
  have integrableProduct := localProductGoal Value Parameter parameterMeasure family representative
    integrableFamily jointlyMeasurable represented region measurableRegion finiteRegion
  rw [← finiteSetIntegral_apply Value region measurableRegion finiteRegion,
    ← (finiteSetIntegral Value region measurableRegion finiteRegion).integral_comp_comm integrableFamily]
  calc
    _ = ∫ parameter, (∫ point in region, representative parameter point) ∂parameterMeasure := by
      apply integral_congr_ae
      filter_upwards [represented] with parameter same
      rw [finiteSetIntegral_apply]
      exact integral_congr_ae (ae_restrict_of_ae same)
    _ = _ := integral_integral_swap integrableProduct

end Grad.Mollifier.Pointwise.Bridge
