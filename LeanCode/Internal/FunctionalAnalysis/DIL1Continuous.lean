import DIL1Field

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues FieldL2)
open scoped Topology

namespace Grad.SpatialDilation

theorem continuous_scale_val : Continuous (fun scale : Scale => scale.val) := continuous_subtype_val

def planeDilation (dimension : ℕ) (scale : Scale) : FieldL2 dimension Set.univ →L[ℂ] FieldL2 dimension Set.univ :=
  fieldDilation dimension Set.univ MeasurableSet.univ scale

theorem eventually_half_scale : ∀ᶠ scale : Scale in 𝓝 oneScale, (1 / 2 : ℝ) < scale.val :=
  continuous_scale_val.continuousAt.eventually (eventually_gt_nhds (by norm_num [oneScale]))

theorem rawValue_plane_one (dimension : ℕ) (field : FieldL2 dimension Set.univ) :
    rawValue dimension Set.univ MeasurableSet.univ oneScale field = field := by
  apply Lp.ext
  filter_upwards [rawValue_ae dimension Set.univ MeasurableSet.univ oneScale field] with point equality
  exact equality.trans (congrArg field (one_smul ℝ point))

theorem compact_zero_outside (dimension : ℕ) (function : Spatial → CellValues dimension)
    (radius : ℝ) (support : tsupport function ⊆ Metric.closedBall (0 : Spatial) radius)
    (point : Spatial) (outside : radius < ‖point‖) : function point = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro membership
  have bound := support membership
  have : ‖point‖ ≤ radius := by simpa only [Metric.mem_closedBall, dist_zero_right] using bound
  exact (not_le.mpr outside) this

theorem compact_continuous_integral_tendsto (dimension : ℕ) (function : Spatial → CellValues dimension)
    (compact : HasCompactSupport function) (continuousFunction : Continuous function) :
    Filter.Tendsto (fun scale : Scale => ∫ point : Spatial, ‖function (scale.val • point) - function point‖ ^ 2)
      (𝓝 oneScale) (𝓝 0) := by
  obtain ⟨radius, positiveRadius, support⟩ := compact.isBounded.subset_closedBall_lt 0 (0 : Spatial)
  obtain ⟨bound, bounded⟩ := compact.exists_bound_of_continuous continuousFunction
  have nonnegativeBound : 0 ≤ bound := (norm_nonneg (function 0)).trans (bounded 0)
  let majorant : Spatial → ℝ := (Metric.closedBall (0 : Spatial) (2 * radius)).indicator (fun _ => (2 * bound) ^ 2)
  have integrableMajorant : Integrable majorant (volume : Measure Spatial) :=
    (integrableOn_const (isCompact_closedBall (0 : Spatial) (2 * radius)).measure_ne_top).integrable_indicator
      Metric.isClosed_closedBall.measurableSet
  have domination : ∀ᶠ scale : Scale in 𝓝 oneScale,
      ∀ᵐ point ∂(volume : Measure Spatial), ‖‖function (scale.val • point) - function point‖ ^ 2‖ ≤ majorant point := by
    filter_upwards [eventually_half_scale] with scale half
    apply Filter.Eventually.of_forall
    intro point
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases inside : point ∈ Metric.closedBall (0 : Spatial) (2 * radius)
    · change _ ≤ (Metric.closedBall (0 : Spatial) (2 * radius)).indicator (fun _ => (2 * bound) ^ 2) point
      rw [Set.indicator_of_mem inside]
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr
      calc
        _ ≤ ‖function (scale.val • point)‖ + ‖function point‖ := norm_sub_le _ _
        _ ≤ bound + bound := add_le_add (bounded _) (bounded _)
        _ = _ := by ring
    · have outside : 2 * radius < ‖point‖ := by
        simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using inside
      have originalZero := compact_zero_outside dimension function radius support point (by linarith)
      have scaledOutside : radius < ‖scale.val • point‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos scale.property.1]
        have comparison := mul_lt_mul_of_pos_right half (show 0 < ‖point‖ by linarith)
        nlinarith
      have scaledZero := compact_zero_outside dimension function radius support _ scaledOutside
      simp only [majorant, Set.indicator_of_notMem inside, originalZero, scaledZero, sub_self, norm_zero,
        zero_pow (by decide : 2 ≠ 0), le_refl]
  have pointwise : ∀ point : Spatial,
      Filter.Tendsto (fun scale : Scale => ‖function (scale.val • point) - function point‖ ^ 2)
        (𝓝 oneScale) (𝓝 (0 : ℝ)) := by
    intro point
    have input : Filter.Tendsto (fun scale : Scale => scale.val • point) (𝓝 oneScale) (𝓝 point) := by
      simpa only [show oneScale.val = (1 : ℝ) from rfl, one_smul] using
        ((continuous_scale_val.tendsto oneScale).smul_const point)
    have limit := (((continuousFunction.tendsto point).comp input).sub_const (function point)).norm.pow 2
    simpa only [Function.comp_apply, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using limit
  have limit := tendsto_integral_filter_of_dominated_convergence
    (F := fun scale : Scale => fun point : Spatial => ‖function (scale.val • point) - function point‖ ^ 2)
    (f := fun _ : Spatial => (0 : ℝ)) majorant
    (Filter.Eventually.of_forall (fun scale : Scale =>
      (((continuousFunction.comp (continuous_const_smul scale.val)).sub continuousFunction).norm.pow 2).aestronglyMeasurable))
    domination integrableMajorant (Filter.Eventually.of_forall pointwise)
  simpa only [integral_zero] using limit

theorem compact_continuous_tendsto (dimension : ℕ) (function : Spatial → CellValues dimension)
    (compact : HasCompactSupport function) (continuousFunction : Continuous function)
    (membership : MemLp function 2 (volume.restrict Set.univ)) :
    Filter.Tendsto (fun scale : Scale => rawValue dimension Set.univ MeasurableSet.univ scale
      (membership.toLp function)) (𝓝 oneScale) (𝓝 (membership.toLp function)) := by
  let field : FieldL2 dimension Set.univ := membership.toLp function
  change Filter.Tendsto (fun scale : Scale => planeDilation dimension scale field) (𝓝 oneScale) (𝓝 field)
  have normEquality (scale : Scale) :
      ‖planeDilation dimension scale field - field‖ ^ 2 =
        ∫ point : Spatial, ‖function (scale.val • point) - function point‖ ^ 2 := by
    calc
      _ = ∫ point in Set.univ, ‖(planeDilation dimension scale field - field) point‖ ^ 2 :=
        Grad.GenericCarriers.domainL2_norm_sq Set.univ _
      _ = ∫ point in Set.univ, ‖function (scale.val • point) - function point‖ ^ 2 := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_sub (planeDilation dimension scale field) field,
          show planeDilation dimension scale field =ᵐ[volume.restrict Set.univ]
            (fun point => field (scale.val • point)) from rawValue_ae dimension Set.univ MeasurableSet.univ scale field,
          show field =ᵐ[volume.restrict Set.univ] function from MemLp.coeFn_toLp _,
          pull_ae Set.univ MeasurableSet.univ scale
            (show field =ᵐ[volume.restrict Set.univ] function from MemLp.coeFn_toLp _)]
          with point difference rawAt sourceAt pulledAt
        rw [difference, Pi.sub_apply, rawAt, sourceAt, pulledAt]
      _ = _ := by rw [Measure.restrict_univ]
  have squared : Filter.Tendsto (fun scale : Scale =>
      ‖planeDilation dimension scale field - field‖ ^ 2) (𝓝 oneScale) (𝓝 0) := by
    simpa only [normEquality] using compact_continuous_integral_tendsto dimension function compact continuousFunction
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have limit := Real.continuous_sqrt.continuousAt.tendsto.comp squared
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using limit

theorem compact_continuous_approximation (dimension : ℕ) (field : FieldL2 dimension Set.univ)
    (error : ℝ) (positiveError : 0 < error) :
    ∃ (function : Spatial → CellValues dimension) (membership : MemLp function 2 (volume.restrict Set.univ)),
      HasCompactSupport function ∧ Continuous function ∧ ‖field - membership.toLp function‖ ≤ error := by
  have original : MemLp field 2 (volume : Measure Spatial) := by simpa only [Measure.restrict_univ] using Lp.memLp field
  obtain ⟨function, compact, approximation, continuousFunction, membership⟩ :=
    original.exists_hasCompactSupport_eLpNorm_sub_le ENNReal.ofNat_ne_top
      (ne_of_gt (ENNReal.ofReal_pos.mpr positiveError))
  have restricted : MemLp function 2 (volume.restrict Set.univ) := by
    simpa only [Measure.restrict_univ] using membership
  refine ⟨function, restricted, compact, continuousFunction, ?_⟩
  rw [Lp.norm_def]
  have represented : (field - restricted.toLp function : FieldL2 dimension Set.univ) =ᵐ[volume.restrict Set.univ]
      fun point => field point - function point := by
    filter_upwards [Lp.coeFn_sub field (restricted.toLp function), MemLp.coeFn_toLp restricted] with point difference value
    rw [difference, Pi.sub_apply, value]
  rw [eLpNorm_congr_ae represented]
  simp only [Measure.restrict_univ]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top approximation).trans_eq (ENNReal.toReal_ofReal positiveError.le)

theorem plane_continuity_goal : PlaneContinuityGoal := by
  intro dimension field
  change Filter.Tendsto (fun scale : Scale => planeDilation dimension scale field) (𝓝 oneScale) (𝓝 field)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply tendsto_order.mpr
  constructor
  · intro lower negative
    exact Filter.Eventually.of_forall (fun _ => negative.trans_le (norm_nonneg _))
  · intro error positiveError
    obtain ⟨function, membership, compact, continuousFunction, approximation⟩ :=
      compact_continuous_approximation dimension field (error / 8) (by positivity)
    let approximant : FieldL2 dimension Set.univ := membership.toLp function
    have compactLimit := tendsto_iff_norm_sub_tendsto_zero.mp
      (compact_continuous_tendsto dimension function compact continuousFunction membership)
    have near := compactLimit.eventually_lt_const (show (0 : ℝ) < error / 2 by positivity)
    filter_upwards [near, eventually_half_scale] with scale close half
    have inverseBound : scale.val⁻¹ ≤ 2 := by
      rw [← one_div]
      rw [div_le_iff₀ scale.property.1]
      linarith
    let mapping := planeDilation dimension scale
    have firstBound : ‖mapping field - mapping approximant‖ ≤ 2 * ‖field - approximant‖ := by
      rw [← map_sub]
      exact (rawValue_norm dimension Set.univ MeasurableSet.univ scale (field - approximant)).le.trans
        (mul_le_mul_of_nonneg_right inverseBound (norm_nonneg _))
    have total : ‖mapping field - field‖ ≤
        ‖mapping field - mapping approximant‖ + ‖mapping approximant - approximant‖ + ‖approximant - field‖ := by
      have first := norm_sub_le_norm_sub_add_norm_sub (mapping field) (mapping approximant) field
      have second := norm_sub_le_norm_sub_add_norm_sub (mapping approximant) approximant field
      linarith
    have reversed : ‖approximant - field‖ = ‖field - approximant‖ := norm_sub_rev _ _
    change ‖mapping field - field‖ < error
    change ‖mapping approximant - approximant‖ < error / 2 at close
    change ‖field - approximant‖ ≤ error / 8 at approximation
    linarith

end Grad.SpatialDilation
