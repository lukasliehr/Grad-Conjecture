import DIL1Interface

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues PhysicalValue FieldL2)
open scoped Topology

namespace Grad.SpatialDilation

theorem spatial_measurePreserving (domain : Set Spatial) (measurableDomain : MeasurableSet domain)
    (scale : Scale) : MeasurePreserving (spatialMap scale)
      (volume.restrict (pullDomain scale domain)) (jacobian scale • volume.restrict domain) :=
  ⟨measurable_const_smul scale.val, map_measure domain measurableDomain scale⟩

theorem pull_ae (domain : Set Spatial) (measurableDomain : MeasurableSet domain) (scale : Scale)
    {predicate : Spatial → Prop} (almost : ∀ᵐ point ∂volume.restrict domain, predicate point) :
    ∀ᵐ point ∂volume.restrict (pullDomain scale domain), predicate (scale.val • point) :=
  (spatial_measurePreserving domain measurableDomain scale).quasiMeasurePreserving.ae
    (Measure.ae_smul_measure almost (jacobian scale))

theorem rawValue_ae (dimension : ℕ) (domain : Set Spatial) (measurableDomain : MeasurableSet domain)
    (scale : Scale) (field : FieldL2 dimension domain) :
    rawValue dimension domain measurableDomain scale field =ᵐ[volume.restrict (pullDomain scale domain)]
      fun point => field (scale.val • point) := by
  let scaled := ((Lp.memLp field).smul_measure (c := jacobian scale) ENNReal.ofReal_ne_top).toLp field
  have first : rawValue dimension domain measurableDomain scale field =ᵐ[
      volume.restrict (pullDomain scale domain)] scaled ∘ spatialMap scale :=
    Lp.coeFn_compMeasurePreserving scaled (spatial_measurePreserving domain measurableDomain scale)
  exact first.trans ((spatial_measurePreserving domain measurableDomain scale).quasiMeasurePreserving.ae
    (MemLp.coeFn_toLp _))

theorem rawValue_norm_sq (dimension : ℕ) (domain : Set Spatial) (measurableDomain : MeasurableSet domain)
    (scale : Scale) (field : FieldL2 dimension domain) :
    ‖rawValue dimension domain measurableDomain scale field‖ ^ 2 = (scale.val ^ 2)⁻¹ * ‖field‖ ^ 2 := by
  let scaled := ((Lp.memLp field).smul_measure (c := jacobian scale) ENNReal.ofReal_ne_top).toLp field
  calc
    _ = ‖scaled‖ ^ 2 := congrArg (fun value : ℝ => value ^ 2)
      ((mapPullback dimension domain measurableDomain scale).norm_map scaled)
    _ = ∫ point, ‖scaled point‖ ^ 2 ∂jacobian scale • volume.restrict domain :=
      Grad.GenericCarriers.lpTwo_norm_sq _ scaled
    _ = ∫ point, ‖field point‖ ^ 2 ∂jacobian scale • volume.restrict domain := by
      apply integral_congr_ae
      filter_upwards [show scaled =ᵐ[jacobian scale • volume.restrict domain] field from MemLp.coeFn_toLp _]
        with point equality
      rw [equality]
    _ = (scale.val ^ 2)⁻¹ * ∫ point in domain, ‖field point‖ ^ 2 := by
      rw [integral_smul_measure, jacobian, ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg scale.val))]
      rfl
    _ = _ := by rw [Grad.GenericCarriers.domainL2_norm_sq]

theorem rawValue_norm (dimension : ℕ) (domain : Set Spatial) (measurableDomain : MeasurableSet domain)
    (scale : Scale) (field : FieldL2 dimension domain) :
    ‖rawValue dimension domain measurableDomain scale field‖ = scale.val⁻¹ * ‖field‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (inv_nonneg.mpr scale.property.1.le) (norm_nonneg _))).mp
  rw [rawValue_norm_sq, mul_pow, inv_pow]

theorem rawValue_add (dimension : ℕ) (domain : Set Spatial) (measurableDomain : MeasurableSet domain)
    (scale : Scale) (first second : FieldL2 dimension domain) :
    rawValue dimension domain measurableDomain scale (first + second) =
      rawValue dimension domain measurableDomain scale first + rawValue dimension domain measurableDomain scale second := by
  apply Lp.ext
  filter_upwards [rawValue_ae dimension domain measurableDomain scale (first + second),
    rawValue_ae dimension domain measurableDomain scale first,
    rawValue_ae dimension domain measurableDomain scale second,
    pull_ae domain measurableDomain scale (Lp.coeFn_add first second),
    Lp.coeFn_add (rawValue dimension domain measurableDomain scale first)
      (rawValue dimension domain measurableDomain scale second)] with point total firstAt secondAt sourceAt targetAt
  rw [total, sourceAt, targetAt, Pi.add_apply, Pi.add_apply, firstAt, secondAt]

theorem rawValue_smul (dimension : ℕ) (domain : Set Spatial) (measurableDomain : MeasurableSet domain)
    (scale : Scale) (scalar : ℂ) (field : FieldL2 dimension domain) :
    rawValue dimension domain measurableDomain scale (scalar • field) =
      scalar • rawValue dimension domain measurableDomain scale field := by
  apply Lp.ext
  filter_upwards [rawValue_ae dimension domain measurableDomain scale (scalar • field),
    rawValue_ae dimension domain measurableDomain scale field,
    pull_ae domain measurableDomain scale (Lp.coeFn_smul scalar field),
    Lp.coeFn_smul scalar (rawValue dimension domain measurableDomain scale field)]
    with point scaledAt fieldAt sourceAt targetAt
  rw [scaledAt, sourceAt, targetAt, Pi.smul_apply, Pi.smul_apply, fieldAt]

def fieldDilation (dimension : ℕ) (domain : Set Spatial) (measurableDomain : MeasurableSet domain)
    (scale : Scale) : FieldL2 dimension domain →L[ℂ] FieldL2 dimension (pullDomain scale domain) :=
  ({ toFun := rawValue dimension domain measurableDomain scale
     map_add' := rawValue_add dimension domain measurableDomain scale
     map_smul' := rawValue_smul dimension domain measurableDomain scale } :
    FieldL2 dimension domain →ₗ[ℂ] FieldL2 dimension (pullDomain scale domain)).mkContinuous scale.val⁻¹
      (fun field => (rawValue_norm dimension domain measurableDomain scale field).le)

theorem fieldDilation_apply (dimension : ℕ) (domain : Set Spatial) (measurableDomain : MeasurableSet domain)
    (scale : Scale) (field : FieldL2 dimension domain) :
    fieldDilation dimension domain measurableDomain scale field = rawValue dimension domain measurableDomain scale field := rfl

theorem fieldDilation_opNorm_le (dimension : ℕ) (domain : Set Spatial)
    (measurableDomain : MeasurableSet domain) (scale : Scale) :
    ‖fieldDilation dimension domain measurableDomain scale‖ ≤ scale.val⁻¹ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.mpr scale.property.1.le)
  intro field
  exact (rawValue_norm dimension domain measurableDomain scale field).le

theorem rawValue_naturality (dimension : ℕ) (domain : Set Spatial) (measurableDomain : MeasurableSet domain)
    (scale : Scale) (mapping : CellValues dimension →L[ℂ] CellValues dimension) (field : FieldL2 dimension domain) :
    rawValue dimension domain measurableDomain scale ((mapping.compLpL 2 (volume.restrict domain)) field) =
      mapping.compLpL 2 (volume.restrict (pullDomain scale domain))
        (rawValue dimension domain measurableDomain scale field) := by
  apply Lp.ext
  filter_upwards [rawValue_ae dimension domain measurableDomain scale
      ((mapping.compLpL 2 (volume.restrict domain)) field),
    pull_ae domain measurableDomain scale (mapping.coeFn_compLpL field),
    mapping.coeFn_compLpL (rawValue dimension domain measurableDomain scale field),
    rawValue_ae dimension domain measurableDomain scale field] with point total sourceAt targetAt fieldAt
  rw [total, sourceAt, targetAt, fieldAt]

theorem rawValue_inverse (dimension : ℕ) (domain : Set Spatial) (measurableDomain : MeasurableSet domain)
    (scale : Scale) (power : ℕ) (field : FieldL2 dimension domain) :
    rawValue dimension domain measurableDomain scale (Grad.CellWeights.inverseFieldCLM dimension domain power field) =
      Grad.CellWeights.inverseFieldCLM dimension (pullDomain scale domain) power
        (rawValue dimension domain measurableDomain scale field) :=
  rawValue_naturality dimension domain measurableDomain scale
    (Grad.CellWeights.inverseCellCLM (PhysicalValue dimension) power) field

theorem field_goal : FieldGoal := by
  intro dimension domain measurableDomain scale
  refine ⟨⟨fieldDilation dimension domain measurableDomain scale, fun _ => rfl,
    fieldDilation_opNorm_le dimension domain measurableDomain scale⟩, ?_,
    rawValue_inverse dimension domain measurableDomain scale⟩
  intro field
  refine ⟨rawValue_norm dimension domain measurableDomain scale field, ?_⟩
  filter_upwards [rawValue_ae dimension domain measurableDomain scale field] with point equality
  intro cell
  rw [equality]

theorem geometry_goal : GeometryGoal := by
  refine ⟨expandedDisk_eq, ?_⟩
  intro radius scale positive strict
  have gap : radius < radius / scale.val := by
    apply (lt_div_iff₀ scale.property.1).mpr
    exact mul_lt_of_lt_one_right positive strict
  refine ⟨by dsimp [diskMargin]; linarith, by dsimp [diskMargin]; ring, ?_⟩
  rw [expandedDisk_eq]
  exact Metric.closedBall_subset_ball gap

end Grad.SpatialDilation
