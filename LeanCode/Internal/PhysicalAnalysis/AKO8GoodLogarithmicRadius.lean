import AKO6SameLowMovingIncomingTrace
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ENNReal Topology
namespace Grad.AnnularIncomingIntegrability

private theorem inverseSquareComparison (radius eta value : ℝ) (radiusPositive : 0 < radius)
    (etaPositive : 0 < eta) (bound : eta ≤ value) :
    radius⁻¹ ≤ (eta ^ 2)⁻¹ * (radius⁻¹ * value ^ 2) := by
  have squares : eta ^ 2 ≤ value ^ 2 := (sq_le_sq₀ etaPositive.le (etaPositive.le.trans bound)).mpr bound
  calc
    radius⁻¹ = ((eta ^ 2)⁻¹ * radius⁻¹) * eta ^ 2 := by
      rw [mul_right_comm,inv_mul_cancel₀ (sq_pos_of_pos etaPositive).ne',one_mul]
    _ ≤ ((eta ^ 2)⁻¹ * radius⁻¹) * value ^ 2 :=
      mul_le_mul_of_nonneg_left squares (mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (inv_nonneg.mpr radiusPositive.le))
    _ = _ := by ring

/-- Finite logarithmic square integral supplies arbitrarily small genuine
trace radii, avoiding any prescribed Lebesgue-null exceptional set. -/
theorem exists_good_logarithmic_radius (upper : ℝ) (_upperPositive : 0 < upper)
    (incoming : ℝ → ℝ) (measurable : Measurable incoming)
    (finite : (∫⁻ radius, ENNReal.ofReal (radius⁻¹ * incoming radius ^ 2)
      ∂volume.restrict (Ioc 0 upper)) < ⊤)
    (exceptional : Set ℝ) (null : volume exceptional = 0)
    (delta eta : ℝ) (deltaPositive : 0 < delta) (deltaUpper : delta ≤ upper) (etaPositive : 0 < eta) :
    ∃ radius : ℝ, 0 < radius ∧ radius < delta ∧ radius ∉ exceptional ∧ incoming radius < eta := by
  by_contra absent
  have avoid : ∀ᵐ radius ∂volume, radius ∉ exceptional := by
    apply ae_iff.mpr
    simpa only [not_not,Set.ofPred_mem_eq] using null
  have integrable : IntegrableOn (fun radius : ℝ => radius⁻¹ * incoming radius ^ 2) (Ioc 0 upper) := by
    refine ⟨(measurable_inv.mul (measurable.pow_const 2)).aestronglyMeasurable,?_⟩
    apply (hasFiniteIntegral_iff_ofReal ?_).mpr finite
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius inside
    exact mul_nonneg (inv_nonneg.mpr inside.1.le) (sq_nonneg _)
  have restricted : IntegrableOn (fun radius : ℝ => radius⁻¹ * incoming radius ^ 2) (Ioo 0 delta) :=
    integrable.mono_set (fun _ inside => ⟨inside.1,inside.2.le.trans deltaUpper⟩)
  have inverseIntegrable : IntegrableOn (fun radius : ℝ => radius⁻¹) (Ioo 0 delta) := by
    apply (restricted.const_mul (eta ^ 2)⁻¹).mono' measurable_inv.aestronglyMeasurable
    filter_upwards [ae_restrict_of_ae avoid,ae_restrict_mem measurableSet_Ioo] with radius outside inside
    have bound : eta ≤ incoming radius := by
      by_contra failure
      exact absent ⟨radius,inside.1,inside.2,outside,lt_of_not_ge failure⟩
    rw [Real.norm_eq_abs,abs_of_pos (inv_pos.mpr inside.1)]
    exact inverseSquareComparison radius eta (incoming radius) inside.1 etaPositive bound
  have impossible := (intervalIntegral.integrableOn_Ioo_rpow_iff (s := (-1 : ℝ)) deltaPositive).mp
    (by simpa only [Real.rpow_neg_one] using inverseIntegrable)
  norm_num at impossible

end Grad.AnnularIncomingIntegrability
