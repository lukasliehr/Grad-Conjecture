import AIV4UniformOriginalFluxComparison

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalHigh
open Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph Grad.AnnularHighTilt
open Grad.AnnularCrossMaps

/-- Original AK6 high carrier with the literal W and D_h Hilbert norms. -/
abbrev OriginalHighSpace (lower length : ℝ) (positive : 0 < lower) :=
  WithLp 2 ((annularEnergySpace lower length positive) × (originalNuGraph lower positive))

def originalHighTiltEquivalence (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length) :
    OriginalHighSpace lower length positive ≃L[ℂ] CrossHighSpace lower length positive lengthPositive :=
  (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).trans
    (((highEnergyTiltEquivalence lower length positive bounded).prodCongr
      (originalFluxTiltEquivalence lower length positive bounded lengthPositive)).trans
      (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).symm)

theorem originalHighTilt_energy (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (field : OriginalHighSpace lower length positive) :
    (originalHighTiltEquivalence lower length positive bounded lengthPositive field).ofLp.1 =
      highEnergyWeight lower length positive bounded field.ofLp.1 := rfl

theorem originalHighTilt_flux (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (field : OriginalHighSpace lower length positive) :
    (originalHighTiltEquivalence lower length positive bounded lengthPositive field).ofLp.2 =
      originalFluxTiltEquivalence lower length positive bounded lengthPositive field.ofLp.2 := rfl

theorem originalHighTilt_inverse_energy (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (field : CrossHighSpace lower length positive lengthPositive) :
    ((originalHighTiltEquivalence lower length positive bounded lengthPositive).symm field).ofLp.1 =
      highEnergyUnweight lower length positive bounded field.ofLp.1 := rfl

theorem originalHighTilt_inverse_flux (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (field : CrossHighSpace lower length positive lengthPositive) :
    ((originalHighTiltEquivalence lower length positive bounded lengthPositive).symm field).ofLp.2 =
      (originalFluxTiltEquivalence lower length positive bounded lengthPositive).symm field.ofLp.2 := rfl

/-- The BF6 high inverse is uniform even in the ORIGINAL nu derivative norm. -/
theorem originalHighTilt_inverse_bound (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (field : CrossHighSpace lower length positive lengthPositive) :
    ‖(originalHighTiltEquivalence lower length positive bounded lengthPositive).symm field‖ ≤
      (5 + length⁻¹ + highTiltExponent) * ‖field‖ := by
  let output := (originalHighTiltEquivalence lower length positive bounded lengthPositive).symm field
  have inputSq := WithLp.prod_norm_sq_eq_of_L2 field
  have outputSq := WithLp.prod_norm_sq_eq_of_L2 output
  change ‖field‖ ^ 2 = ‖field.ofLp.1‖ ^ 2 + ‖field.ofLp.2‖ ^ 2 at inputSq
  change ‖output‖ ^ 2 = ‖output.ofLp.1‖ ^ 2 + ‖output.ofLp.2‖ ^ 2 at outputSq
  have energy : ‖field.ofLp.1‖ ≤ ‖field‖ := by
    nlinarith [norm_nonneg field, norm_nonneg field.ofLp.1, sq_nonneg ‖field.ofLp.2‖]
  have flux : ‖field.ofLp.2‖ ≤ ‖field‖ := by
    nlinarith [norm_nonneg field, norm_nonneg field.ofLp.2, sq_nonneg ‖field.ofLp.1‖]
  have outEnergy : ‖output.ofLp.1‖ ≤ 3 * ‖field‖ :=
    (highEnergyUnweight_bound lower length positive bounded _).trans
      (mul_le_mul_of_nonneg_left energy (by norm_num))
  have outFlux : ‖output.ofLp.2‖ ≤ (2 + length⁻¹ + highTiltExponent) * ‖field‖ :=
    (originalFluxTilt_inverse_bound lower length positive bounded lengthPositive _).trans
      (mul_le_mul_of_nonneg_left flux (by have := highTiltExponent_pos; positivity))
  have outSum : ‖output‖ ≤ ‖output.ofLp.1‖ + ‖output.ofLp.2‖ := by
    nlinarith [norm_nonneg output, norm_nonneg output.ofLp.1, norm_nonneg output.ofLp.2,
      mul_nonneg (norm_nonneg output.ofLp.1) (norm_nonneg output.ofLp.2)]
  calc
    _ ≤ ‖output.ofLp.1‖ + ‖output.ofLp.2‖ := outSum
    _ ≤ 3 * ‖field‖ + (2 + length⁻¹ + highTiltExponent) * ‖field‖ := add_le_add outEnergy outFlux
    _ = _ := by ring

end Grad.AnnularOriginalHigh
