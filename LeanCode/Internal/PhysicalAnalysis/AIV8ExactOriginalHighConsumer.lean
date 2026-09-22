import AIV7SameInsertedGradeEquivalence

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularOriginalHigh
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularFluxTrace Grad.AnnularOmegaGraph
open Grad.AnnularHighTilt Grad.AnnularGrades Grad.AnnularCrossMaps Grad.SourceCollarDivision

/-- Fixed-radius forward bound has exactly the BF6 radial loss. -/
theorem originalHighTilt_forward_bound (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (field : OriginalHighSpace lower length positive) :
    ‖originalHighTiltEquivalence lower length positive bounded lengthPositive field‖ ≤
      ((12 + 3 * length) * lower ^ (-highTiltExponent)) * ‖field‖ := by
  let output := originalHighTiltEquivalence lower length positive bounded lengthPositive field
  have inputSq := WithLp.prod_norm_sq_eq_of_L2 field
  have outputSq := WithLp.prod_norm_sq_eq_of_L2 output
  change ‖field‖ ^ 2 = ‖field.ofLp.1‖ ^ 2 + ‖field.ofLp.2‖ ^ 2 at inputSq
  change ‖output‖ ^ 2 = ‖output.ofLp.1‖ ^ 2 + ‖output.ofLp.2‖ ^ 2 at outputSq
  have energy : ‖field.ofLp.1‖ ≤ ‖field‖ := by
    nlinarith [norm_nonneg field, norm_nonneg field.ofLp.1, sq_nonneg ‖field.ofLp.2‖]
  have flux : ‖field.ofLp.2‖ ≤ ‖field‖ := by
    nlinarith [norm_nonneg field, norm_nonneg field.ofLp.2, sq_nonneg ‖field.ofLp.1‖]
  have outEnergy : ‖output.ofLp.1‖ ≤ (3 * lower ^ (-highTiltExponent)) * ‖field‖ :=
    (highEnergyWeight_bound lower length positive bounded _).trans
      (mul_le_mul_of_nonneg_left energy (by positivity))
  have outFlux : ‖output.ofLp.2‖ ≤ (3 * (3 + length) * lower ^ (-highTiltExponent)) * ‖field‖ :=
    (originalFluxTilt_forward_bound lower length positive bounded lengthPositive _).trans
      (mul_le_mul_of_nonneg_left flux (by positivity))
  have outSum : ‖output‖ ≤ ‖output.ofLp.1‖ + ‖output.ofLp.2‖ := by
    nlinarith [norm_nonneg output, norm_nonneg output.ofLp.1, norm_nonneg output.ofLp.2,
      mul_nonneg (norm_nonneg output.ofLp.1) (norm_nonneg output.ofLp.2)]
  calc
    _ ≤ ‖output.ofLp.1‖ + ‖output.ofLp.2‖ := outSum
    _ ≤ (3 * lower ^ (-highTiltExponent)) * ‖field‖ +
        (3 * (3 + length) * lower ^ (-highTiltExponent)) * ‖field‖ := add_le_add outEnergy outFlux
    _ = _ := by ring

/-- Pointwise original radial factor on every actual high flux mode. The
same Fourier phase can therefore be decoded on both sides. -/
theorem originalHighTilt_flux_ae (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (lengthPositive : 0 < length)
    (field : OriginalHighSpace lower length positive) (mode : HighAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      (originalHighTiltEquivalence lower length positive bounded lengthPositive field).ofLp.2.val 0 mode radius =
        radius ^ (-highTiltExponent) • field.ofLp.2.val 0 mode radius := by
  change ∀ᵐ radius ∂volume.restrict (Icc lower 1),
    highBulkWeight lower positive bounded (field.ofLp.2.val 0) mode radius = _
  filter_upwards [scalarRadialMap_ae lower (highPowerCurve lower (-highTiltExponent) positive)
    (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded) (field.ofLp.2.val 0 mode),
    ae_restrict_mem measurableSet_Icc] with radius actual inside
  exact actual.trans (by rw [highPowerCurve_physical lower (-highTiltExponent) positive radius inside])

/-- Immediate exact BF6 high consumer: genuine graph equivalence, inverse
laws, sharp radial dependence, and every unchanged inserted grade. -/
theorem originalHighBF6_consumer (lower length : ℝ) (positive : 0 < lower)
    (strict : lower < 1) (lengthPositive : 0 < length) :
    ∃ equivalence : OriginalHighSpace lower length positive ≃L[ℂ]
        CrossHighSpace lower length positive lengthPositive,
      (∀ field, equivalence field = originalHighTiltEquivalence lower length positive strict.le lengthPositive field) ∧
      (∀ field, ‖equivalence field‖ ≤ ((12 + 3 * length) * lower ^ (-highTiltExponent)) * ‖field‖) ∧
      (∀ field, ‖equivalence.symm field‖ ≤ (5 + length⁻¹ + highTiltExponent) * ‖field‖) ∧
      (∀ angular cell inserted (field : OriginalHighSpace lower length positive),
        (HasAnnularEnergyGrade lower length positive angular cell inserted field.ofLp.1 ∧
          HasAnnularFluxGrade lower positive angular cell inserted (originalNuPairEquivalence lower positive field.ofLp.2)) ↔
        (HasAnnularEnergyGrade lower length positive angular cell inserted (equivalence field).ofLp.1 ∧
          HasAnnularOmegaGrade lower angular cell inserted (equivalence field).ofLp.2.val)) := by
  refine ⟨originalHighTiltEquivalence lower length positive strict.le lengthPositive, fun _ => rfl,
    originalHighTilt_forward_bound lower length positive strict.le lengthPositive,
    originalHighTilt_inverse_bound lower length positive strict.le lengthPositive, ?_⟩
  intro angular cell inserted field
  exact and_congr (originalEnergyTilt_grade_iff lower length positive strict angular cell inserted field.ofLp.1)
    (originalFluxTilt_grade_iff lower length positive strict lengthPositive angular cell inserted field.ofLp.2)

end Grad.AnnularOriginalHigh
