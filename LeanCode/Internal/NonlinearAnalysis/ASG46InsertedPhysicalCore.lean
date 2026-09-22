import ASG45SourceRotationTrace

noncomputable section
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction Grad.PhaseAlgebra

theorem totalNormalizeCore_eq_phaseCore (parameters : PhaseParameters) (dimension angular cell grade : ℕ)
    (mode : ℤ × ℤ) (core : SmoothRadialCore dimension) :
    totalNormalizeCore parameters dimension angular cell grade mode core =
      sourceInsertedWeight angular cell grade mode • phaseConjugatedCore parameters mode core := by
  rw [totalNormalizeCore, LinearMap.smul_apply, annularNormalizeCore_eq_phaseCore, smul_smul]
  rfl

theorem totalConjugatedMode_core (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell grade : ℕ)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) (mode : ℤ × ℤ) :
    totalConjugatedMode parameters dimension lower positive bounded angular cell grade
      (physicalTotalSourceCore parameters dimension lower angular cell grade core) mode =
      collarH1Core (ComplexEuclidean dimension) lower (phaseConjugatedCore parameters mode (core mode)).val := by
  unfold totalConjugatedMode
  rw [physicalTotalSourceCore_apply, weightedToOrdinary_core, totalNormalizeCore_eq_phaseCore]
  change (sourceInsertedWeight angular cell grade mode)⁻¹ •
    collarH1Core (ComplexEuclidean dimension) lower
      (sourceInsertedWeight angular cell grade mode • (phaseConjugatedCore parameters mode (core mode)).val) = _
  rw [map_smul, smul_smul, inv_mul_cancel₀ (sourceInsertedWeight_pos angular cell grade mode).ne', one_smul]

theorem totalSourceCoefficient_core (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell grade : ℕ)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) (mode : ℤ × ℤ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      totalSourceCoefficient parameters dimension lower positive bounded angular cell grade
        (physicalTotalSourceCore parameters dimension lower angular cell grade core) mode radius =
      (core mode).val.val.1 radius := by
  unfold totalSourceCoefficient totalConjugatedCoordinate
  rw [totalConjugatedMode_core, collarH1Coordinate_core_zero]
  filter_upwards [(collarContinuous_memLp (ComplexEuclidean dimension) lower
    (phaseConjugatedCore parameters mode (core mode)).val.val.1).coeFn_toLp] with radius representative
  change collarContinuousL2 (ComplexEuclidean dimension) lower
    (phaseConjugatedCore parameters mode (core mode)).val.val.1 radius = _ at representative
  rw [representative]
  change (Real.exp (radialPhase parameters radius mode.2))⁻¹ •
    (Real.exp (radialPhase parameters radius mode.2) • (core mode).val.val.1 radius) = _
  rw [smul_smul, inv_mul_cancel₀ (Real.exp_pos _).ne', one_smul]

theorem totalNormalizedRadialCore_norm_sq (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell grade : ℕ)
    (mode : ℤ × ℤ) (core : SmoothRadialCore dimension) :
    ‖weightedRadialCoreInto dimension lower
      (totalNormalizeCore parameters dimension angular cell grade mode core)‖ ^ 2 =
      sourceInsertedWeight angular cell grade mode ^ 2 *
        (∫ radius in lower..1, radius *
          (‖phaseConjugatedCurve parameters mode core radius‖ ^ 2 +
           ‖deriv (phaseConjugatedCurve parameters mode core) radius‖ ^ 2)) := by
  rw [totalNormalizeCore, LinearMap.smul_apply, map_smul, norm_smul,
    Real.norm_of_nonneg (pow_pos (annularFrequency_pos mode) grade).le, mul_pow,
    normalizedRadialCore_norm_sq parameters dimension lower positive bounded]
  rw [sourceInsertedWeight, mul_pow]
  ring

theorem physicalTotalSourceCore_norm_sq (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell grade : ℕ)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) :
    ‖physicalTotalSourceCore parameters dimension lower angular cell grade core‖ ^ 2 =
      ∑' mode : ℤ × ℤ, sourceInsertedWeight angular cell grade mode ^ 2 *
        (∫ radius in lower..1, radius *
          (‖phaseConjugatedCurve parameters mode (core mode) radius‖ ^ 2 +
           ‖deriv (phaseConjugatedCurve parameters mode (core mode)) radius‖ ^ 2)) := by
  have formula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (physicalTotalSourceCore parameters dimension lower angular cell grade core)
  norm_num at formula
  rw [formula]
  apply tsum_congr
  intro mode
  rw [physicalTotalSourceCore_apply]
  exact totalNormalizedRadialCore_norm_sq parameters dimension lower positive bounded angular cell grade mode (core mode)

end Grad.AnnularSourceGraph
