import ASG7FourierTraceOperators
import ASG8OriginalPhaseNormalization

noncomputable section

set_option maxHeartbeats 800000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularSourceGraph

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.BoundaryKernelAction Grad.PhaseAlgebra

def finiteRadialModeMap (dimension : ℕ)
    (family : (ℤ × ℤ) → SmoothRadialCore dimension →ₗ[ℝ] SmoothRadialCore dimension) :
    ((ℤ × ℤ) →₀ SmoothRadialCore dimension) →ₗ[ℝ] ((ℤ × ℤ) →₀ SmoothRadialCore dimension) :=
  Finsupp.lsum ℝ (fun mode => (Finsupp.lsingle mode).comp (family mode))

theorem finiteRadialModeMap_apply (dimension : ℕ)
    (family : (ℤ × ℤ) → SmoothRadialCore dimension →ₗ[ℝ] SmoothRadialCore dimension)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) (mode : ℤ × ℤ) :
    finiteRadialModeMap dimension family core mode = family mode (core mode) := by
  classical
  rw [finiteRadialModeMap, Finsupp.lsum_apply, Finsupp.sum, Finsupp.finsetSum_apply]
  simp only [LinearMap.comp_apply, Finsupp.lsingle_apply, Finsupp.single_apply]
  rw [Finset.sum_eq_single mode]
  · simp only [ite_true]
  · intro other _ different
    exact if_neg different
  · intro missing
    rw [Finsupp.notMem_support_iff.mp missing, map_zero]
    simp

/-- Actual physical finite Fourier smooth radial sources, normalized by
exactly e^(Phi_n) and the two prescribed polynomial grades. -/
def physicalSourceCore (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ) (angular cell : ℕ) :
    ((ℤ × ℤ) →₀ SmoothRadialCore dimension) →ₗ[ℝ] AnnularSourceH1 parameters dimension lower angular cell :=
  (finiteSourceCore parameters dimension lower angular cell).comp
    (finiteRadialModeMap dimension (annularNormalizeCore parameters dimension angular cell))

theorem physicalSourceCore_apply (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (angular cell : ℕ) (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) (mode : ℤ × ℤ) :
    physicalSourceCore parameters dimension lower angular cell core mode =
      weightedRadialCoreInto dimension lower (annularNormalizeCore parameters dimension angular cell mode (core mode)) := by
  rw [physicalSourceCore, LinearMap.comp_apply, finiteSourceCore_apply, finiteRadialModeMap_apply]

theorem physicalSourceCore_denseRange (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (angular cell : ℕ) : DenseRange (physicalSourceCore parameters dimension lower angular cell) := by
  apply (finiteSourceCore_denseRange parameters dimension lower angular cell).mono
  rintro _ ⟨core, rfl⟩
  refine ⟨finiteRadialModeMap dimension (annularDenormalizeCore parameters dimension angular cell) core, ?_⟩
  unfold physicalSourceCore
  rw [LinearMap.comp_apply]
  congr 1
  apply Finsupp.ext
  intro mode
  rw [finiteRadialModeMap_apply, finiteRadialModeMap_apply, annularNormalizeCore_right]

theorem normalizedRadialCore_norm_sq (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)
    (mode : ℤ × ℤ) (core : SmoothRadialCore dimension) :
    ‖weightedRadialCoreInto dimension lower
      (annularNormalizeCore parameters dimension angular cell mode core)‖ ^ 2 =
      splitTangentialWeight angular cell mode ^ 2 *
        (∫ radius in lower..1, radius *
          (‖phaseConjugatedCurve parameters mode core radius‖ ^ 2 +
            ‖deriv (phaseConjugatedCurve parameters mode core) radius‖ ^ 2)) := by
  rw [weightedRadialCore_norm_sq dimension lower positive bounded]
  simp only [annularNormalizeCore_value, annularNormalizeCore_slope, norm_smul,
    Real.norm_of_nonneg (splitTangentialWeight_pos angular cell mode).le, mul_pow]
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro radius _
  ring

/-- AH10 on the literal physical smooth core: original curved phase,
product polynomial weights, r dr, and derivative of the conjugated field. -/
theorem physicalSourceCore_norm_sq (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)
    (core : (ℤ × ℤ) →₀ SmoothRadialCore dimension) :
    ‖physicalSourceCore parameters dimension lower angular cell core‖ ^ 2 =
      ∑' mode : ℤ × ℤ, splitTangentialWeight angular cell mode ^ 2 *
        (∫ radius in lower..1, radius *
          (‖phaseConjugatedCurve parameters mode (core mode) radius‖ ^ 2 +
            ‖deriv (phaseConjugatedCurve parameters mode (core mode)) radius‖ ^ 2)) := by
  have formula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (physicalSourceCore parameters dimension lower angular cell core)
  norm_num at formula
  rw [formula]
  apply tsum_congr
  intro mode
  rw [physicalSourceCore_apply]
  exact normalizedRadialCore_norm_sq parameters dimension lower positive bounded angular cell mode (core mode)

end Grad.AnnularSourceGraph
