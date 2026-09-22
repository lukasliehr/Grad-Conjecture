import AKBG1CovariantPrimitiveTestLaws

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.RepresentedKernel.SpatialProduct

theorem startupCovariantDerivative_contraction (source : Fin 2) (angle scalar : ℝ) (derivative : Fin 2 → ℝ) :
    (∑ target : Fin 2, ∑ coordinate : Fin 2,
      (scalar * startupAverageWeight source target angle * startupInverseRotationEntry target coordinate angle) *
        derivative coordinate) = scalar * derivative source := by
  have circle := Real.sin_sq_add_cos_sq angle
  fin_cases source <;> simp [Fin.sum_univ_two, startupAverageWeight, startupInverseRotationEntry,
    planeRotation, spatialDirection]
  · linear_combination scalar * derivative 0 * circle
  · linear_combination scalar * derivative 1 * circle

/-- Exact covariant compact test identity C grad = grad K. The inverse
spatial covector is retained and contracted with the actual value rotation. -/
theorem startupCovariantAngularTest_divergence (weight : ℝ → ℝ) (weightSmooth : ContDiff ℝ ∞ weight)
    (source : Fin 2) (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (point : Spatial) :
    (∑ target : Fin 2, directionDerivative target
      (startupAngularTest (fun angle => weight angle * startupAverageWeight source target angle) test) point) =
      startupAngularTest weight (directionDerivative source test) point := by
  have rotationContinuous : Continuous (fun angle : ℝ => planeRotationEquiv (-angle) point) := by
    have insertion : ContDiff ℝ ∞ (fun angle : ℝ => (point, angle)) := contDiff_const.prodMk contDiff_id
    simpa only [Function.comp_def] using (startupInverseTestRotation_smooth.comp insertion).continuous
  have rows (target : Fin 2) : IntegrableOn (fun angle : ℝ => ∑ coordinate : Fin 2,
      (weight angle * startupAverageWeight source target angle * startupInverseRotationEntry target coordinate angle) *
        fderiv ℝ test (planeRotationEquiv (-angle) point) (spatialDirection coordinate))
      (Icc (0 : ℝ) (2 * Real.pi)) := by
    apply Continuous.integrableOn_Icc
    apply continuous_finsetSum
    intro coordinate _
    exact ((weightSmooth.continuous.mul (startupAverageWeight_smooth source target).continuous).mul
      (startupInverseRotationEntry_smooth target coordinate).continuous).mul
      (((smooth.continuous_fderiv (by simp)).comp rotationContinuous).clm_apply continuous_const)
  have differentiated (target : Fin 2) := startupAngularTest_derivative_integral
    (fun angle => weight angle * startupAverageWeight source target angle)
    (weightSmooth.mul (startupAverageWeight_smooth source target)) test smooth point target
  change (∑ target : Fin 2, fderiv ℝ
    (startupAngularTest (fun angle => weight angle * startupAverageWeight source target angle) test)
      point (spatialDirection target)) = _
  simp_rw [differentiated]
  rw [← Finset.mul_sum, ← integral_finsetSum _ (fun target _ => rows target)]
  unfold startupAngularTest
  congr 1
  apply integral_congr_ae
  filter_upwards [] with angle
  exact startupCovariantDerivative_contraction source angle (weight angle)
    (fun coordinate => fderiv ℝ test (planeRotationEquiv (-angle) point) (spatialDirection coordinate))

end Grad.CartesianStartup
