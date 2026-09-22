import AKAX14ActualLaplacianRotation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.RepresentedKernel.SpatialProduct

theorem startupAngularTest_wordDerivative2 (weight : ℝ → ℝ) (weightSmooth : ContDiff ℝ ∞ weight)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test) (word : Word 2) (point : Spatial) :
    wordDerivative 2 word (startupAngularTest weight test) point =
      (2 * Real.pi)⁻¹ * ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
        wordDerivative 2 word (fun source => weight angle * test (planeRotationEquiv (-angle) source)) point := by
  let integrand : Spatial × ℝ → ℝ := fun argument =>
    weight argument.2 * test (planeRotationEquiv (-argument.2) argument.1)
  have smooth : ContDiff ℝ ∞ integrand :=
    (weightSmooth.comp contDiff_snd).mul (testSmooth.comp startupInverseTestRotation_smooth)
  have integralSmooth : ContDiff ℝ ∞ (fun source => ∫ angle in Icc (0 : ℝ) (2 * Real.pi), integrand (source, angle)) :=
    contDiffOn_univ.mp (contDiffOn_compactIntegral isOpen_univ smooth.contDiffOn 0 (2 * Real.pi))
  change wordDerivative 2 word (fun source => (2 * Real.pi)⁻¹ *
    ∫ angle in Icc (0 : ℝ) (2 * Real.pi), integrand (source, angle)) point = _
  rw [startupWordDerivative_const_mul _ integralSmooth]
  congr 1
  exact cartesianDerivative_compactIntegral 2 word smooth 0 (2 * Real.pi) point

theorem startupWordDerivative2_slice_continuous (integrand : Spatial × ℝ → ℝ)
    (smooth : ContDiff ℝ ∞ integrand) (word : Word 2) (point : Spatial) :
    Continuous (fun angle : ℝ => wordDerivative 2 word (fun source => integrand (source, angle)) point) := by
  have insertion : Continuous (fun angle : ℝ => (point, angle)) := continuous_const.prodMk continuous_id
  have rowContinuous : Continuous (fun angle : ℝ => sliceListDerivative (List.ofFn word) integrand (point, angle)) := by
    simpa only [Function.comp_def] using (sliceListDerivative_smooth (List.ofFn word) smooth).continuous.comp insertion
  apply rowContinuous.congr
  intro angle
  have sectionSmooth : ContDiff ℝ ∞ (fun source => integrand (source, angle)) :=
    smooth.comp (contDiff_id.prodMk contDiff_const)
  exact (congrFun (sliceListDerivative_eq (List.ofFn word) smooth angle) point).trans
    (listDerivative_ofFn isOpen_univ 2 word sectionSmooth.contDiffOn (mem_univ point))

/-- Exact Laplacian commutation for the actual inverse-angle kernel on compact-test functions. -/
theorem startupAngularTest_laplacian (weight : ℝ → ℝ) (weightSmooth : ContDiff ℝ ∞ weight)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test) (point : Spatial) :
    startupWordLaplacian (startupAngularTest weight test) point =
      startupAngularTest weight (startupWordLaplacian test) point := by
  let integrand : Spatial × ℝ → ℝ := fun argument =>
    weight argument.2 * test (planeRotationEquiv (-argument.2) argument.1)
  have smooth : ContDiff ℝ ∞ integrand :=
    (weightSmooth.comp contDiff_snd).mul (testSmooth.comp startupInverseTestRotation_smooth)
  have rows (word : Word 2) : IntegrableOn (fun angle : ℝ =>
      wordDerivative 2 word (fun source => weight angle * test (planeRotationEquiv (-angle) source)) point)
      (Icc (0 : ℝ) (2 * Real.pi)) :=
    (startupWordDerivative2_slice_continuous integrand smooth word point).integrableOn_Icc
  unfold startupWordLaplacian
  rw [startupAngularTest_wordDerivative2 weight weightSmooth test testSmooth,
    startupAngularTest_wordDerivative2 weight weightSmooth test testSmooth, ← mul_add,
    ← integral_add (rows (fun _ => 0)) (rows (fun _ => 1))]
  change (2 * Real.pi)⁻¹ * _ = (2 * Real.pi)⁻¹ * _
  congr 1
  apply integral_congr_ae
  filter_upwards [] with angle
  have rotatedSmooth : ContDiff ℝ ∞ (fun source : Spatial => test (planeRotationEquiv (-angle) source)) := by
    have insertion : ContDiff ℝ ∞ (fun source : Spatial => (source, angle)) :=
      contDiff_id.prodMk contDiff_const
    simpa only [Function.comp_def] using testSmooth.comp (startupInverseTestRotation_smooth.comp insertion)
  rw [startupWordDerivative_const_mul _ rotatedSmooth, startupWordDerivative_const_mul _ rotatedSmooth, ← mul_add]
  exact congrArg (fun value : ℝ => weight angle * value)
    (startupWordLaplacian_rotation (-angle) test point)

end Grad.CartesianStartup
