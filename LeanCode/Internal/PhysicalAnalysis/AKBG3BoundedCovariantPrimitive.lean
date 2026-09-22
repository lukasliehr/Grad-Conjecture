import AKBG2CovariantPrimitiveGradientTest

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger

def startupRealAngularKernelDim (dimension : ℕ) (weight : ℝ → ℝ) (smooth : ContDiff ℝ ∞ weight) :
    StartupL2 dimension →L[ℂ] StartupL2 dimension :=
  startupAngularKernel dimension (fun angle => (weight angle : ℂ)) (Complex.ofRealCLM.contDiff.comp smooth)

/-- Raw covariant primitive/average, with literal O(-angle) value rotation.
A scalar angular weight is sufficient; no shifted inverse is assumed. -/
def startupCovariantAngularKernel (weight : ℝ → ℝ) (smooth : ContDiff ℝ ∞ weight) :
    StartupL2 2 →L[ℂ] StartupL2 2 :=
  startupRealAngularKernelDim 2 (fun angle => weight angle * Real.cos angle) (smooth.mul Real.contDiff_cos) -
    (originalValueKernel quarterValueMap).comp
      (startupRealAngularKernelDim 2 (fun angle => weight angle * Real.sin angle) (smooth.mul Real.contDiff_sin))

def startupCovariantPrimitiveKernel : StartupL2 2 →L[ℂ] StartupL2 2 :=
  startupCovariantAngularKernel (fun angle : ℝ => angle) contDiff_id

def startupCovariantAngularTest (weight : ℝ → ℝ) (source target : Fin 2) (test : Spatial → ℝ) : Spatial → ℝ :=
  startupAngularTest (fun angle => weight angle * startupAverageWeight source target angle) test

theorem startupCovariantAngularTest_matrix (weight : ℝ → ℝ) (source target : Fin 2)
    (test : Spatial → ℝ) (point : Spatial) :
    startupCovariantAngularTest weight source target test point =
      if source = target then startupAngularTest (fun angle => weight angle * Real.cos angle) test point
      else if source = 0 then startupAngularTest (fun angle => weight angle * Real.sin angle) test point
      else -startupAngularTest (fun angle => weight angle * Real.sin angle) test point := by
  fin_cases source <;> fin_cases target <;>
    simp [startupCovariantAngularTest, startupAverageWeight, startupInverseRotationEntry,
      planeRotation, spatialDirection, startupAngularTest, mul_neg, neg_mul, integral_neg]

theorem startupQuarterKernel_pairing (field : StartupL2 2) (cell : ℤ) (source : Fin 2) (test : Spatial → ℝ) :
    (∫ point in openUnitDisk, test point • (originalValueKernel quarterValueMap field) point cell source) =
      if source = 0 then -(∫ point in openUnitDisk, test point • field point cell 1)
      else ∫ point in openUnitDisk, test point • field point cell 0 := by
  have actual : (∫ point in openUnitDisk, test point • (originalValueKernel quarterValueMap field) point cell source) =
      ∫ point in openUnitDisk, test point • quarterValueMap (field point cell) source := by
    apply integral_congr_ae
    filter_upwards [startupPointKernel_field_ae quarterValueMap (LinearIsometryEquiv.refl ℝ _) field] with point same
    change ∀ cell : ℤ, (originalValueKernel quarterValueMap field) point cell = quarterValueMap (field point cell) at same
    rw [same cell]
  rw [actual]
  fin_cases source <;> simp [quarterValueMap, quarterValueLinear, smul_neg, integral_neg]

theorem startupCovariantAngularKernel_transpose (weight : ℝ → ℝ) (weightSmooth : ContDiff ℝ ∞ weight)
    (field : StartupL2 2) (cell : ℤ) (source : Fin 2)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    (∫ point in openUnitDisk, test point • (startupCovariantAngularKernel weight weightSmooth field) point cell source) =
      ∑ target : Fin 2, ∫ point in openUnitDisk,
        startupCovariantAngularTest weight source target test point • field point cell target := by
  let functional := Grad.WeakTesting.compactPairing 2 openUnitDisk cell
    (EuclideanSpace.single source 1) test smooth compact
  have actual (value : StartupL2 2) : functional value =
      ∫ point in openUnitDisk, test point • value point cell source := by
    simpa only [EuclideanSpace.inner_single_left, map_one, one_mul] using
      Grad.WeakTesting.compactPairing_apply 2 openUnitDisk cell (EuclideanSpace.single source 1) test smooth compact value
  have cosine (coordinate : Fin 2) := startupRealAngularKernel_transposeDim 2
    (fun angle => weight angle * Real.cos angle) (weightSmooth.mul Real.contDiff_cos)
    field cell (EuclideanSpace.single coordinate 1) test smooth compact
  have sine (coordinate : Fin 2) := startupRealAngularKernel_transposeDim 2
    (fun angle => weight angle * Real.sin angle) (weightSmooth.mul Real.contDiff_sin)
    field cell (EuclideanSpace.single coordinate 1) test smooth compact
  simp only [EuclideanSpace.inner_single_left, map_one, one_mul] at cosine sine
  rw [← actual]
  change functional (startupRealAngularKernelDim 2 (fun angle => weight angle * Real.cos angle) (weightSmooth.mul Real.contDiff_cos) field -
    originalValueKernel quarterValueMap
      (startupRealAngularKernelDim 2 (fun angle => weight angle * Real.sin angle) (weightSmooth.mul Real.contDiff_sin) field)) = _
  rw [map_sub, actual, actual, startupQuarterKernel_pairing]
  change (∫ point in openUnitDisk, test point •
    (startupAngularKernel 2 (fun angle => ((weight angle * Real.cos angle : ℝ) : ℂ))
      (Complex.ofRealCLM.contDiff.comp (weightSmooth.mul Real.contDiff_cos)) field) point cell source) - _ = _
  have sineDimension (coordinate : Fin 2) :
      (∫ point in openUnitDisk, test point •
        (startupRealAngularKernelDim 2 (fun angle => weight angle * Real.sin angle)
          (weightSmooth.mul Real.contDiff_sin) field) point cell coordinate) =
        ∫ point in openUnitDisk, startupAngularTest (fun angle => weight angle * Real.sin angle) test point •
          field point cell coordinate := by
    change (∫ point in openUnitDisk, test point •
      (startupAngularKernel 2 (fun angle => ((weight angle * Real.sin angle : ℝ) : ℂ))
        (Complex.ofRealCLM.contDiff.comp (weightSmooth.mul Real.contDiff_sin)) field) point cell coordinate) = _
    exact sine coordinate
  rw [cosine source, sineDimension 0, sineDimension 1]
  fin_cases source
  · simp only [Fin.sum_univ_two, startupCovariantAngularTest_matrix]
    norm_num
  · simp only [Fin.sum_univ_two, startupCovariantAngularTest_matrix]
    norm_num
    rw [integral_neg]
    ring


end Grad.CartesianStartup
