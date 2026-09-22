import AKAX2AngularTransposeMeasure

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- Real angular weights include the literal unshifted primitive and every inverse covector. -/
def startupRealAngularKernel (weight : ℝ → ℝ) (smooth : ContDiff ℝ ∞ weight) :
    StartupL2 3 →L[ℂ] StartupL2 3 :=
  startupAngularKernel 3 (fun angle => (weight angle : ℂ)) (Complex.ofRealCLM.contDiff.comp smooth)

theorem startupRealAngularCoefficient_pairing (weight : ℝ → ℝ) (angle scalar : ℝ)
    (vector value : PhysicalValue 3) :
    scalar • inner ℂ vector (startupAngularCoefficient 3 (fun theta => (weight theta : ℂ)) angle value) =
      ((2 * Real.pi)⁻¹ * (weight angle * scalar)) • inner ℂ vector value := by
  have coefficient : startupAngularCoefficient 3 (fun theta => (weight theta : ℂ)) angle value =
      ((2 * Real.pi)⁻¹ * weight angle) • value := by
    change (((2 * Real.pi)⁻¹ : ℝ) : ℂ) • ((weight angle : ℂ) • value) = _
    rw [Complex.coe_smul, Complex.coe_smul, smul_smul]
  have linear := (innerSL ℂ vector).toLinearMap.map_smul_of_tower
    ((2 * Real.pi)⁻¹ * weight angle) value
  change inner ℂ vector (((2 * Real.pi)⁻¹ * weight angle) • value) =
    ((2 * Real.pi)⁻¹ * weight angle) • inner ℂ vector value at linear
  rw [coefficient, linear, smul_smul]
  congr 1
  ring

theorem startupAngular_pairing_changeVariables (weight : ℝ → ℂ) (angle : ℝ)
    (field : StartupL2 3) (cell : ℤ) (vector : PhysicalValue 3) (test : Spatial → ℝ) :
    (∫ point in openUnitDisk, test point • inner ℂ vector
      (startupAngularCoefficient 3 weight angle (field (planeRotationEquiv angle point) cell))) =
      ∫ point in openUnitDisk, test (planeRotationEquiv (-angle) point) • inner ℂ vector
        (startupAngularCoefficient 3 weight angle (field point cell)) := by
  have changed := (startupRotation_disk_preserving angle).integral_comp
    (planeRotationEquiv angle).toHomeomorph.measurableEmbedding
    (fun point : Spatial => test ((planeRotationEquiv angle).symm point) • inner ℂ vector
      (startupAngularCoefficient 3 weight angle (field point cell)))
  have inverse (point : Spatial) : (planeRotationEquiv angle).symm point =
      planeRotationEquiv (-angle) point := rfl
  simpa only [inverse, planeRotationEquiv_apply, planeRotation_neg_left] using changed

/-- Exact transpose on the SAME all-cell L2 carrier and the original compact test.
 The inverse spatial rotation and the 1/(2pi) normalization are literal. -/
theorem startupRealAngularKernel_transpose (weight : ℝ → ℝ) (smooth : ContDiff ℝ ∞ weight)
    (field : StartupL2 3) (cell : ℤ) (vector : PhysicalValue 3)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    (∫ point in openUnitDisk, test point • inner ℂ vector
      ((startupRealAngularKernel weight smooth field) point cell)) =
      ∫ point in openUnitDisk, startupAngularTest weight test point • inner ℂ vector (field point cell) := by
  have testLp : MemLp test 2 (volume.restrict openUnitDisk) :=
    testSmooth.continuous.memLp_of_hasCompactSupport compact
  have fubini := startupAngularKernel_testFubini (fun angle => (weight angle : ℂ))
    (Complex.ofRealCLM.contDiff.comp smooth) field cell vector test testSmooth.continuous.measurable testLp
  have transposeIntegrable := startupAngular_transposed_integrable (fun angle => (weight angle : ℂ))
    (Complex.ofRealCLM.contDiff.comp smooth) field cell vector test testSmooth.continuous.measurable testLp
  calc
    _ = ∫ point in openUnitDisk, test point • inner ℂ vector
        (fieldCellProjection 3 openUnitDisk cell (startupRealAngularKernel weight smooth field) point) := by
      apply integral_congr_ae
      filter_upwards [fieldCellProjection_ae 3 openUnitDisk (startupRealAngularKernel weight smooth field)] with point same
      rw [same cell]
    _ = _ := fubini
    _ = ∫ angle in Icc (0 : ℝ) (2 * Real.pi), ∫ point in openUnitDisk,
        test (planeRotationEquiv (-angle) point) • inner ℂ vector
          (startupAngularCoefficient 3 (fun theta => (weight theta : ℂ)) angle (field point cell)) := by
      apply integral_congr_ae
      filter_upwards [] with angle
      exact startupAngular_pairing_changeVariables _ angle field cell vector test
    _ = ∫ point in openUnitDisk, ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
        test (planeRotationEquiv (-angle) point) • inner ℂ vector
          (startupAngularCoefficient 3 (fun theta => (weight theta : ℂ)) angle (field point cell)) :=
      integral_integral_swap transposeIntegrable
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with point
      simp_rw [startupRealAngularCoefficient_pairing]
      rw [integral_smul_const, integral_const_mul]
      rfl

end Grad.CartesianStartup
