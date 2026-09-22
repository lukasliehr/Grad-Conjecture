import AKAY35ActualRoughEquivariantAverage

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.RepresentedKernel Grad.RepresentedKernel.WeakDerivatives

theorem startupAngularKernel_testFubiniDim (dimension : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (field : StartupL2 dimension) (cell : ℤ) (vector : PhysicalValue dimension)
    (test : Spatial → ℝ) (testMeasurable : Measurable test)
    (testLp : MemLp test 2 (volume.restrict openUnitDisk)) :
    (∫ point in openUnitDisk, test point • inner ℂ vector
      (fieldCellProjection dimension openUnitDisk cell (startupAngularKernel dimension weight smooth field) point)) =
      ∫ angle in Icc (0 : ℝ) (2 * Real.pi), ∫ point in openUnitDisk,
        test point • inner ℂ vector
          (startupAngularCoefficient dimension weight angle (field (planeRotationEquiv angle point) cell)) := by
  have fubini := coefficientCell_pairing_fubini (startupAngularRawDataDim dimension weight smooth)
    cell cell field test testMeasurable testLp vector
  simp only [startupAngularRawDataDim, startupFixedRawData, startupFixedKernelData, if_true] at fubini
  change (∫ point in openUnitDisk, test point • inner ℂ vector
    (∫ angle in Icc (0 : ℝ) (2 * Real.pi),
      startupAngularCoefficient dimension weight angle (field (planeRotationEquiv angle point) cell))) = _ at fubini
  apply Eq.trans _ fubini
  apply integral_congr_ae
  filter_upwards [Grad.FullCellKernel.entry_field_ae (startupAngularKernelData dimension weight smooth)
    field cell cell] with point represented
  rw [startupAngularKernel_coordinate]
  simp only [startupAngularKernelData, startupFixedKernelData, if_true] at represented
  change _ = ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
    startupAngularCoefficient dimension weight angle (field (planeRotationEquiv angle point) cell) at represented
  exact congrArg (fun value : PhysicalValue dimension => test point • inner ℂ vector value) represented


theorem startupRealAngularCoefficient_pairingDim (dimension : ℕ) (weight : ℝ → ℝ) (angle scalar : ℝ)
    (vector value : PhysicalValue dimension) :
    scalar • inner ℂ vector (startupAngularCoefficient dimension (fun theta => (weight theta : ℂ)) angle value) =
      ((2 * Real.pi)⁻¹ * (weight angle * scalar)) • inner ℂ vector value := by
  have coefficient : startupAngularCoefficient dimension (fun theta => (weight theta : ℂ)) angle value =
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

theorem startupAngular_pairing_changeVariablesDim (dimension : ℕ) (weight : ℝ → ℂ) (angle : ℝ)
    (field : StartupL2 dimension) (cell : ℤ) (vector : PhysicalValue dimension) (test : Spatial → ℝ) :
    (∫ point in openUnitDisk, test point • inner ℂ vector
      (startupAngularCoefficient dimension weight angle (field (planeRotationEquiv angle point) cell))) =
      ∫ point in openUnitDisk, test (planeRotationEquiv (-angle) point) • inner ℂ vector
        (startupAngularCoefficient dimension weight angle (field point cell)) := by
  have changed := (startupRotation_disk_preserving angle).integral_comp
    (planeRotationEquiv angle).toHomeomorph.measurableEmbedding
    (fun point : Spatial => test ((planeRotationEquiv angle).symm point) • inner ℂ vector
      (startupAngularCoefficient dimension weight angle (field point cell)))
  have inverse (point : Spatial) : (planeRotationEquiv angle).symm point =
      planeRotationEquiv (-angle) point := rfl
  simpa only [inverse, planeRotationEquiv_apply, planeRotation_neg_left] using changed


theorem startupAngular_transposed_integrableDim (dimension : ℕ) (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight)
    (field : StartupL2 dimension) (cell : ℤ) (vector : PhysicalValue dimension)
    (test : Spatial → ℝ) (testMeasurable : Measurable test)
    (testLp : MemLp test 2 (volume.restrict openUnitDisk)) :
    Integrable (fun pair : ℝ × Spatial => test (planeRotationEquiv (-pair.1) pair.2) •
      inner ℂ vector (startupAngularCoefficient dimension weight pair.1 (field pair.2 cell)))
      ((volume.restrict (Icc (0 : ℝ) (2 * Real.pi))).prod (volume.restrict openUnitDisk)) := by
  have original := testedCell_integrable (startupAngularRawDataDim dimension weight smooth)
    cell cell field test testMeasurable testLp vector
  simp only [startupAngularRawDataDim, startupFixedRawData, startupFixedKernelData, if_true] at original
  have transformed := (startupInverseRotationProduct_preserving.integrable_comp
    original.aestronglyMeasurable).mpr original
  simpa only [Function.comp_def, planeRotationEquiv_apply, planeRotation_neg_right] using transformed


theorem startupRealAngularKernel_transposeDim (dimension : ℕ) (weight : ℝ → ℝ) (smooth : ContDiff ℝ ∞ weight)
    (field : StartupL2 dimension) (cell : ℤ) (vector : PhysicalValue dimension)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) :
    (∫ point in openUnitDisk, test point • inner ℂ vector
      ((startupAngularKernel dimension (fun angle => (weight angle : ℂ)) (Complex.ofRealCLM.contDiff.comp smooth) field) point cell)) =
      ∫ point in openUnitDisk, startupAngularTest weight test point • inner ℂ vector (field point cell) := by
  have testLp : MemLp test 2 (volume.restrict openUnitDisk) :=
    testSmooth.continuous.memLp_of_hasCompactSupport compact
  have fubini := startupAngularKernel_testFubiniDim dimension (fun angle => (weight angle : ℂ))
    (Complex.ofRealCLM.contDiff.comp smooth) field cell vector test testSmooth.continuous.measurable testLp
  have transposeIntegrable := startupAngular_transposed_integrableDim dimension (fun angle => (weight angle : ℂ))
    (Complex.ofRealCLM.contDiff.comp smooth) field cell vector test testSmooth.continuous.measurable testLp
  calc
    _ = ∫ point in openUnitDisk, test point • inner ℂ vector
        (fieldCellProjection dimension openUnitDisk cell (startupAngularKernel dimension (fun angle => (weight angle : ℂ)) (Complex.ofRealCLM.contDiff.comp smooth) field) point) := by
      apply integral_congr_ae
      filter_upwards [fieldCellProjection_ae dimension openUnitDisk (startupAngularKernel dimension (fun angle => (weight angle : ℂ)) (Complex.ofRealCLM.contDiff.comp smooth) field)] with point same
      rw [same cell]
    _ = _ := fubini
    _ = ∫ angle in Icc (0 : ℝ) (2 * Real.pi), ∫ point in openUnitDisk,
        test (planeRotationEquiv (-angle) point) • inner ℂ vector
          (startupAngularCoefficient dimension (fun theta => (weight theta : ℂ)) angle (field point cell)) := by
      apply integral_congr_ae
      filter_upwards [] with angle
      exact startupAngular_pairing_changeVariablesDim dimension _ angle field cell vector test
    _ = ∫ point in openUnitDisk, ∫ angle in Icc (0 : ℝ) (2 * Real.pi),
        test (planeRotationEquiv (-angle) point) • inner ℂ vector
          (startupAngularCoefficient dimension (fun theta => (weight theta : ℂ)) angle (field point cell)) :=
      integral_integral_swap transposeIntegrable
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with point
      simp_rw [startupRealAngularCoefficient_pairingDim dimension]
      rw [integral_smul_const, integral_const_mul]
      rfl


end Grad.CartesianStartup
