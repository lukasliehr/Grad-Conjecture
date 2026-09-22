import AKBL4SameNativeCovariantGauge

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

 theorem startupCharacter_zero_pairing {dimension : ℕ} (field : StartupL2 dimension)
    (cell : ℤ) (coordinate : Fin dimension) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate test (startupCharacterKernel dimension 0 field) =
      startupCoordinateTestPairing cell coordinate (startupMeanTest test) field := by
  rw [startupZeroMean_realDim]
  exact congrArg (fun operator : StartupL2 dimension →L[ℂ] ℂ => operator field)
    (startupCoordinateTestPairing_angular (fun _ : ℝ => 1) contDiff_const cell coordinate test)

 theorem startupMean_rotation_pairing {dimension : ℕ} (field : StartupL2 dimension)
    (cell : ℤ) (coordinate : Fin dimension) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate (startupMeanTest (startupRotationTest test)) field = 0 := by
  rw [startupCoordinateTestPairing_apply]
  change (∫ point in openUnitDisk,
    startupAngularTest (fun _ : ℝ => 1) (startupRotationDerivative test.toFun) point • field point cell coordinate) = 0
  simp only [startupMeanTest_rotation_zero test.toFun test.smooth, zero_smul, integral_zero]

 theorem startupSame_fixedScalar_rotation (field : StartupL2 1) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell 0 (startupRotationTest test) (field - startupCharacterKernel 1 0 field) =
      startupCoordinateTestPairing cell 0 (startupRotationTest test) field := by
  rw [map_sub, startupCharacter_zero_pairing, startupMean_rotation_pairing, sub_zero]

 theorem startupSame_fixedScalar_meanFree (field : StartupL2 1) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell 0 (startupMeanFreeTest test) (field - startupCharacterKernel 1 0 field) =
      startupCoordinateTestPairing cell 0 (startupMeanFreeTest test) field := by
  change startupCoordinateTestPairing cell 0 (startupSubTest test (startupMeanTest test))
    (field - startupCharacterKernel 1 0 field) = _
  rw [startupCoordinateTestPairing_sub, sub_apply]
  rw [map_sub, startupCharacter_zero_pairing, startupSame_fixedScalar_mean]
  change _ = startupCoordinateTestPairing cell 0 (startupSubTest test (startupMeanTest test)) field
  rw [startupCoordinateTestPairing_sub, sub_apply, sub_zero]

/-- The tangential quotient correction has rotationally invariant divergence
as a distribution, before any derivative of the field is represented in L2. -/
 theorem startupTangential_divergence_rotation (field : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakDivergencePairing (originalTangentialKernel field) cell (startupRotationTest test) = 0 := by
  have first := startupTangential_rotation_pairing field cell 0 (startupDerivativeTest 0 test)
  have second := startupTangential_rotation_pairing field cell 1 (startupDerivativeTest 1 test)
  rw [startupRotationDerivativeTest_zero, startupCoordinateTestPairing_sub, sub_apply,
    startupCoordinateTestPairing_quarter] at first
  rw [startupRotationDerivativeTest_one, startupCoordinateTestPairing_add, add_apply,
    startupCoordinateTestPairing_quarter] at second
  unfold startupWeakDivergencePairing
  norm_num at first second ⊢
  linear_combination -first - second

 theorem startupTangential_divergence_meanFree (field : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakDivergencePairing (originalTangentialKernel field) cell (startupMeanFreeTest test) = 0 := by
  have rotation := startupTangential_divergence_rotation field cell (startupTrueInverseTest test)
  rw [startupTrueInverseTest_rotation, startupWeakDivergence_sub_test] at rotation
  change startupWeakDivergencePairing (originalTangentialKernel field) cell (startupMeanTest test) -
    startupWeakDivergencePairing (originalTangentialKernel field) cell test = 0 at rotation
  change startupWeakDivergencePairing (originalTangentialKernel field) cell
    (startupSubTest test (startupMeanTest test)) = 0
  rw [startupWeakDivergence_sub_test]
  linear_combination -rotation

 theorem startupWeakDivergence_sub_field (first second : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakDivergencePairing (first-second) cell test =
      startupWeakDivergencePairing first cell test-startupWeakDivergencePairing second cell test := by
  simp only [startupWeakDivergencePairing,map_sub]
  ring

 theorem startupSame_fixedPlanar_meanFreeDivergence (field : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakDivergencePairing (field-originalTangentialKernel field) cell (startupMeanFreeTest test) =
      startupWeakDivergencePairing field cell (startupMeanFreeTest test) := by
  rw [startupWeakDivergence_sub_field,startupTangential_divergence_meanFree,sub_zero]

/-- Passing the actual third equation to the SAME full fixed quotient removes
only a scalar angular mean, whose rotational derivative is proved zero. -/
 theorem startupSame_fullCircle_third (axial : ℤ → ℂ) (theta source : StartupL2 1) (covariant : StartupL2 3)
    (equation : StartupWeakThirdEquation axial theta (originalValueKernel toroidalPartMap covariant) source) :
    StartupWeakThirdEquation axial theta (originalValueKernel toroidalPartMap (originalCircleKernel covariant)) source := by
  intro cell test
  rw [startupFullCircle_scalar,startupSame_fixedScalar_rotation]
  exact equation cell test

/-- The actual outer P0 determinant row is unchanged by passing from the
physical covariant to its literal full three-component fixed quotient. -/
 theorem startupSame_fullCircle_determinant (axial : ℤ → ℂ) (covariant : StartupL2 3)
    (determinant : StartupL2 1) (planarFlux : StartupL2 2) (scalarFlux : StartupL2 1)
    (equation : StartupWeakDeterminantEquation axial (originalValueKernel planarPartMap covariant)
      (originalValueKernel toroidalPartMap covariant) determinant planarFlux scalarFlux) :
    StartupWeakDeterminantEquation axial (originalValueKernel planarPartMap (originalCircleKernel covariant))
      (originalValueKernel toroidalPartMap (originalCircleKernel covariant)) determinant planarFlux scalarFlux := by
  intro cell test
  rw [startupFullCircle_planar,startupFullCircle_scalar,startupSame_fixedPlanar_meanFreeDivergence,
    startupSame_fixedScalar_meanFree]
  exact equation cell test

end Grad.CartesianStartup
