import AKBG10SameWeakGradientRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets Grad.ActualAngularInverse

/-- The exact scalar inverse in every value dimension, with its mean subtraction. -/
theorem startupTrueAngularInverse_realDim (dimension : ℕ) :
    startupTrueAngularInverse dimension 0 =
      (startupRealAngularKernelDim dimension (fun angle : ℝ => angle) contDiff_id).comp
        (ContinuousLinearMap.id ℂ _ - startupRealAngularKernelDim dimension (fun _ : ℝ => 1) contDiff_const) := by
  have primitive : startupPrimitiveKernel dimension 0 =
      startupRealAngularKernelDim dimension (fun angle : ℝ => angle) contDiff_id := by
    unfold startupPrimitiveKernel startupRealAngularKernelDim
    congr 1
    funext angle
    simp only [shiftPrimitiveKernel, neg_zero, angularCharacter_zero_mode, mul_one]
  have mean : startupCharacterKernel dimension 0 =
      startupRealAngularKernelDim dimension (fun _ : ℝ => 1) contDiff_const := by
    unfold startupCharacterKernel startupRealAngularKernelDim
    congr 1
    funext angle
    simp only [angularCharacter_zero_mode, Complex.ofReal_one]
  rw [startupTrueAngularInverse, neg_zero, primitive, mean]

theorem startupCoordinateTestPairing_trueInverse {dimension : ℕ} (cell : ℤ)
    (coordinate : Fin dimension) (test : TestFunction openUnitDisk) :
    (startupCoordinateTestPairing cell coordinate test).comp (startupTrueAngularInverse dimension 0) =
      startupCoordinateTestPairing cell coordinate (startupTrueInverseTest test) := by
  rw [startupTrueAngularInverse_realDim, ← ContinuousLinearMap.comp_assoc,
    startupCoordinateTestPairing_angular, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.comp_id, startupCoordinateTestPairing_angular]
  exact (startupCoordinateTestPairing_sub cell coordinate _ _).symm

/-- Genuine normalized third row, retaining its actual cellwise axial multiplier. -/
def StartupWeakThirdEquation (axial : ℤ → ℂ) (theta scalar source : StartupL2 1) : Prop :=
  ∀ (cell : ℤ) (test : TestFunction openUnitDisk),
    startupCoordinateTestPairing cell 0 test source =
      -startupCoordinateTestPairing cell 0 (startupRotationTest test) scalar +
        axial cell * startupCoordinateTestPairing cell 0 (startupRotationTest test) theta

/-- Angular inversion on the SAME rough third component. Cellwise multipliers
remain literal; this theorem does not pretend an unbounded diagonal is bounded. -/
theorem startupSame_third_recovery (axial : ℤ → ℂ) (theta scalar source : StartupL2 1)
    (equation : StartupWeakThirdEquation axial theta scalar source)
    (thetaMean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) theta = 0)
    (scalarMean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) scalar = 0)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell 0 test scalar =
      axial cell * startupCoordinateTestPairing cell 0 test theta +
        startupCoordinateTestPairing cell 0 test (startupTrueAngularInverse 1 0 source) := by
  have inverse := congrArg (fun operator : StartupL2 1 →L[ℂ] ℂ => operator source)
    (startupCoordinateTestPairing_trueInverse cell 0 test)
  change startupCoordinateTestPairing cell 0 test (startupTrueAngularInverse 1 0 source) =
    startupCoordinateTestPairing cell 0 (startupTrueInverseTest test) source at inverse
  rw [inverse, equation cell (startupTrueInverseTest test), startupTrueInverseTest_rotation,
    startupCoordinateTestPairing_sub, sub_apply, sub_apply]
  change _ = axial cell * _ +
    (-(startupCoordinateTestPairing cell 0 (startupMeanTest test) scalar - _) +
      axial cell * (startupCoordinateTestPairing cell 0 (startupMeanTest test) theta - _))
  rw [thetaMean, scalarMean]
  ring

end Grad.CartesianStartup
