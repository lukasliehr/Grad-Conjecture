import AKBN2ScaledCompactTestCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.SpatialDilation
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupPulledTest_mean (scale : Scale) (test : TestFunction openUnitDisk) :
    startupPulledTest scale (startupMeanTest test) = startupMeanTest (startupPulledTest scale test) :=
  startupPulledTest_angular scale _ _ test

theorem startupPulledTest_meanFree (scale : Scale) (test : TestFunction openUnitDisk) :
    startupPulledTest scale (startupMeanFreeTest test) = startupMeanFreeTest (startupPulledTest scale test) := by
  unfold startupMeanFreeTest
  rw [startupPulledTest_sub,startupPulledTest_mean]

theorem startupPulledTest_trueInverse (scale : Scale) (test : TestFunction openUnitDisk) :
    startupPulledTest scale (startupTrueInverseTest test) = startupTrueInverseTest (startupPulledTest scale test) := by
  unfold startupTrueInverseTest
  rw [startupPulledTest_sub,startupPulledTest_angular,startupPulledTest_angular,startupPulledTest_angular]

theorem startupCoordinateTestPairing_qrad (field : StartupL2 2) (cell : ℤ)
    (source : Fin 2) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell source test (startupGenuineQradKernel field) =
      ∑ target : Fin 2, startupCoordinateTestPairing cell target (startupQradTestComponent target source test) field := by
  rw [startupCoordinateTestPairing_apply,startupGenuineQrad_rawTranspose field cell source test.toFun test.smooth test.compact]
  simp only [startupCoordinateTestPairing_apply,startupRawQradTest_same]

/-- The SAME unweighted corrected radial projector commutes with the accepted dilation. -/
theorem startupGenuineQradKernel_dilation (scale : Scale) (field : StartupL2 2) :
    startupMomentDilation scale (startupGenuineQradKernel field) =
      startupGenuineQradKernel (startupMomentDilation scale field) := by
  apply startupField_eq_of_coordinatePairing
  intro cell source test
  rw [startupCoordinateTestPairing_dilation,startupCoordinateTestPairing_qrad,
    startupCoordinateTestPairing_qrad,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro target _
  rw [startupCoordinateTestPairing_dilation,startupPulledTest_qrad]

/-- Dilation commutes with the genuine inverse of R on mean-free fields. -/
theorem startupTrueAngularInverse_dilation {dimension : ℕ} (scale : Scale) (field : StartupL2 dimension) :
    startupMomentDilation scale (startupTrueAngularInverse dimension 0 field) =
      startupTrueAngularInverse dimension 0 (startupMomentDilation scale field) := by
  have inversePairing (value : StartupL2 dimension) (cell : ℤ) (coordinate : Fin dimension) (test : TestFunction openUnitDisk) :
      startupCoordinateTestPairing cell coordinate test (startupTrueAngularInverse dimension 0 value) =
        startupCoordinateTestPairing cell coordinate (startupTrueInverseTest test) value :=
    congrArg (fun mapping : StartupL2 dimension →L[ℂ] ℂ => mapping value)
      (startupCoordinateTestPairing_trueInverse cell coordinate test)
  apply startupField_eq_of_coordinatePairing
  intro cell coordinate test
  rw [startupCoordinateTestPairing_dilation,inversePairing,inversePairing,
    startupCoordinateTestPairing_dilation,startupPulledTest_trueInverse]

end Grad.CartesianStartup
