import AKBG22ScalarAngularCommutation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

theorem startupTrueInverseTest_rotation_commute (test : TestFunction openUnitDisk) :
    startupTrueInverseTest (startupRotationTest test) = startupRotationTest (startupTrueInverseTest test) := by
  simp only [startupTrueInverseTest, startupRotationTest_sub, startupRotationTest_angular]

/-- The SAME bounded true scalar primitive has the genuine R equation from
an actual mean-free rough source; no assumed scalar PDE or H1 is needed. -/
theorem startupSame_scalarPrimitive_rotation (source : StartupL2 1)
    (mean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) source = 0)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    -startupCoordinateTestPairing cell 0 (startupRotationTest test) (startupTrueAngularInverse 1 0 source) =
      startupCoordinateTestPairing cell 0 test source := by
  have transpose := congrArg (fun operator : StartupL2 1 →L[ℂ] ℂ => operator source)
    (startupCoordinateTestPairing_trueInverse cell 0 (startupRotationTest test))
  change startupCoordinateTestPairing cell 0 (startupRotationTest test) (startupTrueAngularInverse 1 0 source) =
    startupCoordinateTestPairing cell 0 (startupTrueInverseTest (startupRotationTest test)) source at transpose
  rw [transpose, startupTrueInverseTest_rotation_commute, startupTrueInverseTest_rotation,
    startupCoordinateTestPairing_sub, sub_apply]
  change -(startupCoordinateTestPairing cell 0 (startupMeanTest test) source - _) = _
  rw [mean, zero_sub, neg_neg]

/-- Its genuine scalar mean is zero, derived from compact angular Fubini
and the SAME source mean. It is not an additional startup assumption. -/
theorem startupSame_scalarPrimitive_mean (source : StartupL2 1)
    (mean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) source = 0)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell 0 (startupMeanTest test) (startupTrueAngularInverse 1 0 source) = 0 := by
  have transpose := congrArg (fun operator : StartupL2 1 →L[ℂ] ℂ => operator source)
    (startupCoordinateTestPairing_trueInverse cell 0 (startupMeanTest test))
  change startupCoordinateTestPairing cell 0 (startupMeanTest test) (startupTrueAngularInverse 1 0 source) =
    startupCoordinateTestPairing cell 0 (startupTrueInverseTest (startupMeanTest test)) source at transpose
  rw [transpose, startupTrueInverseTest, startupCoordinateTestPairing_sub, sub_apply]
  have first : startupAngularCompactTest (fun angle : ℝ => angle) contDiff_id (startupMeanTest test) =
      startupMeanTest (startupAngularCompactTest (fun angle : ℝ => angle) contDiff_id test) :=
    startupAngularCompactTest_commute (fun angle : ℝ => angle) (fun _ : ℝ => 1) contDiff_id contDiff_const test
  rw [first]
  change startupCoordinateTestPairing cell 0 (startupMeanTest _) source -
    startupCoordinateTestPairing cell 0 (startupMeanTest _) source = 0
  rw [mean, mean, sub_self]

/-- Concrete rough force consumer: Theta is the actual scalar inverse of
psi, and the vector is the actual fixed quotient of the original covariant. -/
theorem startupSame_projected_scalarPrimitive_force (psi : StartupL2 1) (covariant right : StartupL2 2)
    (projected : StartupWeakProjectedForceEquation psi covariant right)
    (mean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) psi = 0) :
    StartupWeakForceEquation (startupTrueAngularInverse 1 0 psi)
      (covariant - originalTangentialKernel covariant) right ∧
    (∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test)
      (startupTrueAngularInverse 1 0 psi) = 0) :=
  ⟨startupSame_projected_to_force _ psi covariant right projected mean (startupSame_scalarPrimitive_rotation psi mean),
    startupSame_scalarPrimitive_mean psi mean⟩

end Grad.CartesianStartup
