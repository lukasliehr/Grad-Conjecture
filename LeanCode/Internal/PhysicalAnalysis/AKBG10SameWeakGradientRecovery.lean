import AKBG9PrimitiveForceVectorTerm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

/-- Exact unprojected force equation on actual rough carriers. The right
side is the already assembled genuine force minus its coefficient correction. -/
def StartupWeakForceEquation (theta : StartupL2 1) (vector right : StartupL2 2) : Prop :=
  ∀ (cell : ℤ) (coordinate : Fin 2) (test : TestFunction openUnitDisk),
    startupCoordinateTestPairing cell coordinate test right =
      startupCoordinateTestPairing cell 0 (startupRotationTest (startupDerivativeTest coordinate test)) theta +
        startupCoordinateTestPairing cell coordinate (startupRotationTest test) vector -
        startupCoordinateTestPairing cell coordinate test (originalValueKernel quarterValueMap vector)

def startupRecoveredGradient (vector right : StartupL2 2) : StartupL2 2 :=
  vector - originalAverageKernel vector +
    startupCovariantPrimitiveKernel (right + (2 : ℂ) • originalValueKernel quarterValueMap vector)

theorem startupCovariantPrimitive_force_recovery (theta : StartupL2 1) (vector right : StartupL2 2)
    (equation : StartupWeakForceEquation theta vector right)
    (mean : ∀ (cell : ℤ) (test : TestFunction openUnitDisk),
      startupCoordinateTestPairing cell 0 (startupMeanTest test) theta = 0)
    (cell : ℤ) (coordinate : Fin 2) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate test (startupCovariantPrimitiveKernel right) =
      -startupCoordinateTestPairing cell 0 (startupDerivativeTest coordinate test) theta +
        startupCoordinateTestPairing cell coordinate test (originalAverageKernel vector) -
        startupCoordinateTestPairing cell coordinate test vector -
        (2 : ℂ) * startupCoordinateTestPairing cell coordinate test
          (startupCovariantPrimitiveKernel (originalValueKernel quarterValueMap vector)) := by
  rw [startupCovariantPrimitive_pairing]
  have rows (target : Fin 2) := equation cell target
    (startupCovariantCompactTest (fun angle : ℝ => angle) contDiff_id coordinate target test)
  simp_rw [rows]
  have regroup (scalar first second : Fin 2 → ℂ) :
      (∑ target, (scalar target + first target - second target)) =
        (∑ target, scalar target) + (∑ target, (first target - second target)) := by
    simp only [Fin.sum_univ_two]
    ring
  rw [regroup]
  rw [startupCovariantPrimitive_theta_term theta mean, startupCovariantPrimitive_vector_term]
  ring

/-- The recovered L2 field is the weak gradient of the SAME Theta. No H1
premise or new scalar unknown has been introduced. -/
theorem startupSame_weakGradient (theta : StartupL2 1) (vector right : StartupL2 2)
    (equation : StartupWeakForceEquation theta vector right)
    (mean : ∀ (cell : ℤ) (test : TestFunction openUnitDisk),
      startupCoordinateTestPairing cell 0 (startupMeanTest test) theta = 0)
    (cell : ℤ) (coordinate : Fin 2) (test : TestFunction openUnitDisk) :
    -startupCoordinateTestPairing cell 0 (startupDerivativeTest coordinate test) theta =
      startupCoordinateTestPairing cell coordinate test (startupRecoveredGradient vector right) := by
  rw [startupRecoveredGradient, map_add, map_sub, map_add, map_smul, map_add, map_smul]
  rw [startupCovariantPrimitive_force_recovery theta vector right equation mean]
  simp only [smul_eq_mul]
  ring

end Grad.CartesianStartup
