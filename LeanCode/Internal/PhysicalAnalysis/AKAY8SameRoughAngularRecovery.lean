import AKAY7TrueInverseRotationTests
import WT2Proof

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupField_eq_of_testPairing (first second : StartupL2 3)
    (same : ∀ (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk),
      startupTestPairing cell vector test first = startupTestPairing cell vector test second) :
    first = second := by
  apply Grad.WeakTesting.Separation.equality 3 openUnitDisk openUnitDisk_isOpen first second
  intro cell vector test smooth compact supported
  exact same cell vector ⟨test, smooth, compact, supported⟩

/-- Exact recovery of the SAME rough all-cell field from its genuine weak R equation
and actual zero angular mean. The accepted bounded inverse acts on its actual source. -/
theorem startupSameField_angularInverse (original source : StartupL2 3)
    (equation : ∀ (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk),
      -startupTestPairing cell vector (startupRotationTest test) original =
        startupTestPairing cell vector test source)
    (meanZero : startupRealAngularKernel (fun _ : ℝ => 1) contDiff_const original = 0) :
    startupTrueAngularInverse 3 0 source = original :=
  startupField_eq_of_testPairing _ _
    (startupTrueInverse_weakRotation_recovery original source equation meanZero)

end Grad.CartesianStartup
