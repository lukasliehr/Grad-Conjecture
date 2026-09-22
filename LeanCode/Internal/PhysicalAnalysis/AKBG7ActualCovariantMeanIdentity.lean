import AKBG6CompactPrimitiveElimination

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

theorem startupField_eq_of_coordinatePairing {dimension : ℕ} (first second : StartupL2 dimension)
    (same : ∀ (cell : ℤ) (coordinate : Fin dimension) (test : TestFunction openUnitDisk),
      startupCoordinateTestPairing cell coordinate test first = startupCoordinateTestPairing cell coordinate test second) :
    first = second := by
  apply sub_eq_zero.mp
  have rows (cell : ℤ) (coordinate : Fin dimension) : ∀ᵐ point ∂volume.restrict openUnitDisk,
      (first - second) point cell coordinate = 0 := by
    apply Grad.WeakTesting.Separation.coordinate_ae_eq_zero dimension openUnitDisk openUnitDisk_isOpen cell coordinate
    intro test smooth compact supported
    change startupCoordinateTestPairing cell coordinate ⟨test, smooth, compact, supported⟩ (first - second) = 0
    rw [map_sub, same cell coordinate ⟨test, smooth, compact, supported⟩, sub_self]
  have allCoordinates := ae_all_iff.mpr (fun cell : ℤ => ae_all_iff.mpr (rows cell))
  apply Lp.ext
  filter_upwards [allCoordinates, Lp.coeFn_zero (CellValues dimension) 2 (volume.restrict openUnitDisk)] with point zeroCoordinates zeroRepresentative
  rw [zeroRepresentative]
  apply lp.ext
  funext cell
  apply PiLp.ext
  intro coordinate
  exact zeroCoordinates cell coordinate

/-- The mean in C(R-J)=I-A is the actual original equivariant average. -/
theorem startupCovariantAngularKernel_one :
    startupCovariantAngularKernel (fun _ : ℝ => 1) contDiff_const = originalAverageKernel := by
  apply ContinuousLinearMap.ext
  intro field
  apply startupField_eq_of_coordinatePairing
  intro cell source test
  rw [startupCoordinateTestPairing_apply, startupCoordinateTestPairing_apply,
    startupCovariantAngularKernel_transpose (fun _ : ℝ => 1) contDiff_const field cell source test.toFun test.smooth test.compact,
    startupAverageKernel_transpose field cell source test.toFun test.smooth test.compact]
  simp only [startupCovariantAngularTest, one_mul]

end Grad.CartesianStartup
