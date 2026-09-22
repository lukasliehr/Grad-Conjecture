import AKBK25ActualSourcePlanarWeakConsumer
import AKBG25SameFullCircleForceConsumer
import AKBF7SameDimensionDilation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.SpatialDilation

/-- Existing DIL1 compact-test pullback, restricted to the original disk. -/
def startupPulledTest (scale : Scale) (test : TestFunction openUnitDisk) : TestFunction openUnitDisk :=
  let original : TestFunction (disk 1) := Restriction.widenTest
    (by rw [openUnitDisk_eq_ball]; exact Set.Subset.rfl) test
  let expanded := Restriction.widenTest (disk_subset_expanded 1 scale) original
  Restriction.widenTest (by rw [openUnitDisk_eq_ball]; exact Set.Subset.rfl) (pulledTest 1 scale expanded)

theorem startupPulledTest_apply (scale : Scale) (test : TestFunction openUnitDisk) (point : Spatial) :
    (startupPulledTest scale test).toFun point = test.toFun (scale.val⁻¹ • point) := rfl

/-- The existing source-matched full-cell dilation has exactly the two-dimensional
Jacobian in every compact coordinate pairing. -/
theorem startupCoordinateTestPairing_dilation {dimension : ℕ} (scale : Scale)
    (field : StartupL2 dimension) (cell : ℤ) (coordinate : Fin dimension) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate test (startupMomentDilation scale field) =
      (scale.val ^ 2)⁻¹ • startupCoordinateTestPairing cell coordinate (startupPulledTest scale test) field := by
  rw [startupCoordinateTestPairing_apply]
  calc
    _ = ∫ point in pullDomain scale openUnitDisk,
        test.toFun point • rawValue dimension openUnitDisk openUnitDisk_isOpen.measurableSet scale field point cell coordinate := by
      simpa only [startupMomentDilation,EuclideanSpace.inner_single_left,map_one,one_mul] using
        Restriction.integral_restriction dimension (startupDilation_inclusion scale)
          (openUnitDisk_isOpen.preimage (continuous_const_smul scale.val)).measurableSet
          (rawValue dimension openUnitDisk openUnitDisk_isOpen.measurableSet scale field)
          cell (EuclideanSpace.single coordinate 1) test.toFun test.supported
    _ = (scale.val ^ 2)⁻¹ • ∫ point in openUnitDisk,
        test.toFun (scale.val⁻¹ • point) • field point cell coordinate := by
      simpa only [EuclideanSpace.inner_single_left,map_one,one_mul] using
        integral_rawValue dimension openUnitDisk openUnitDisk_isOpen.measurableSet scale test.toFun field cell
          (EuclideanSpace.single coordinate 1)
    _ = _ := by rw [startupCoordinateTestPairing_apply]; rfl

end Grad.CartesianStartup
