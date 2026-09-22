import AKAX15AngularTestLaplacian

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

open Set MeasureTheory
open scoped ContDiff

namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets Grad.WeightedJets
open Grad.Constraints Grad.RepresentedKernel.SpatialProduct
open Grad.GaugeCoefficients.Physical.RadialLedger

def startupAddTest (first second : TestFunction openUnitDisk) : TestFunction openUnitDisk where
  toFun := first.toFun + second.toFun
  smooth := first.smooth.add second.smooth
  compact := first.compact.add second.compact
  supported := (tsupport_add first.toFun second.toFun).trans (union_subset first.supported second.supported)

theorem startupTestPairing_add (cell : ℤ) (vector : PhysicalValue 3)
    (first second : TestFunction openUnitDisk) :
    startupTestPairing cell vector (startupAddTest first second) =
      startupTestPairing cell vector first + startupTestPairing cell vector second := by
  ext field
  simp only [add_apply, startupTestPairing_apply]
  change (∫ point in openUnitDisk, (first.toFun point + second.toFun point) • inner ℂ vector (field point cell)) = _
  simp_rw [add_smul]
  exact integral_add
    (Grad.WeakTesting.pairing_integrable 3 openUnitDisk cell vector first.toFun
      (first.smooth.continuous.memLp_of_hasCompactSupport first.compact) field)
    (Grad.WeakTesting.pairing_integrable 3 openUnitDisk cell vector second.toFun
      (second.smooth.continuous.memLp_of_hasCompactSupport second.compact) field)

def startupLaplacianTest (test : TestFunction openUnitDisk) : TestFunction openUnitDisk :=
  startupAddTest (startupDerivativeTest 0 (startupDerivativeTest 0 test))
    (startupDerivativeTest 1 (startupDerivativeTest 1 test))

theorem startupWordDerivative_two_directions (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test)
    (direction : Fin 2) (point : Spatial) :
    directionDerivative direction (directionDerivative direction test) point =
      wordDerivative 2 (fun _ => direction) test point := by
  have identity := listDerivative_ofFn isOpen_univ 2 (fun _ => direction) smooth.contDiffOn (mem_univ point)
  exact identity

theorem startupLaplacianTest_toFun (test : TestFunction openUnitDisk) :
    (startupLaplacianTest test).toFun = startupWordLaplacian test.toFun := by
  funext point
  change directionDerivative 0 (directionDerivative 0 test.toFun) point +
    directionDerivative 1 (directionDerivative 1 test.toFun) point = _
  rw [startupWordDerivative_two_directions test.toFun test.smooth, startupWordDerivative_two_directions test.toFun test.smooth]
  rfl

theorem startupLaplacianTest_sub (first second : TestFunction openUnitDisk) :
    startupLaplacianTest (startupSubTest first second) =
      startupSubTest (startupLaplacianTest first) (startupLaplacianTest second) := by
  simp only [startupLaplacianTest, startupDerivativeTest_sub]
  apply startupTest_ext
  intro point
  change ((_ : ℝ) - (_ : ℝ)) + ((_ : ℝ) - (_ : ℝ)) =
    ((_ : ℝ) + (_ : ℝ)) - ((_ : ℝ) + (_ : ℝ))
  ring

theorem startupLaplacianTest_angular (weight : ℝ → ℝ) (smooth : ContDiff ℝ ∞ weight)
    (test : TestFunction openUnitDisk) :
    startupLaplacianTest (startupAngularCompactTest weight smooth test) =
      startupAngularCompactTest weight smooth (startupLaplacianTest test) := by
  apply startupTest_ext
  intro point
  rw [startupLaplacianTest_toFun]
  change startupWordLaplacian (startupAngularTest weight test.toFun) point =
    startupAngularTest weight (startupLaplacianTest test).toFun point
  rw [startupLaplacianTest_toFun]
  exact startupAngularTest_laplacian weight smooth test.toFun test.smooth point

/-- The transpose of TRUE Z0 commutes with the genuine Cartesian Laplacian. -/
theorem startupLaplacianTest_trueInverse (test : TestFunction openUnitDisk) :
    startupLaplacianTest (startupTrueInverseTest test) =
      startupTrueInverseTest (startupLaplacianTest test) := by
  simp only [startupTrueInverseTest, startupLaplacianTest_sub, startupLaplacianTest_angular]

theorem startupTestPairing_laplacian (cell : ℤ) (vector : PhysicalValue 3) (test : TestFunction openUnitDisk) :
    startupTestPairing cell vector (startupLaplacianTest test) =
      ∑ direction : Fin 2, startupTestPairing cell vector (startupDerivativeTest direction (startupDerivativeTest direction test)) := by
  rw [startupLaplacianTest, startupTestPairing_add, Fin.sum_univ_two]

/-- Exact Z0 Delta versus Delta Z0 weak scalar identity on every rough all-cell field. -/
theorem startupTrueInverse_laplacianWeak (cell : ℤ) (vector : PhysicalValue 3)
    (test : TestFunction openUnitDisk) (field : StartupL2 3) :
    (∑ direction : Fin 2, startupTestPairing cell vector
      (startupTrueInverseTest (startupDerivativeTest direction (startupDerivativeTest direction test))) field) =
      ∑ direction : Fin 2, startupTestPairing cell vector
        (startupDerivativeTest direction (startupDerivativeTest direction (startupTrueInverseTest test))) field := by
  have main := startupTestPairing_trueInverse cell vector (startupLaplacianTest test)
  rw [← startupLaplacianTest_trueInverse, startupTestPairing_laplacian] at main
  have identity := congrArg (fun pairing : StartupL2 3 →L[ℂ] ℂ => pairing field) main
  rw [ContinuousLinearMap.comp_apply, startupTestPairing_laplacian, sum_apply, sum_apply] at identity
  rw [← identity]
  apply Finset.sum_congr rfl
  intro direction _
  exact (congrArg (fun pairing : StartupL2 3 →L[ℂ] ℂ => pairing field)
    (startupTestPairing_trueInverse cell vector (startupDerivativeTest direction (startupDerivativeTest direction test)))).symm

end Grad.CartesianStartup
