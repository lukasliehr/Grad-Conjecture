import AKBG17WeakDeterminantElimination

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets Grad.WeightedJets.SpatialMultiplier
open Grad.RepresentedKernel.SpatialProduct Grad.PhysicalFamily

theorem startupCovariantCompactTest_rotation_commute (weight : ℝ → ℝ) (smooth : ContDiff ℝ ∞ weight)
    (source target : Fin 2) (test : TestFunction openUnitDisk) :
    startupCovariantCompactTest weight smooth source target (startupRotationTest test) =
      startupRotationTest (startupCovariantCompactTest weight smooth source target test) := by
  exact (startupRotationTest_angular _ _ test).symm

/-- The actual rough average lies in the R=J resonance, verified only on tests. -/
theorem startupAverage_rotation_pairing (field : StartupL2 2) (cell : ℤ) (source : Fin 2)
    (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell source (startupRotationTest test) (originalAverageKernel field) =
      -startupCoordinateTestPairing cell source test (originalValueKernel quarterValueMap (originalAverageKernel field)) := by
  rw [← startupAverage_quarter, startupAverage_pairing, startupAverage_pairing]
  simp_rw [startupCovariantCompactTest_rotation_commute, startupCovariantAverageCompact_rotation,
    startupCoordinateTestPairing_add, startupCoordinateTestPairing_real_smul,
    add_apply, smul_apply, startupCoordinateTestPairing_quarter]
  fin_cases source <;> simp only [Fin.sum_univ_two, startupQuarterEntry] <;> norm_num

theorem startupSpatialReflection_quarter (point : Spatial) :
    cartesianReflectionEquiv (planeQuarterTurn point) = -planeQuarterTurn (cartesianReflectionEquiv point) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [cartesianReflectionEquiv, cartesianReflection, planeQuarterTurn]

theorem startupRotationTest_reflection (test : TestFunction openUnitDisk) :
    startupRotationTest (startupReflectionTest test) =
      multiplyTest (fun _ : Spatial => (-1 : ℝ)) contDiff_const (startupReflectionTest (startupRotationTest test)) := by
  apply startupTest_ext
  intro point
  change fderiv ℝ (test.toFun ∘ cartesianReflectionEquiv) point (planeQuarterTurn point) =
    (-1 : ℝ) * fderiv ℝ test.toFun (cartesianReflectionEquiv point)
      (planeQuarterTurn (cartesianReflectionEquiv point))
  rw [fderiv_comp point (test.smooth.differentiable (by simp) (cartesianReflectionEquiv point))
    cartesianReflectionEquiv.toContinuousLinearEquiv.differentiableAt]
  simp only [ContinuousLinearMap.comp_apply, LinearIsometryEquiv.fderiv]
  change fderiv ℝ test.toFun (cartesianReflectionEquiv point)
    (cartesianReflectionEquiv (planeQuarterTurn point)) = _
  rw [startupSpatialReflection_quarter, map_neg]
  ring

theorem startupCoordinateTestPairing_reflection (field : StartupL2 2) (cell : ℤ) (source : Fin 2)
    (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell source test
      (startupPointKernel reflectionValueMap cartesianReflectionEquiv field) =
      (if source = 0 then 1 else -1 : ℝ) • startupCoordinateTestPairing cell source (startupReflectionTest test) field := by
  simp only [startupCoordinateTestPairing_apply]
  exact startupReflectionKernel_transpose field cell source test.toFun

/-- The reflected average is also in the R=J resonance. The reflection's
spatial and value signs cancel, before tangential projection is applied. -/
theorem startupReflectedAverage_rotation_pairing (field : StartupL2 2) (cell : ℤ) (source : Fin 2)
    (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell source (startupRotationTest test)
      (startupPointKernel reflectionValueMap cartesianReflectionEquiv (originalAverageKernel field)) =
      -startupCoordinateTestPairing cell source test (originalValueKernel quarterValueMap
        (startupPointKernel reflectionValueMap cartesianReflectionEquiv (originalAverageKernel field))) := by
  have reflectedR := startupRotationTest_reflection test
  have pairR := congrArg (fun query : TestFunction openUnitDisk =>
    startupCoordinateTestPairing cell source query (originalAverageKernel field)) reflectedR
  rw [startupCoordinateTestPairing_real_smul, smul_apply, startupAverage_rotation_pairing] at pairR
  rw [startupCoordinateTestPairing_reflection]
  rw [← neg_neg (originalValueKernel quarterValueMap _), ← startupReflection_quarter, map_neg,
    neg_neg, startupCoordinateTestPairing_reflection]
  have signs : startupCoordinateTestPairing cell source (startupReflectionTest (startupRotationTest test))
      (originalAverageKernel field) = startupCoordinateTestPairing cell source (startupReflectionTest test)
      (originalValueKernel quarterValueMap (originalAverageKernel field)) := by
    change -_ = (-1 : ℝ) • _ at pairR
    simp only [neg_smul, one_smul] at pairR
    exact (neg_inj.mp pairR).symm
  rw [signs]

end Grad.CartesianStartup
