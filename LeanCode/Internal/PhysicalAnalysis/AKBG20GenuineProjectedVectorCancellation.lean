import AKBG19TangentialWeakForceAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets Grad.WeightedJets.SpatialMultiplier

theorem startupAverageTestComponent_same (target source : Fin 2) (test : TestFunction openUnitDisk) :
    startupAverageTestComponent target source test =
      startupCovariantCompactTest (fun _ : ℝ => 1) contDiff_const source target test := by
  apply startupTest_ext
  intro point
  change startupAngularTest (fun angle => startupInverseRotationEntry source target (-angle)) test.toFun point =
    startupAngularTest (fun angle => 1 * startupInverseRotationEntry source target (-angle)) test.toFun point
  simp only [one_mul]

theorem startupTwiceQuarterTangential_pairing (field : StartupL2 2) (cell : ℤ) (source : Fin 2)
    (test : TestFunction openUnitDisk) :
    (2 : ℂ) * startupCoordinateTestPairing cell source test
      (originalValueKernel quarterValueMap (originalTangentialKernel field)) =
      startupCoordinateTestPairing cell source test (originalValueKernel quarterValueMap (originalAverageKernel field)) +
        ((if source = 0 then 1 else -1 : ℝ) : ℂ) *
          startupCoordinateTestPairing cell source (startupReflectionTest test)
            (originalValueKernel quarterValueMap (originalAverageKernel field)) := by
  change (2 : ℂ) * startupCoordinateTestPairing cell source test (originalValueKernel quarterValueMap
    ((1/2 : ℂ) • (originalAverageKernel field - startupPointKernel reflectionValueMap cartesianReflectionEquiv
      (originalAverageKernel field)))) = _
  rw [map_smul, map_sub, map_smul, map_sub]
  have reflected := startupCoordinateTestPairing_reflection
    (originalValueKernel quarterValueMap (originalAverageKernel field)) cell source test
  rw [startupReflection_quarter, map_neg] at reflected
  simp only [Complex.real_smul, smul_eq_mul] at reflected ⊢
  linear_combination reflected

/-- The genuine I+JTJ force projection removes exactly the tangential
complement of the SAME covariant field; this is an identity on compact tests. -/
theorem startupGenuineQrad_vector_cancellation (vector : StartupL2 2) (cell : ℤ) (source : Fin 2)
    (test : TestFunction openUnitDisk) :
    (∑ target : Fin 2, startupWeakForceVectorPairing vector cell target (startupQradTestComponent target source test)) =
      startupWeakForceVectorPairing (vector - originalTangentialKernel vector) cell source test := by
  rw [startupWeakForceVector_fixed_quotient, startupTwiceQuarterTangential_pairing]
  have average := startupAverage_vector_term vector cell source test
  have reflected := startupAverage_vector_term vector cell source (startupReflectionTest test)
  change (∑ target : Fin 2, startupWeakForceVectorPairing vector cell target
    (startupCovariantCompactTest (fun _ : ℝ => 1) contDiff_const source target test)) = _ at average
  change (∑ target : Fin 2, startupWeakForceVectorPairing vector cell target
    (startupCovariantCompactTest (fun _ : ℝ => 1) contDiff_const source target (startupReflectionTest test))) = _ at reflected
  rw [startupAverage_quarter] at average reflected
  simp only [startupQradTestComponent, startupWeakForceVector_sub_test, startupWeakForceVector_const_mul_test,
    startupWeakForceVector_add_test, startupAverageTestComponent_same]
  simp only [Fin.sum_univ_two] at average reflected ⊢
  fin_cases source
  · norm_num at average reflected ⊢
    linear_combination -(1/2 : ℂ) * average - (1/2 : ℂ) * reflected
  · norm_num at average reflected ⊢
    linear_combination -(1/2 : ℂ) * average + (1/2 : ℂ) * reflected

end Grad.CartesianStartup
