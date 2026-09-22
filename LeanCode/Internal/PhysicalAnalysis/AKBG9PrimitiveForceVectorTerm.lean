import AKBG8PrimitiveForceScalarTerm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

/-- Exact vector part of the raw primitive reduction. The full equivariant
average AV is retained and the two J contributions have their genuine signs. -/
theorem startupCovariantPrimitive_vector_term (vector : StartupL2 2)
    (cell : ℤ) (source : Fin 2) (test : TestFunction openUnitDisk) :
    (∑ target : Fin 2,
      (startupCoordinateTestPairing cell target
        (startupRotationTest (startupCovariantCompactTest (fun angle : ℝ => angle) contDiff_id source target test)) vector -
        startupCoordinateTestPairing cell target
          (startupCovariantCompactTest (fun angle : ℝ => angle) contDiff_id source target test)
            (originalValueKernel quarterValueMap vector))) =
      startupCoordinateTestPairing cell source test (originalAverageKernel vector) -
        startupCoordinateTestPairing cell source test vector -
        (2 : ℂ) * startupCoordinateTestPairing cell source test
          (startupCovariantPrimitiveKernel (originalValueKernel quarterValueMap vector)) := by
  rw [startupAverage_pairing, startupCovariantPrimitive_pairing]
  simp_rw [startupCovariantPrimitiveCompact_rotation, startupCoordinateTestPairing_sub,
    startupCoordinateTestPairing_add, startupCoordinateTestPairing_real_smul,
    sub_apply, add_apply, smul_apply, startupCoordinateTestPairing_quarter]
  fin_cases source <;> simp only [Fin.sum_univ_two, startupQuarterEntry] <;> norm_num <;> ring

end Grad.CartesianStartup
