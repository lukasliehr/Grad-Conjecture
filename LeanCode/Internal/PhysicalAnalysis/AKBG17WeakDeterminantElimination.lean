import AKBG16MeanDivergenceTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 700000
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

theorem startupWeakDivergence_sub_test (vector : StartupL2 2) (cell : ℤ)
    (first second : TestFunction openUnitDisk) :
    startupWeakDivergencePairing vector cell (startupSubTest first second) =
      startupWeakDivergencePairing vector cell first - startupWeakDivergencePairing vector cell second := by
  simp only [startupWeakDivergencePairing, startupDerivativeTest_sub, startupCoordinateTestPairing_sub, sub_apply]
  ring

theorem startupWeakDivergence_add_field (first second : StartupL2 2) (cell : ℤ)
    (test : TestFunction openUnitDisk) :
    startupWeakDivergencePairing (first + second) cell test =
      startupWeakDivergencePairing first cell test + startupWeakDivergencePairing second cell test := by
  simp only [startupWeakDivergencePairing, map_add]
  ring

/-- The actual outer scalar projection of the determinant is retained on the
unknown. Its coefficient fluxes have already received their literal I-A / I-Pi. -/
def StartupWeakDeterminantEquation (axial : ℤ → ℂ) (vector : StartupL2 2)
    (scalar determinant : StartupL2 1) (planarFlux : StartupL2 2) (scalarFlux : StartupL2 1) : Prop :=
  ∀ cell test, startupCoordinateTestPairing cell 0 test determinant =
    -startupWeakDivergencePairing vector cell (startupMeanFreeTest test) -
      axial cell * startupCoordinateTestPairing cell 0 (startupMeanFreeTest test) scalar +
      startupWeakDivergencePairing planarFlux cell test + axial cell * startupCoordinateTestPairing cell 0 test scalarFlux

/-- Literal divergence recovery from the genuine projected determinant and
force rows. The equivariant contribution is J A(right)/2, not zero. -/
theorem startupSame_determinant_divergence (axial : ℤ → ℂ) (theta scalar determinant scalarFlux : StartupL2 1)
    (vector right planarFlux : StartupL2 2)
    (forceEquation : StartupWeakForceEquation theta vector right)
    (determinantEquation : StartupWeakDeterminantEquation axial vector scalar determinant planarFlux scalarFlux)
    (scalarMean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) scalar = 0)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakDivergencePairing vector cell test =
      -startupCoordinateTestPairing cell 0 test determinant -
        axial cell * startupCoordinateTestPairing cell 0 test scalar +
        axial cell * startupCoordinateTestPairing cell 0 test scalarFlux +
        startupWeakDivergencePairing
          (planarFlux + (1 / 2 : ℂ) • originalValueKernel quarterValueMap (originalAverageKernel right)) cell test := by
  have determinantRow := determinantEquation cell test
  change _ = -startupWeakDivergencePairing vector cell (startupSubTest test (startupMeanTest test)) -
    axial cell * startupCoordinateTestPairing cell 0 (startupSubTest test (startupMeanTest test)) scalar + _ + _ at determinantRow
  rw [startupWeakDivergence_sub_test, startupCoordinateTestPairing_sub, sub_apply,
    scalarMean, sub_zero, startupWeakDivergence_mean,
    startupSame_force_average_recovery theta vector right forceEquation] at determinantRow
  rw [startupWeakDivergence_add_field]
  linear_combination determinantRow

end Grad.CartesianStartup
