import AKBG20GenuineProjectedVectorCancellation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets Grad.WeightedJets.SpatialMultiplier
open Grad.RepresentedKernel.SpatialProduct

theorem startupDerivativeTest_add (direction : Fin 2) (first second : TestFunction openUnitDisk) :
    startupDerivativeTest direction (startupAddTest first second) =
      startupAddTest (startupDerivativeTest direction first) (startupDerivativeTest direction second) := by
  apply startupTest_ext
  intro point
  exact congrFun (startupDirection_add first.toFun second.toFun first.smooth second.smooth direction) point

theorem startupCovariantAverage_gradient_pairing (scalar : StartupL2 1)
    (mean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) scalar = 0)
    (cell : ℤ) (source : Fin 2) (test : TestFunction openUnitDisk) :
    (∑ target : Fin 2, startupCoordinateTestPairing cell 0
      (startupDerivativeTest target (startupCovariantCompactTest (fun _ : ℝ => 1) contDiff_const source target test)) scalar) = 0 := by
  rw [Fin.sum_univ_two, ← add_apply, ← startupCoordinateTestPairing_add, startupCovariantCompactTest_divergence]
  exact mean cell (startupDerivativeTest source test)

/-- Qrad preserves the actual gradient of a rough mean-free scalar, verified
without claiming that its derivative already lies in L2. -/
theorem startupGenuineQrad_gradient_cancellation (scalar : StartupL2 1)
    (mean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) scalar = 0)
    (cell : ℤ) (source : Fin 2) (test : TestFunction openUnitDisk) :
    (∑ target : Fin 2, startupCoordinateTestPairing cell 0
      (startupDerivativeTest target (startupQradTestComponent target source test)) scalar) =
      startupCoordinateTestPairing cell 0 (startupDerivativeTest source test) scalar := by
  have average := startupCovariantAverage_gradient_pairing scalar mean cell source test
  have reflected := startupCovariantAverage_gradient_pairing scalar mean cell source (startupReflectionTest test)
  simp only [startupQradTestComponent, startupDerivativeTest_sub, startupDerivativeTest_add,
    startupDerivativeTest_const_mul, startupCoordinateTestPairing_sub, startupCoordinateTestPairing_add,
    startupCoordinateTestPairing_real_smul, sub_apply, add_apply, smul_apply, startupAverageTestComponent_same]
  simp only [Fin.sum_univ_two] at average reflected ⊢
  fin_cases source
  · norm_num at average reflected ⊢
    linear_combination -(1/2 : ℂ) * average - (1/2 : ℂ) * reflected
  · norm_num at average reflected ⊢
    linear_combination -(1/2 : ℂ) * average + (1/2 : ℂ) * reflected

/-- Exact original projected force interface on unweighted rough carriers. The
right field is already Qrad(force minus literal correction). -/
def StartupWeakProjectedForceEquation (psi : StartupL2 1) (covariant right : StartupL2 2) : Prop :=
  ∀ cell source test, startupCoordinateTestPairing cell source test right =
    ∑ target : Fin 2, (-startupCoordinateTestPairing cell 0
      (startupDerivativeTest target (startupQradTestComponent target source test)) psi +
      startupWeakForceVectorPairing covariant cell target (startupQradTestComponent target source test))

/-- Genuine Qrad-to-fixed-Q0 cancellation at the rough distributional level.
The SAME covariant is used, and the scalar primitive is identified by its actual R equation. -/
theorem startupSame_projected_to_force (theta psi : StartupL2 1) (covariant right : StartupL2 2)
    (projected : StartupWeakProjectedForceEquation psi covariant right)
    (mean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) psi = 0)
    (rotation : ∀ cell test, -startupCoordinateTestPairing cell 0 (startupRotationTest test) theta =
      startupCoordinateTestPairing cell 0 test psi) :
    StartupWeakForceEquation theta (covariant - originalTangentialKernel covariant) right := by
  intro cell source test
  rw [projected]
  have regroup (scalar vector : Fin 2 → ℂ) :
      (∑ target, (-scalar target + vector target)) = -(∑ target, scalar target) + ∑ target, vector target := by
    simp only [Fin.sum_univ_two]
    ring
  rw [regroup, startupGenuineQrad_gradient_cancellation psi mean,
    startupGenuineQrad_vector_cancellation, ← rotation cell (startupDerivativeTest source test), neg_neg]
  unfold startupWeakForceVectorPairing
  ring

end Grad.CartesianStartup
