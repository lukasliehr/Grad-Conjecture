import AKBP1CorrectedWeakPrincipalSplit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

theorem startupER_divergence_split (axial : ℤ → ℂ) (scalar determinant scalarFlux : StartupL2 1)
    (source force planarFlux : StartupL2 2) (cell : ℤ) (test : TestFunction openUnitDisk) :
    -startupCoordinateTestPairing cell 0 test determinant -
      axial cell * startupCoordinateTestPairing cell 0 test scalar +
      axial cell * startupCoordinateTestPairing cell 0 test scalarFlux +
      startupWeakDivergencePairing
        (planarFlux + (1/2 : ℂ) • originalValueKernel quarterValueMap (originalAverageKernel (source-force))) cell test =
    startupWeakDivergencePairing
      (planarFlux - (1/2 : ℂ) • originalValueKernel quarterValueMap (originalAverageKernel force)) cell test +
      startupERLowerDivergence axial scalar determinant scalarFlux source cell test := by
  simp only [map_sub, smul_sub, startupWeakDivergence_add_field, startupWeakDivergence_sub_field,
    startupERLowerDivergence]
  ring

/-- All three genuine original first-order rows give the corrected ER11
principal/lower decomposition on SAME Q0(a_C). Quotient scalar and curl gauges
and the projected-force complement cancellation remain internal. -/
theorem startupSame_fullCircle_correctedER (axial : ℤ → ℂ)
    (psi knownThird thirdCorrection determinant scalarFlux : StartupL2 1) (covariant : StartupL2 3)
    (knownForce forceCorrection planarFlux : StartupL2 2)
    (projected : StartupWeakProjectedForceEquation psi (originalValueKernel planarPartMap covariant)
      (knownForce-forceCorrection))
    (third : StartupWeakThirdEquation axial (originalScalarInverseKernel psi)
      (originalValueKernel toroidalPartMap covariant) (knownThird+thirdCorrection))
    (determinantRow : StartupWeakDeterminantEquation axial (originalValueKernel planarPartMap covariant)
      (originalValueKernel toroidalPartMap covariant) determinant planarFlux scalarFlux)
    (rawPsi : ℤ → Spatial → PhysicalValue 1)
    (samePsi : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, psi point cell = rawPsi cell point)
    (psiOrbitMean : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (∫ angle in Icc (0 : ℝ) (2*Real.pi), rawPsi cell (planeRotationEquiv angle point)) = 0) :
    let vector := originalValueKernel planarPartMap (originalCircleKernel covariant)
    let scalar := originalValueKernel toroidalPartMap (originalCircleKernel covariant)
    let flux := planarFlux - (1/2 : ℂ) • originalValueKernel quarterValueMap (originalAverageKernel forceCorrection)
    (∀ cell coordinate test,
      startupCoordinateTestPairing cell coordinate (startupLaplacianTest test) vector =
        startupERPlanarPrincipal forceCorrection flux cell coordinate test +
        startupERPlanarRemainder (startupERLowerDivergence axial scalar determinant scalarFlux knownForce cell)
          knownForce cell coordinate test) ∧
    (∀ cell test, startupCoordinateTestPairing cell 0 (startupLaplacianTest test) scalar =
      startupCoordinateTestPairing cell 0 (startupLaplacianTest test) (startupTrueAngularInverse 1 0 thirdCorrection) +
      (axial cell * startupWeakDivergencePairing (startupRecoveredGradient vector (knownForce-forceCorrection)) cell test +
        startupCoordinateTestPairing cell 0 (startupLaplacianTest test) (startupTrueAngularInverse 1 0 knownThird))) := by
  have rows := startupSame_fullCircle_elliptic_consumer axial psi (knownThird+thirdCorrection)
    determinant scalarFlux covariant (knownForce-forceCorrection) planarFlux
    projected third determinantRow rawPsi samePsi psiOrbitMean
  refine ⟨?_, ?_⟩
  · apply startupERPlanar_split _ knownForce forceCorrection _ _ _ rows.2.1
    intro cell test
    exact (rows.1 cell test).trans (startupER_divergence_split axial _ determinant scalarFlux
      knownForce forceCorrection planarFlux cell test)
  · intro cell test
    rw [rows.2.2 cell test, map_add, map_add]
    ring

end Grad.CartesianStartup
