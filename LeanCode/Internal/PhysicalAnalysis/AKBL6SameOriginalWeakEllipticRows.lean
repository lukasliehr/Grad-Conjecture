import AKBL5FixedQuotientScalarRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

/-- The actual three first-order rows imply these second-order identities on
literal Q0(a_C), with Theta=Kpsi. Both quotient gauges are proved internally;
there is no smooth-core, H1, unprojected force, or zero vector-average premise.
The axial diagonal remains explicit rather than being declared bounded. -/
theorem startupSame_fullCircle_elliptic_consumer (axial : ℤ → ℂ)
    (psi source determinant scalarFlux : StartupL2 1) (covariant : StartupL2 3)
    (right planarFlux : StartupL2 2)
    (projected : StartupWeakProjectedForceEquation psi (originalValueKernel planarPartMap covariant) right)
    (third : StartupWeakThirdEquation axial (originalScalarInverseKernel psi)
      (originalValueKernel toroidalPartMap covariant) source)
    (determinantRow : StartupWeakDeterminantEquation axial (originalValueKernel planarPartMap covariant)
      (originalValueKernel toroidalPartMap covariant) determinant planarFlux scalarFlux)
    (rawPsi : ℤ → Spatial → PhysicalValue 1)
    (samePsi : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, psi point cell = rawPsi cell point)
    (psiOrbitMean : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (∫ angle in Icc (0 : ℝ) (2*Real.pi), rawPsi cell (planeRotationEquiv angle point)) = 0) :
    let vector := originalValueKernel planarPartMap (originalCircleKernel covariant)
    let scalar := originalValueKernel toroidalPartMap (originalCircleKernel covariant)
    (∀ cell test, startupWeakDivergencePairing vector cell test =
      -startupCoordinateTestPairing cell 0 test determinant -
        axial cell * startupCoordinateTestPairing cell 0 test scalar +
        axial cell * startupCoordinateTestPairing cell 0 test scalarFlux +
        startupWeakDivergencePairing
          (planarFlux + (1/2 : ℂ) • originalValueKernel quarterValueMap (originalAverageKernel right)) cell test) ∧
    (∀ cell coordinate test,
      startupCoordinateTestPairing cell coordinate (startupLaplacianTest test) vector =
        if coordinate = 0 then
          -startupWeakDivergencePairing vector cell (startupDerivativeTest 0 test) -
            startupWeakCurlPairing right cell (startupTrueInverseTest (startupDerivativeTest 1 test)) -
            (2 : ℂ) * startupWeakDivergencePairing vector cell (startupTrueInverseTest (startupDerivativeTest 1 test))
        else -startupWeakDivergencePairing vector cell (startupDerivativeTest 1 test) +
            startupWeakCurlPairing right cell (startupTrueInverseTest (startupDerivativeTest 0 test)) +
            (2 : ℂ) * startupWeakDivergencePairing vector cell (startupTrueInverseTest (startupDerivativeTest 0 test))) ∧
    (∀ cell test, startupCoordinateTestPairing cell 0 (startupLaplacianTest test) scalar =
      axial cell * startupWeakDivergencePairing (startupRecoveredGradient vector right) cell test +
        startupCoordinateTestPairing cell 0 (startupLaplacianTest test) (startupTrueAngularInverse 1 0 source)) := by
  have force := startupSame_fullCircle_force_consumer psi covariant right projected rawPsi samePsi psiOrbitMean
  have scalarMean := startupSame_fullCircle_scalarMean covariant
  have curlMean := startupSame_fullCircle_curlMean covariant
  have thirdFixed := startupSame_fullCircle_third axial (originalScalarInverseKernel psi) source covariant third
  have determinantFixed := startupSame_fullCircle_determinant axial covariant determinant planarFlux scalarFlux determinantRow
  refine ⟨?_,?_,?_⟩
  · exact startupSame_determinant_divergence axial (originalScalarInverseKernel psi)
      (originalValueKernel toroidalPartMap (originalCircleKernel covariant)) determinant scalarFlux
      (originalValueKernel planarPartMap (originalCircleKernel covariant)) right planarFlux
      force.1 determinantFixed scalarMean
  · exact startupSame_planar_laplacian (originalScalarInverseKernel psi)
      (originalValueKernel planarPartMap (originalCircleKernel covariant)) right force.1 curlMean
  · exact startupSame_third_laplacian axial (originalScalarInverseKernel psi)
      (originalValueKernel toroidalPartMap (originalCircleKernel covariant)) source
      (originalValueKernel planarPartMap (originalCircleKernel covariant)) right
      force.1 thirdFixed force.2.1 scalarMean

end Grad.CartesianStartup
