import AKBP23ActualFirstRowsDivDiv

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- The native compact scalar mean is already sufficient; no extra angular
representative, orbit mean or regularity assumption is introduced. -/
theorem startupSame_weakMean_elliptic (axial : ℤ → ℂ)
    (psi source determinant scalarFlux : StartupL2 1) (covariant : StartupL2 3) (right planarFlux : StartupL2 2)
    (projected : StartupWeakProjectedForceEquation psi (originalValueKernel planarPartMap covariant) right)
    (third : StartupWeakThirdEquation axial (originalScalarInverseKernel psi)
      (originalValueKernel toroidalPartMap covariant) source)
    (determinantRow : StartupWeakDeterminantEquation axial (originalValueKernel planarPartMap covariant)
      (originalValueKernel toroidalPartMap covariant) determinant planarFlux scalarFlux)
    (mean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) psi = 0) :
    let vector := originalValueKernel planarPartMap (originalCircleKernel covariant)
    let scalar := originalValueKernel toroidalPartMap (originalCircleKernel covariant)
    (∀ cell test, startupWeakDivergencePairing vector cell test =
      -startupCoordinateTestPairing cell 0 test determinant - axial cell * startupCoordinateTestPairing cell 0 test scalar +
        axial cell * startupCoordinateTestPairing cell 0 test scalarFlux +
          startupWeakDivergencePairing (planarFlux + (1/2 : ℂ) • originalValueKernel quarterValueMap (originalAverageKernel right)) cell test) ∧
    (∀ cell coordinate test, startupCoordinateTestPairing cell coordinate (startupLaplacianTest test) vector =
      if coordinate = 0 then -startupWeakDivergencePairing vector cell (startupDerivativeTest 0 test) -
        startupWeakCurlPairing right cell (startupTrueInverseTest (startupDerivativeTest 1 test)) -
          (2 : ℂ) * startupWeakDivergencePairing vector cell (startupTrueInverseTest (startupDerivativeTest 1 test))
      else -startupWeakDivergencePairing vector cell (startupDerivativeTest 1 test) +
        startupWeakCurlPairing right cell (startupTrueInverseTest (startupDerivativeTest 0 test)) +
          (2 : ℂ) * startupWeakDivergencePairing vector cell (startupTrueInverseTest (startupDerivativeTest 0 test))) ∧
    (∀ cell test, startupCoordinateTestPairing cell 0 (startupLaplacianTest test) scalar =
      axial cell * startupWeakDivergencePairing (startupRecoveredGradient vector right) cell test +
        startupCoordinateTestPairing cell 0 (startupLaplacianTest test) (startupTrueAngularInverse 1 0 source)) := by
  have force := startupSame_projected_scalarPrimitive_force psi (originalValueKernel planarPartMap covariant) right projected mean
  rw [← startupFullCircle_planar covariant] at force
  have scalarMean := startupSame_fullCircle_scalarMean covariant
  have curlMean := startupSame_fullCircle_curlMean covariant
  have thirdFixed := startupSame_fullCircle_third axial (originalScalarInverseKernel psi) source covariant third
  have determinantFixed := startupSame_fullCircle_determinant axial covariant determinant planarFlux scalarFlux determinantRow
  refine ⟨?_,?_,?_⟩
  · exact startupSame_determinant_divergence axial (originalScalarInverseKernel psi)
      (originalValueKernel toroidalPartMap (originalCircleKernel covariant)) determinant scalarFlux
      (originalValueKernel planarPartMap (originalCircleKernel covariant)) right planarFlux force.1 determinantFixed scalarMean
  · exact startupSame_planar_laplacian (originalScalarInverseKernel psi)
      (originalValueKernel planarPartMap (originalCircleKernel covariant)) right force.1 curlMean
  · exact startupSame_third_laplacian axial (originalScalarInverseKernel psi)
      (originalValueKernel toroidalPartMap (originalCircleKernel covariant)) source
      (originalValueKernel planarPartMap (originalCircleKernel covariant)) right force.1 thirdFixed force.2 scalarMean

theorem startupSame_weakMean_firstRows_divDiv (scale : ℝ)
    (psi knownThird thirdCorrection determinant scalarFlux : StartupL2 1) (covariant : StartupL2 3)
    (knownForce forceCorrection planarFlux : StartupL2 2)
    (scalarMoment scalarFluxMoment : StartupL2 1) (gradientMoment : StartupL2 2)
    (scalarSame : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) scalarMoment
      (originalValueKernel toroidalPartMap (originalCircleKernel covariant)))
    (fluxSame : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) scalarFluxMoment scalarFlux)
    (gradientSame : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) gradientMoment
      (startupRecoveredGradient (originalValueKernel planarPartMap (originalCircleKernel covariant)) (knownForce-forceCorrection)))
    (projected : StartupWeakProjectedForceEquation psi (originalValueKernel planarPartMap covariant) (knownForce-forceCorrection))
    (third : StartupWeakThirdEquation (fun cell => (scale : ℂ) * (Complex.I * (cell : ℂ)))
      (originalScalarInverseKernel psi) (originalValueKernel toroidalPartMap covariant) (knownThird+thirdCorrection))
    (determinantRow : StartupWeakDeterminantEquation (fun cell => (scale : ℂ) * (Complex.I * (cell : ℂ)))
      (originalValueKernel planarPartMap covariant) (originalValueKernel toroidalPartMap covariant) determinant planarFlux scalarFlux)
    (mean : ∀ cell test, startupCoordinateTestPairing cell 0 (startupMeanTest test) psi = 0) :
    StartupWeakDivDivEquation (originalCircleKernel covariant) 0
      (fun outer inside => startupThreeRowTensor forceCorrection thirdCorrection
        (planarFlux - (1/2 : ℂ) • originalValueKernel quarterValueMap (originalAverageKernel forceCorrection)) outer inside +
          startupThreeRowTensor (-knownForce) knownThird (startupERSourceFlux knownForce) outer inside)
      (startupERLowerFlux (startupERLowerScalar scale determinant scalarMoment scalarFluxMoment) (startupAxialField scale gradientMoment)) := by
  have rows := startupSame_weakMean_elliptic (fun cell => (scale : ℂ) * (Complex.I * (cell : ℂ)))
    psi (knownThird+thirdCorrection) determinant scalarFlux covariant (knownForce-forceCorrection) planarFlux
    projected third determinantRow mean
  apply startupERCompact_equation
  · have lowerSplit (cell : ℤ) (test : TestFunction openUnitDisk) :=
      (rows.1 cell test).trans (startupER_divergence_split (fun cell => (scale : ℂ) * (Complex.I * (cell : ℂ)))
        (originalValueKernel toroidalPartMap (originalCircleKernel covariant)) determinant scalarFlux knownForce forceCorrection planarFlux cell test)
    have split := startupERPlanar_split _ knownForce forceCorrection _ _ lowerSplit rows.2.1
    intro cell coordinate test
    have lower : startupERLowerDivergence (fun cell => (scale : ℂ) * (Complex.I * (cell : ℂ)))
        (originalValueKernel toroidalPartMap (originalCircleKernel covariant)) determinant scalarFlux knownForce cell =
        (fun test => startupCoordinateTestPairing cell 0 test (startupERLowerScalar scale determinant scalarMoment scalarFluxMoment) +
          startupWeakDivergencePairing (startupERSourceFlux knownForce) cell test) := by
      funext test
      exact startupERLowerDivergence_L2 scale _ determinant scalarFlux scalarMoment scalarFluxMoment knownForce scalarSame fluxSame cell test
    have identity := split cell coordinate test
    rw [lower] at identity
    exact identity
  · intro cell test
    rw [startupAxialField_divergence scale gradientMoment _ gradientSame]
    have identity := rows.2.2 cell test
    rw [map_add,map_add] at identity
    linear_combination identity

end Grad.CartesianStartup
