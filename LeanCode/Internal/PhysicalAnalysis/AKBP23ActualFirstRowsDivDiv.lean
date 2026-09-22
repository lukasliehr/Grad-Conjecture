import AKBP22SameERCompactTensor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupAxialField_divergence (scale : ℝ) (moment field : StartupL2 2)
    (same : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) moment field)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupWeakDivergencePairing (startupAxialField scale moment) cell test =
      ((scale : ℂ) * (Complex.I * (cell : ℂ))) * startupWeakDivergencePairing field cell test := by
  simp only [startupWeakDivergencePairing,startupAxialField_pairing scale moment field same]
  ring

/-- The genuine projected force, third and determinant compact rows imply a
full L2 div-div equation for SAME Q0(a_C). Native cell moments pay all unknown
axial terms. There is no elliptic equation or H1 premise in this consumer. -/
theorem startupSame_firstRows_divDiv (scale : ℝ)
    (psi knownThird thirdCorrection determinant scalarFlux : StartupL2 1) (covariant : StartupL2 3)
    (knownForce forceCorrection planarFlux : StartupL2 2)
    (scalarMoment scalarFluxMoment : StartupL2 1) (gradientMoment : StartupL2 2)
    (scalarSame : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) scalarMoment
      (originalValueKernel toroidalPartMap (originalCircleKernel covariant)))
    (fluxSame : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) scalarFluxMoment scalarFlux)
    (gradientSame : StartupRadialRelated (fun cell _ => Grad.CellWeights.cellWeight cell) gradientMoment
      (startupRecoveredGradient (originalValueKernel planarPartMap (originalCircleKernel covariant)) (knownForce-forceCorrection)))
    (projected : StartupWeakProjectedForceEquation psi (originalValueKernel planarPartMap covariant)
      (knownForce-forceCorrection))
    (third : StartupWeakThirdEquation (fun cell => (scale : ℂ) * (Complex.I * (cell : ℂ)))
      (originalScalarInverseKernel psi) (originalValueKernel toroidalPartMap covariant) (knownThird+thirdCorrection))
    (determinantRow : StartupWeakDeterminantEquation (fun cell => (scale : ℂ) * (Complex.I * (cell : ℂ)))
      (originalValueKernel planarPartMap covariant) (originalValueKernel toroidalPartMap covariant)
      determinant planarFlux scalarFlux)
    (rawPsi : ℤ → Spatial → PhysicalValue 1)
    (samePsi : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ, psi point cell = rawPsi cell point)
    (psiOrbitMean : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      (∫ angle in Icc (0 : ℝ) (2*Real.pi), rawPsi cell (planeRotationEquiv angle point)) = 0) :
    StartupWeakDivDivEquation (originalCircleKernel covariant) 0
      (fun outer inside =>
        startupThreeRowTensor forceCorrection thirdCorrection
          (planarFlux - (1/2 : ℂ) • originalValueKernel quarterValueMap (originalAverageKernel forceCorrection)) outer inside +
        startupThreeRowTensor (-knownForce) knownThird (startupERSourceFlux knownForce) outer inside)
      (startupERLowerFlux (startupERLowerScalar scale determinant scalarMoment scalarFluxMoment)
        (startupAxialField scale gradientMoment)) := by
  have rows := startupSame_fullCircle_correctedER (fun cell => (scale : ℂ) * (Complex.I * (cell : ℂ)))
    psi knownThird thirdCorrection determinant scalarFlux covariant knownForce forceCorrection planarFlux
    projected third determinantRow rawPsi samePsi psiOrbitMean
  apply startupERCompact_equation
  · intro cell coordinate test
    have identity := rows.1 cell coordinate test
    change startupCoordinateTestPairing cell coordinate (startupLaplacianTest test)
      (originalValueKernel planarPartMap (originalCircleKernel covariant)) = _ at identity
    have lower : startupERLowerDivergence (fun cell => (scale : ℂ) * (Complex.I * (cell : ℂ)))
        (originalValueKernel toroidalPartMap (originalCircleKernel covariant)) determinant scalarFlux knownForce cell =
        (fun test => startupCoordinateTestPairing cell 0 test (startupERLowerScalar scale determinant scalarMoment scalarFluxMoment) +
          startupWeakDivergencePairing (startupERSourceFlux knownForce) cell test) := by
      funext test
      exact startupERLowerDivergence_L2 scale _ determinant scalarFlux scalarMoment scalarFluxMoment knownForce scalarSame fluxSame cell test
    rw [lower] at identity
    exact identity
  · intro cell test
    have identity := rows.2 cell test
    rw [startupAxialField_divergence scale gradientMoment _ gradientSame]
    exact identity

end Grad.CartesianStartup
