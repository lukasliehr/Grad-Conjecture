import AKBP3PrincipalCoordinatePairings

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger Grad.WeightedJets

theorem startupPrincipalWeak_planar (force flux : StartupL2 2) (scalar : StartupL2 1)
    (cell : ℤ) (coordinate : Fin 2) (test : TestFunction openUnitDisk) :
    startupPrincipalWeakExpression cell (EuclideanSpace.single coordinate.castSucc 1) test
      (originalValueKernel planarInclusionMap force) (originalValueKernel toroidalInclusionMap scalar)
      (originalValueKernel planarInclusionMap flux) = startupERPlanarPrincipal force flux cell coordinate test := by
  unfold startupPrincipalWeakExpression
  simp only [startupPrincipalEntry_pairing, startupPrincipalRotatedEntry_pairing, startupToroidalEmbedding_pairing,
    Fin.sum_univ_two, smul_eq_mul]
  fin_cases coordinate <;>
    norm_num [Fin.ext_iff, startupERPlanarPrincipal, startupWeakDivergencePairing, startupWeakCurlPairing] <;> ring

theorem startupCoordinate_trueInverse_apply {dimension : ℕ} (field : StartupL2 dimension)
    (cell : ℤ) (coordinate : Fin dimension) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate test (startupTrueAngularInverse dimension 0 field) =
      startupCoordinateTestPairing cell coordinate (startupTrueInverseTest test) field :=
  congrArg (fun operator : StartupL2 dimension →L[ℂ] ℂ => operator field)
    (startupCoordinateTestPairing_trueInverse cell coordinate test)

theorem startupPrincipalWeak_scalar (force flux : StartupL2 2) (scalar : StartupL2 1)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupPrincipalWeakExpression cell (EuclideanSpace.single 2 1) test
      (originalValueKernel planarInclusionMap force) (originalValueKernel toroidalInclusionMap scalar)
      (originalValueKernel planarInclusionMap flux) =
        startupCoordinateTestPairing cell 0 (startupLaplacianTest test) (startupTrueAngularInverse 1 0 scalar) := by
  unfold startupPrincipalWeakExpression
  simp only [startupPrincipalEntry_pairing, startupPrincipalRotatedEntry_pairing, startupToroidalEmbedding_pairing,
    Fin.sum_univ_two, smul_eq_mul]
  norm_num [Fin.ext_iff]
  rw [startupLaplacianTest, startupCoordinateTestPairing_add, add_apply]
  rw [startupCoordinate_trueInverse_apply, startupCoordinate_trueInverse_apply]

end Grad.CartesianStartup
