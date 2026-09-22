import AKBP20LiteralLowerOrderFlux
import AKBP8SamePhaseDivDivEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupTestPairing_coordinates (cell : ℤ) (vector : PhysicalValue 3)
    (test : TestFunction openUnitDisk) (field : StartupL2 3) :
    startupTestPairing cell vector test field =
      ∑ coordinate : Fin 3, star (vector coordinate) * startupCoordinateTestPairing cell coordinate test field := by
  rw [startupTestPairing_apply]
  simp_rw [PiLp.inner_apply,RCLike.inner_apply,Finset.smul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro coordinate _
    rw [startupCoordinateTestPairing_apply,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with point
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_eq_mul,starRingEnd_apply]
    ring
  · intro coordinate _
    have bound := (startupCoordinatePairing_integrable field cell coordinate test.toFun test.smooth test.compact).const_mul
      (star (vector coordinate))
    convert bound using 1
    funext point
    simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),smul_eq_mul,starRingEnd_apply]
    ring

theorem startupDivDiv_of_coordinates (field zeroth : StartupL2 3)
    (tensor : Fin 2 → Fin 2 → StartupL2 3) (flux : Fin 2 → StartupL2 3)
    (equation : ∀ cell coordinate test,
      startupCoordinateTestPairing cell coordinate (startupLaplacianTest test) field =
        (∑ outer : Fin 2, ∑ inside : Fin 2,
          startupCoordinateTestPairing cell coordinate (startupDerivativeTest outer (startupDerivativeTest inside test))
            (tensor outer inside)) + startupCoordinateTestPairing cell coordinate test zeroth +
        ∑ direction : Fin 2, startupCoordinateTestPairing cell coordinate (startupDerivativeTest direction test) (flux direction)) :
    StartupWeakDivDivEquation field zeroth tensor flux := by
  intro cell vector test
  simp_rw [startupTestPairing_coordinates]
  have first := equation cell 0 test
  have second := equation cell 1 test
  have third := equation cell 2 test
  simp only [Fin.sum_univ_three,Fin.sum_univ_two] at first second third ⊢
  linear_combination star (vector 0) * first + star (vector 1) * second + star (vector 2) * third

def startupThreeRowTensor (force : StartupL2 2) (scalar : StartupL2 1) (flux : StartupL2 2)
    (outer inside : Fin 2) : StartupL2 3 :=
  ∑ row : Fin 3, startupPrincipalFixedKernel outer inside row
    (![originalValueKernel planarInclusionMap force,originalValueKernel toroidalInclusionMap scalar,
      originalValueKernel planarInclusionMap flux] row)

theorem startupThreeRowTensor_planar (force flux : StartupL2 2) (scalar : StartupL2 1)
    (cell : ℤ) (coordinate : Fin 2) (test : TestFunction openUnitDisk) :
    (∑ outer : Fin 2, ∑ inside : Fin 2,
      startupCoordinateTestPairing cell coordinate.castSucc (startupDerivativeTest outer (startupDerivativeTest inside test))
        (startupThreeRowTensor force scalar flux outer inside)) = startupERPlanarPrincipal force flux cell coordinate test := by
  have mixed := startupPrincipalRows_mixedWeak cell (EuclideanSpace.single coordinate.castSucc 1) test
    ![originalValueKernel planarInclusionMap force,originalValueKernel toroidalInclusionMap scalar,
      originalValueKernel planarInclusionMap flux]
  change _ = startupPrincipalWeakExpression cell (EuclideanSpace.single coordinate.castSucc 1) test
    (originalValueKernel planarInclusionMap force) (originalValueKernel toroidalInclusionMap scalar)
    (originalValueKernel planarInclusionMap flux) at mixed
  rw [startupPrincipalWeak_planar] at mixed
  simpa only [startupThreeRowTensor,startupCoordinateTestPairing,startupTestPairing,
    startupDerivativeTest_commute] using mixed

theorem startupThreeRowTensor_scalar (force flux : StartupL2 2) (scalar : StartupL2 1)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    (∑ outer : Fin 2, ∑ inside : Fin 2,
      startupCoordinateTestPairing cell 2 (startupDerivativeTest outer (startupDerivativeTest inside test))
        (startupThreeRowTensor force scalar flux outer inside)) =
      startupCoordinateTestPairing cell 0 (startupLaplacianTest test) (startupTrueAngularInverse 1 0 scalar) := by
  have mixed := startupPrincipalRows_mixedWeak cell (EuclideanSpace.single 2 1) test
    ![originalValueKernel planarInclusionMap force,originalValueKernel toroidalInclusionMap scalar,
      originalValueKernel planarInclusionMap flux]
  change _ = startupPrincipalWeakExpression cell (EuclideanSpace.single 2 1) test
    (originalValueKernel planarInclusionMap force) (originalValueKernel toroidalInclusionMap scalar)
    (originalValueKernel planarInclusionMap flux) at mixed
  rw [startupPrincipalWeak_scalar] at mixed
  simpa only [startupThreeRowTensor,startupCoordinateTestPairing,startupTestPairing,
    startupDerivativeTest_commute] using mixed

end Grad.CartesianStartup
