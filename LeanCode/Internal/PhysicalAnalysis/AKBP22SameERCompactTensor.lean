import AKBP21CoordinateDivDivAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem startupPlanarPart_pairing (field : StartupL2 3)
    (cell : ℤ) (coordinate : Fin 2) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell coordinate test (originalValueKernel planarPartMap field) =
      startupCoordinateTestPairing cell coordinate.castSucc test field := by
  have same := startupCoordinate_value_component planarPartMap coordinate coordinate.castSucc 1
    (fun value => by fin_cases coordinate <;> simp [planarPartMap,LinearMap.toContinuousLinearMap]) field cell test
  simpa only [one_mul] using same

theorem startupToroidalPart_pairing (field : StartupL2 3)
    (cell : ℤ) (test : TestFunction openUnitDisk) :
    startupCoordinateTestPairing cell 0 test (originalValueKernel toroidalPartMap field) =
      startupCoordinateTestPairing cell 2 test field := by
  have same := startupCoordinate_value_component toroidalPartMap 0 2 1
    (fun value => by simp [toroidalPartMap,LinearMap.toContinuousLinearMap]) field cell test
  simpa only [one_mul] using same

/-- Literal full-vector assembly of the corrected ER rows. The known-source
tensor remains separate, so its already proved first graph pays its derivative. -/
theorem startupERCompact_equation (field : StartupL2 3) (force flux knownForce : StartupL2 2)
    (correction knownThird lower : StartupL2 1) (axialGradient : StartupL2 2)
    (planar : ∀ cell coordinate test,
      startupCoordinateTestPairing cell coordinate (startupLaplacianTest test) (originalValueKernel planarPartMap field) =
        startupERPlanarPrincipal force flux cell coordinate test +
          startupERPlanarRemainder
            (fun test => startupCoordinateTestPairing cell 0 test lower +
              startupWeakDivergencePairing (startupERSourceFlux knownForce) cell test) knownForce cell coordinate test)
    (scalar : ∀ cell test,
      startupCoordinateTestPairing cell 0 (startupLaplacianTest test) (originalValueKernel toroidalPartMap field) =
        startupCoordinateTestPairing cell 0 (startupLaplacianTest test) (startupTrueAngularInverse 1 0 correction) +
          (startupWeakDivergencePairing axialGradient cell test +
            startupCoordinateTestPairing cell 0 (startupLaplacianTest test) (startupTrueAngularInverse 1 0 knownThird))) :
    StartupWeakDivDivEquation field 0
      (fun outer inside => startupThreeRowTensor force correction flux outer inside +
        startupThreeRowTensor (-knownForce) knownThird (startupERSourceFlux knownForce) outer inside)
      (startupERLowerFlux lower axialGradient) := by
  apply startupDivDiv_of_coordinates
  intro cell coordinate test
  simp only [map_add,map_zero,Finset.sum_add_distrib,add_zero]
  have planarEquation (index : Fin 2) := planar cell index test
  have scalarEquation := scalar cell test
  simp only [startupPlanarPart_pairing] at planarEquation
  rw [startupToroidalPart_pairing] at scalarEquation
  refine Fin.lastCases ?_ (fun index => ?_) coordinate
  · rw [show Fin.last 2 = (2 : Fin 3) by decide]
    have first := startupThreeRowTensor_scalar force flux correction cell test
    have second := startupThreeRowTensor_scalar (-knownForce) (startupERSourceFlux knownForce) knownThird cell test
    have third := startupERLowerFlux_scalar lower axialGradient cell test
    linear_combination scalarEquation - first - second - third
  · have identity := planarEquation index
    rw [startupERPlanarRemainder_L2 lower knownForce axialGradient cell index test] at identity
    have first := startupThreeRowTensor_planar force flux correction cell index test
    have second := startupThreeRowTensor_planar (-knownForce) (startupERSourceFlux knownForce) knownThird cell index test
    linear_combination identity - first - second

end Grad.CartesianStartup
