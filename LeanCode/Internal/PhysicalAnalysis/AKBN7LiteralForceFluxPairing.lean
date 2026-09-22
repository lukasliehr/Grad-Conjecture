import AKBN1ScaledCompactPairings

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.ActualCartesianWeakEquations Grad.ActualSmoothPhysicalField Grad.RepresentedKernel.SpatialProduct
open Grad.PhysicalFamily Grad.WeightedJets.SpatialMultiplier

theorem startupOriginalForceFlux_pairing (psi : StartupL2 1) (vector : StartupL2 2)
    (cell : ℤ) (coordinate : Fin 2) (test : TestFunction openUnitDisk) :
    (∑ direction : Fin 2, ∫ point in openUnitDisk,
      directionDerivative direction test.toFun point • originalForceFlux (fun point => psi point cell 0)
        (fun point => vector point cell) coordinate direction point) =
      startupCoordinateTestPairing cell 0 (startupDerivativeTest coordinate test) psi -
        startupCoordinateTestPairing cell coordinate (startupRotationTest test) vector := by
  have scalarIntegrable (direction : Fin 2) : IntegrableOn (fun point => directionDerivative direction test.toFun point • psi point cell 0) openUnitDisk :=
    startupCoordinatePairing_integrable psi cell 0 (startupDerivativeTest direction test).toFun
      (startupDerivativeTest direction test).smooth (startupDerivativeTest direction test).compact
  have transportIntegrable (direction : Fin 2) : IntegrableOn (fun point =>
      (directionDerivative direction test.toFun point * angularRotationCoordinate direction point) • vector point cell coordinate) openUnitDisk := by
    let product := multiplyTest (angularRotationCoordinate direction) (angularRotationCoordinate direction).contDiff
      (startupDerivativeTest direction test)
    have integrable := startupCoordinatePairing_integrable vector cell coordinate product.toFun product.smooth product.compact
    change Integrable _ (volume.restrict openUnitDisk)
    simpa only [product,multiplyTest,startupDerivativeTest,mul_comm] using integrable
  have separated (direction : Fin 2) :
      (∫ point in openUnitDisk, directionDerivative direction test.toFun point • originalForceFlux
        (fun point => psi point cell 0) (fun point => vector point cell) coordinate direction point) =
      (if direction = coordinate then startupCoordinateTestPairing cell 0 (startupDerivativeTest direction test) psi else 0) -
        ∫ point in openUnitDisk,
          (directionDerivative direction test.toFun point * angularRotationCoordinate direction point) • vector point cell coordinate := by
    unfold originalForceFlux
    simp only [smul_sub,smul_smul]
    by_cases equal : direction = coordinate
    · simp only [if_pos equal]
      rw [integral_sub (scalarIntegrable direction) (transportIntegrable direction),startupCoordinateTestPairing_apply]
      rfl
    · simp only [if_neg equal,smul_zero,zero_sub,integral_neg]
  simp_rw [separated]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
  congr 1
  rw [Fin.sum_univ_two,← integral_add (transportIntegrable 0) (transportIntegrable 1),startupCoordinateTestPairing_apply]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro point
  change (directionDerivative 0 test.toFun point * angularRotationCoordinate 0 point) • vector point cell coordinate +
    (directionDerivative 1 test.toFun point * angularRotationCoordinate 1 point) • vector point cell coordinate =
      startupRotationDerivative test.toFun point • vector point cell coordinate
  rw [← add_smul]
  apply congrArg (fun scalar : ℝ => scalar • vector point cell coordinate)
  rw [startupRotationDerivative_coordinates,Fin.sum_univ_two]
  norm_num [angularRotationCoordinate,planeQuarterTurn]
  ring

end Grad.CartesianStartup
