import AKBN7LiteralForceFluxPairing
import AKBJ15ThirdAngularFlux

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets
open Grad.RepresentedKernel.SpatialProduct Grad.WeightedJets.SpatialMultiplier
open Grad.PhysicalFamily Grad.ActualScalarWeakEquations Grad.ActualSmoothPhysicalField

theorem startupAngularTransport_pairing {dimension : ℕ} (field : StartupL2 dimension)
    (cell : ℤ) (coordinate : Fin dimension) (test : TestFunction openUnitDisk) :
    (∑ direction : Fin 2, ∫ point in openUnitDisk,
      (directionDerivative direction test.toFun point * angularRotationCoordinate direction point) • field point cell coordinate) =
      startupCoordinateTestPairing cell coordinate (startupRotationTest test) field := by
  have integrable (direction : Fin 2) : Integrable (fun point =>
      (directionDerivative direction test.toFun point * angularRotationCoordinate direction point) • field point cell coordinate)
      (volume.restrict openUnitDisk) := by
    let product := multiplyTest (angularRotationCoordinate direction) (angularRotationCoordinate direction).contDiff
      (startupDerivativeTest direction test)
    simpa only [product,multiplyTest,startupDerivativeTest,mul_comm] using
      startupCoordinatePairing_integrable field cell coordinate product.toFun product.smooth product.compact
  rw [Fin.sum_univ_two,← integral_add (integrable 0) (integrable 1),startupCoordinateTestPairing_apply]
  apply integral_congr_ae
  filter_upwards [] with point
  change (directionDerivative 0 test.toFun point * angularRotationCoordinate 0 point) • field point cell coordinate +
    (directionDerivative 1 test.toFun point * angularRotationCoordinate 1 point) • field point cell coordinate =
      startupRotationDerivative test.toFun point • field point cell coordinate
  rw [← add_smul]
  apply congrArg (fun scalar : ℝ => scalar • field point cell coordinate)
  rw [startupRotationDerivative_coordinates,Fin.sum_univ_two]
  norm_num [angularRotationCoordinate,planeQuarterTurn]
  ring

end Grad.CartesianStartup
