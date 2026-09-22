import AKBT17ActualThirdMeanFreeKernel
import AKBN5ScaledProjectionKernels

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.SpatialDilation
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra

theorem startupMomentDilation_add {dimension : ℕ} (scale : Scale) (first second : StartupL2 dimension) :
    startupMomentDilation scale (first+second) = startupMomentDilation scale first+startupMomentDilation scale second := by
  apply startupField_eq_of_coordinatePairing
  intro cell coordinate test
  simp only [map_add,startupCoordinateTestPairing_dilation,smul_add]

theorem startupMomentDilation_sub {dimension : ℕ} (scale : Scale) (first second : StartupL2 dimension) :
    startupMomentDilation scale (first-second) = startupMomentDilation scale first-startupMomentDilation scale second := by
  apply startupField_eq_of_coordinatePairing
  intro cell coordinate test
  simp only [map_sub,startupCoordinateTestPairing_dilation,smul_sub]

theorem startupMomentDilation_smul {dimension : ℕ} (scale : Scale) (scalar : ℂ) (field : StartupL2 dimension) :
    startupMomentDilation scale (scalar • field) = scalar • startupMomentDilation scale field := by
  apply startupField_eq_of_coordinatePairing
  intro cell coordinate test
  simp only [map_smul,startupCoordinateTestPairing_dilation]
  exact smul_comm _ _ _

theorem originalValueKernel_dilation {input output : ℕ}
    (mapping : OperatorValue input output) (scale : Scale) (field : StartupL2 input) :
    startupMomentDilation scale (originalValueKernel mapping field) =
      originalValueKernel mapping (startupMomentDilation scale field) := by
  apply Lp.ext
  filter_upwards [startupMomentDilation_ae scale (originalValueKernel mapping field),
    startupMomentDilation_ae scale field,
    startupDilation_pull_ae scale _ (startupPointKernel_field_ae mapping (LinearIsometryEquiv.refl ℝ _) field),
    startupPointKernel_field_ae mapping (LinearIsometryEquiv.refl ℝ _) (startupMomentDilation scale field)]
    with point outputAt inputAt originalAt scaledAt
  apply lp.ext
  funext cell
  exact (congrArg (fun value : CellValues output => value cell) outputAt).trans
    ((originalAt cell).trans ((congrArg (fun value : CellValues input => mapping (value cell)) inputAt).symm.trans
      (scaledAt cell).symm))

theorem startupCharacterZero_dilation {dimension : ℕ} (scale : Scale) (field : StartupL2 dimension) :
    startupMomentDilation scale (startupCharacterKernel dimension 0 field) =
      startupCharacterKernel dimension 0 (startupMomentDilation scale field) := by
  apply startupField_eq_of_coordinatePairing
  intro cell coordinate test
  rw [startupCoordinateTestPairing_dilation,startupCharacter_zero_pairing,startupCharacter_zero_pairing,
    startupCoordinateTestPairing_dilation,startupPulledTest_mean]

theorem originalAverageKernel_dilation (scale : Scale) (field : StartupL2 2) :
    startupMomentDilation scale (originalAverageKernel field) = originalAverageKernel (startupMomentDilation scale field) := by
  apply startupField_eq_of_coordinatePairing
  intro cell coordinate test
  rw [startupCoordinateTestPairing_dilation,startupAverage_pairing,startupAverage_pairing,Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro target _
  rw [startupCoordinateTestPairing_dilation]
  congr 1
  exact congrArg (fun query => startupCoordinateTestPairing cell target query field)
    (startupPulledTest_angular scale _ _ test).symm

theorem originalScalarMeanFreeKernel_dilation (scale : Scale) (field : StartupL2 1) :
    startupMomentDilation scale (originalScalarMeanFreeKernel field) =
      originalScalarMeanFreeKernel (startupMomentDilation scale field) := by
  change startupMomentDilation scale (field-startupCharacterKernel 1 0 field) = _
  rw [startupMomentDilation_sub,startupCharacterZero_dilation]
  rfl

theorem nativeThirdValueMap : matrixUnit (0 : Fin 1) (2 : Fin 3) = toroidalPartMap := by
  apply ContinuousLinearMap.ext
  intro value
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simp [matrixUnit_apply,operatorBasis,toroidalPartMap,LinearMap.toContinuousLinearMap]

end Grad.CartesianStartup
