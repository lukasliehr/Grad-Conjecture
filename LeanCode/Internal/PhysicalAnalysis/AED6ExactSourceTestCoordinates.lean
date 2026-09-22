import AED5ExactTraceTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.AnnularTiltedReference
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularHighTilt Grad.AnnularReconstruction
open Grad.AnnularFluxTrace Grad.CartesianState Grad.SourceCollarDivision

section Coordinates
variable (lower length : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)

theorem highEnergyUnweight_value (field : annularEnergySpace lower length positive) :
    annularEnergyValue lower length positive (highEnergyUnweight lower length positive bounded field) =
      highBulkUnweight lower positive bounded (annularEnergyValue lower length positive field) := by
  apply lp.ext
  funext mode
  change annularValueMassMap lower length positive mode
    (annularEnergyMass lower length positive (highEnergyUnweight lower length positive bounded field) mode) = _
  rw [highEnergyUnweight_mass_apply]
  exact scalarRadialMap_comm lower (annularValueMassRatio lower length positive mode)
    (highPowerCurve lower highTiltExponent positive) (1 / 3) 1
    (annularValueMassRatio_bound lower length positive mode) (highPositivePower_bound lower positive bounded) _

theorem highEnergyUnweight_radial (field : annularEnergySpace lower length positive) :
    annularEnergyRadial lower length positive (highEnergyUnweight lower length positive bounded field) =
      highBulkUnweight lower positive bounded (annularEnergyRadial lower length positive field) := by
  apply lp.ext
  funext mode
  change annularRadialMassMap lower length positive mode
    (annularEnergyMass lower length positive (highEnergyUnweight lower length positive bounded field) mode) = _
  rw [highEnergyUnweight_mass_apply]
  exact scalarRadialMap_comm lower (annularRadialMassRatio lower length positive mode)
    (highPowerCurve lower highTiltExponent positive) (2 / 3) 1
    (annularRadialMassRatio_bound lower length positive mode) (highPositivePower_bound lower positive bounded) _

theorem highEnergyWeight_value (field : annularEnergySpace lower length positive) :
    annularEnergyValue lower length positive (highEnergyWeight lower length positive bounded field) =
      highBulkWeight lower positive bounded (annularEnergyValue lower length positive field) := by
  apply lp.ext
  funext mode
  change annularValueMassMap lower length positive mode
    (annularEnergyMass lower length positive (highEnergyWeight lower length positive bounded field) mode) = _
  rw [highEnergyWeight_mass_apply]
  exact scalarRadialMap_comm lower (annularValueMassRatio lower length positive mode)
    (highPowerCurve lower (-highTiltExponent) positive) (1 / 3) (lower ^ (-highTiltExponent))
    (annularValueMassRatio_bound lower length positive mode) (highNegativePower_bound lower positive bounded) _

theorem highEnergyWeight_radial (field : annularEnergySpace lower length positive) :
    annularEnergyRadial lower length positive (highEnergyWeight lower length positive bounded field) =
      highBulkWeight lower positive bounded (annularEnergyRadial lower length positive field) := by
  apply lp.ext
  funext mode
  change annularRadialMassMap lower length positive mode
    (annularEnergyMass lower length positive (highEnergyWeight lower length positive bounded field) mode) = _
  rw [highEnergyWeight_mass_apply]
  exact scalarRadialMap_comm lower (annularRadialMassRatio lower length positive mode)
    (highPowerCurve lower (-highTiltExponent) positive) (2 / 3) (lower ^ (-highTiltExponent))
    (annularRadialMassRatio_bound lower length positive mode) (highNegativePower_bound lower positive bounded) _

theorem highEnergyWeight_d (field : annularEnergySpace lower length positive) :
    annularEnergyD lower length positive (highEnergyWeight lower length positive bounded field) =
      highBulkWeight lower positive bounded (annularEnergyD lower length positive field) := by
  apply lp.ext
  funext mode
  change annularEnergyD lower length positive (highEnergyWeight lower length positive bounded field) mode = _
  rw [annularEnergyD_mode]
  have value := congrArg (fun bulk : AnnularBulk lower => bulk mode)
    (highEnergyWeight_value lower length positive bounded field)
  rw [value]
  change (annularDSymbol mode) • scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
    (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
      (annularEnergyValue lower length positive field mode) =
    scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
      (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
        (annularEnergyD lower length positive field mode)
  rw [annularEnergyD_mode, map_smul]

theorem highEnergyWeight_cell (field : annularEnergySpace lower length positive) :
    annularEnergyCell lower length positive (highEnergyWeight lower length positive bounded field) =
      highBulkWeight lower positive bounded (annularEnergyCell lower length positive field) := by
  apply lp.ext
  funext mode
  change annularEnergyCell lower length positive (highEnergyWeight lower length positive bounded field) mode = _
  rw [annularEnergyCell_mode]
  have value := congrArg (fun bulk : AnnularBulk lower => bulk mode)
    (highEnergyWeight_value lower length positive bounded field)
  rw [value]
  change (annularCellSymbol length mode) • scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
    (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
      (annularEnergyValue lower length positive field mode) =
    scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
      (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
        (annularEnergyCell lower length positive field mode)
  rw [annularEnergyCell_mode, map_smul]

end Coordinates
end Grad.AnnularTiltedReference
