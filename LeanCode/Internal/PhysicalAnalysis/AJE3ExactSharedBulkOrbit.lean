import AJE2ExactSourceTraceOrbit
import AIY15ExactSharedStrongDataConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.AnnularStrongData Grad.AnnularHighTilt

/-- Value and genuine radial derivative coordinates of the same graph
both transform by the same Fourier character. -/
theorem annularSourceCoordinate_translation (parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (angular cell : ℕ) (coordinate : Fin 2) (tau : OrbitParameter)
    (field : AnnularSourceH1 parameters dimension lower angular cell) :
    annularSourceCoordinate parameters dimension lower angular cell coordinate
      (sourceGraphTranslation dimension lower tau field) =
      orbitLpAction (RadialL2 dimension lower) tau
        (annularSourceCoordinate parameters dimension lower angular cell coordinate field) := by
  apply lp.ext
  funext mode
  rw [annularSourceCoordinate_apply,sourceGraphTranslation_apply,sourceGraphScalar_coordinate,
    orbitLpAction_apply,annularSourceCoordinate_apply]

theorem bulkInclusion_translation (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (lowAngular lowCell highAngular highCell : ℕ) (angularLe : lowAngular ≤ highAngular)
    (cellLe : lowCell ≤ highCell) (tau : OrbitParameter)
    (field : AnnularSourceBulk parameters dimension lower highAngular highCell) :
    annularBulkInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe
      (orbitLpAction (RadialL2 dimension lower) tau field) =
      orbitLpAction (RadialL2 dimension lower) tau
        (annularBulkInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe field) := by
  apply lp.ext
  funext mode
  change sourceGradeRatio lowAngular lowCell highAngular highCell mode • (orbitCharacter tau mode • field mode) =
    orbitCharacter tau mode • (sourceGradeRatio lowAngular lowCell highAngular highCell mode • field mode)
  exact smul_comm _ _ _

theorem sourceAngularBulk_translation (lower : ℝ) (tau : OrbitParameter) (field : DivisionRow 1 lower) :
    sourceAngularBulk lower (orbitLpAction (RadialL2 1 lower) tau field) =
      orbitLpAction (RadialL2 1 lower) tau (sourceAngularBulk lower field) := by
  apply lp.ext
  funext mode
  rw [sourceAngularBulk_mode,orbitLpAction_apply,orbitLpAction_apply,sourceAngularBulk_mode]
  exact smul_comm _ _ _

theorem unweightedSourceF0Bulk_translation (parameters : PhaseParameters) (lower : ℝ)
    (tau : OrbitParameter) (field : HighF0SourceGraph parameters lower) :
    unweightedSourceF0Bulk parameters lower (sourceGraphTranslation 1 lower tau field) =
      orbitLpAction (RadialL2 1 lower) tau (unweightedSourceF0Bulk parameters lower field) := by
  change annularBulkInclusion parameters 1 lower 0 0 1 0 (by omega) (by omega)
      (annularSourceCoordinate parameters 1 lower 1 0 0 (sourceGraphTranslation 1 lower tau field)) = _
  rw [annularSourceCoordinate_translation,bulkInclusion_translation]
  rfl

theorem unweightedSourceRF0Bulk_translation (parameters : PhaseParameters) (lower : ℝ)
    (tau : OrbitParameter) (field : HighF0SourceGraph parameters lower) :
    unweightedSourceRF0Bulk parameters lower (sourceGraphTranslation 1 lower tau field) =
      orbitLpAction (RadialL2 1 lower) tau (unweightedSourceRF0Bulk parameters lower field) := by
  change sourceAngularBulk lower
      (annularSourceCoordinate parameters 1 lower 1 0 0 (sourceGraphTranslation 1 lower tau field)) = _
  rw [annularSourceCoordinate_translation,sourceAngularBulk_translation]
  rfl

theorem unweightedSourceF2Bulk_translation (parameters : PhaseParameters) (lower : ℝ)
    (tau : OrbitParameter) (field : HighF2SourceGraph parameters lower) :
    unweightedSourceF2Bulk parameters lower (sourceGraphTranslation 1 lower tau field) =
      orbitLpAction (RadialL2 1 lower) tau (unweightedSourceF2Bulk parameters lower field) :=
  annularSourceCoordinate_translation parameters 1 lower 0 0 0 tau field

/-- The exact original radial tilt commutes with physical angular/cell
translation. No derivative of the tilt or extra collar cost is introduced. -/
theorem divisionHighWeight_translation (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (tau : OrbitParameter) (field : DivisionRow 1 lower) :
    divisionHighWeight lower positive bounded (orbitLpAction (RadialL2 1 lower) tau field) =
      orbitLpAction (RadialL2 1 lower) tau (divisionHighWeight lower positive bounded field) := by
  apply lp.ext
  funext mode
  change scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
      (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)
      (orbitCharacter tau mode • field mode) =
    orbitCharacter tau mode • scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
      (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded) (field mode)
  exact map_smul _ _ _

theorem divisionHighUnweight_translation (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (tau : OrbitParameter) (field : DivisionRow 1 lower) :
    divisionHighUnweight lower positive bounded (orbitLpAction (RadialL2 1 lower) tau field) =
      orbitLpAction (RadialL2 1 lower) tau (divisionHighUnweight lower positive bounded field) := by
  apply lp.ext
  funext mode
  change scalarRadialMap lower (highPowerCurve lower highTiltExponent positive)
      1 (highPositivePower_bound lower positive bounded) (orbitCharacter tau mode • field mode) =
    orbitCharacter tau mode • scalarRadialMap lower (highPowerCurve lower highTiltExponent positive)
      1 (highPositivePower_bound lower positive bounded) (field mode)
  exact map_smul _ _ _

end Grad.AnnularStrongOrbit
