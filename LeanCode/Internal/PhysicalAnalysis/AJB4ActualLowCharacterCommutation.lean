import AJB3ActualNormalizedLowOrbitDerivative
import AIZ4CompleteCoupledUnitary

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularCoupledOrbit Grad.AnnularCurrentEnergy Grad.AnnularLowReference

/-- The original retained-mode character, with the same analytic width. -/
def lowModeTranslation (lower : ℝ) (tau : OrbitParameter) : LowModeBulk lower →L[ℂ] LowModeBulk lower :=
  complexLpTwoMap (fun mode : LowAnnularMode =>
    orbitCharacter tau mode.val • ContinuousLinearMap.id ℂ (RadialL2 1 lower)) 1 (by norm_num)
    (fun mode field => by
      change ‖orbitCharacter tau mode.val • field‖ ≤ 1 * ‖field‖
      rw [norm_smul, orbitCharacter_norm])

theorem lowModeTranslation_apply (lower : ℝ) (tau : OrbitParameter) (field : LowModeBulk lower)
    (mode : LowAnnularMode) : lowModeTranslation lower tau field mode = orbitCharacter tau mode.val • field mode := rfl

theorem lowComponent_translation (lower : ℝ) (tau : OrbitParameter) (row : Fin 2) (field : LowEnergyBulk lower) :
    lowComponent lower row (lowBulkTranslation lower tau field) =
      lowModeTranslation lower tau (lowComponent lower row field) := by
  apply lp.ext
  funext mode
  rfl

theorem lowModeScalarFamily_translation (lower : ℝ) (tau : OrbitParameter)
    (coefficient : LowAnnularMode → C(ℝ, ℝ)) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ mode radius, radius ∈ Icc lower 1 → |coefficient mode radius| ≤ bound)
    (field : LowModeBulk lower) :
    lowModeScalarFamily lower coefficient bound nonnegative bounded (lowModeTranslation lower tau field) =
      lowModeTranslation lower tau (lowModeScalarFamily lower coefficient bound nonnegative bounded field) := by
  apply lp.ext
  funext mode
  exact (scalarRadialMap lower (coefficient mode) bound (bounded mode)).map_smul (orbitCharacter tau mode.val) (field mode)

/-- Exact zero extension off the four original low angular modes commutes. -/
theorem lowBulkIntoFull_translation (lower : ℝ) (tau : OrbitParameter) (field : LowModeBulk lower) :
    lowBulkIntoFull lower (lowModeTranslation lower tau field) =
      orbitLpAction (RadialL2 1 lower) tau (lowBulkIntoFull lower field) := by
  apply lp.ext
  funext mode
  rw [orbitLpAction_apply]
  by_cases retained : |mode.1| = 1 ∨ |mode.1| = 2
  · change lowBulkIntoFull lower (lowModeTranslation lower tau field) (⟨mode, retained⟩ : LowAnnularMode).val = _
    rw [lowBulkIntoFull_retained, lowModeTranslation_apply,
      lowBulkIntoFull_retained lower field ⟨mode, retained⟩]
  · rw [lowBulkIntoFull_outside lower _ mode retained, lowBulkIntoFull_outside lower _ mode retained, smul_zero]

theorem bulkMatrixUnit_translation {input output : ℕ} (lower : ℝ) (tau : OrbitParameter)
    (row : Fin output) (column : Fin input) (field : DivisionRow input lower) :
    bulkMatrixUnit lower row column (orbitLpAction (RadialL2 input lower) tau field) =
      orbitLpAction (RadialL2 output lower) tau (bulkMatrixUnit lower row column field) := by
  apply lp.ext
  funext mode
  exact (radialMatrixUnit lower row column).map_smul (orbitCharacter tau mode) (field mode)

theorem lowBulkSlot_translation {dimension : ℕ} (lower : ℝ) (tau : OrbitParameter)
    (slot : Fin dimension) (field : LowModeBulk lower) :
    lowBulkSlot lower slot (lowModeTranslation lower tau field) =
      orbitLpAction (RadialL2 dimension lower) tau (lowBulkSlot lower slot field) := by
  change bulkMatrixUnit lower slot 0 (lowBulkIntoFull lower (lowModeTranslation lower tau field)) = _
  rw [lowBulkIntoFull_translation, bulkMatrixUnit_translation]
  rfl

theorem lowNormalizedRadius_translation (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (tau : OrbitParameter) (field : LowEnergyBulk lower) :
    lowNormalizedRadius parameters lower length positive (lowBulkTranslation lower tau field) =
      lowModeTranslation lower tau (lowNormalizedRadius parameters lower length positive field) := by
  unfold lowNormalizedRadius
  simp only [ContinuousLinearMap.comp_apply, lowComponent_translation, lowModeScalarFamily_translation]

theorem lowNormalizedCell_translation (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (tau : OrbitParameter) (field : LowEnergyBulk lower) :
    lowNormalizedCell parameters lower length lengthPositive positive (lowBulkTranslation lower tau field) =
      lowModeTranslation lower tau (lowNormalizedCell parameters lower length lengthPositive positive field) := by
  unfold lowNormalizedCell
  simp only [ContinuousLinearMap.comp_apply, smul_apply, lowComponent_translation, lowModeScalarFamily_translation, map_smul]

theorem lowNormalizedAngular_translation (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (tau : OrbitParameter) (field : LowEnergyBulk lower) :
    lowNormalizedAngular parameters lower length positive (lowBulkTranslation lower tau field) =
      lowModeTranslation lower tau (lowNormalizedAngular parameters lower length positive field) := by
  unfold lowNormalizedAngular
  simp only [ContinuousLinearMap.comp_apply, smul_apply, lowComponent_translation, lowModeScalarFamily_translation, map_smul]

/-- Actual seven-slot rho-stored input, including fixed radial multipliers. -/
theorem lowNormalizedSevenInput_translation (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (tau : OrbitParameter) (field : LowEnergyBulk lower) :
    lowNormalizedSevenInput parameters lower length lengthPositive positive (lowBulkTranslation lower tau field) =
      orbitLpAction (RadialL2 7 lower) tau (lowNormalizedSevenInput parameters lower length lengthPositive positive field) := by
  unfold lowNormalizedSevenInput
  simp only [add_apply, ContinuousLinearMap.comp_apply, map_add, lowComponent_translation,
    lowNormalizedAngular_translation, lowNormalizedCell_translation, lowNormalizedRadius_translation,
    lowBulkSlot_translation]

theorem lowFullRestriction_translation (lower : ℝ) (tau : OrbitParameter) (field : DivisionRow 1 lower) :
    lowFullRestriction lower (orbitLpAction (RadialL2 1 lower) tau field) =
      lowModeTranslation lower tau (lowFullRestriction lower field) := by
  apply lp.ext
  funext mode
  rfl

theorem lowRowIntoBulk_translation (lower : ℝ) (tau : OrbitParameter) (row : Fin 2) (field : LowModeBulk lower) :
    lowRowIntoBulk lower row (lowModeTranslation lower tau field) =
      lowBulkTranslation lower tau (lowRowIntoBulk lower row field) := by
  apply lp.ext
  funext index
  change (if index.1 = row then lowModeTranslation lower tau field index.2 else 0) =
    orbitCharacter tau index.2.val • (if index.1 = row then field index.2 else 0)
  by_cases same : index.1 = row <;> simp only [same, if_true, if_false, lowModeTranslation_apply, smul_zero]

theorem lowOutputMap_translation (lower : ℝ) (tau : OrbitParameter) (row : Fin 2)
    (coefficient : LowAnnularMode → C(ℝ, ℝ)) (bound : ℝ) (nonnegative : 0 ≤ bound)
    (bounded : ∀ mode radius, radius ∈ Icc lower 1 → |coefficient mode radius| ≤ bound)
    (field : DivisionRow 1 lower) :
    lowOutputMap lower row coefficient bound nonnegative bounded (orbitLpAction (RadialL2 1 lower) tau field) =
      lowBulkTranslation lower tau (lowOutputMap lower row coefficient bound nonnegative bounded field) := by
  unfold lowOutputMap
  simp only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    lowFullRestriction_translation, lowModeScalarFamily_translation, lowRowIntoBulk_translation]

theorem lowFirstOutput_translation (parameters : PhaseParameters) (lower length : ℝ)
    (tau : OrbitParameter) (field : DivisionRow 1 lower) :
    lowFirstOutput parameters lower length (orbitLpAction (RadialL2 1 lower) tau field) =
      lowBulkTranslation lower tau (lowFirstOutput parameters lower length field) :=
  lowOutputMap_translation _ _ _ _ _ _ _ _

theorem lowCellOutput_translation (lower length : ℝ) (positive : 0 < lower)
    (tau : OrbitParameter) (field : DivisionRow 1 lower) :
    lowCellOutput lower length positive (orbitLpAction (RadialL2 1 lower) tau field) =
      lowBulkTranslation lower tau (lowCellOutput lower length positive field) := by
  unfold lowCellOutput
  simp only [smul_apply, lowOutputMap_translation, map_smul]

theorem lowAngularOutput_translation (lower length : ℝ) (positive : 0 < lower)
    (tau : OrbitParameter) (field : DivisionRow 1 lower) :
    lowAngularOutput lower length positive (orbitLpAction (RadialL2 1 lower) tau field) =
      lowBulkTranslation lower tau (lowAngularOutput lower length positive field) := by
  unfold lowAngularOutput
  simp only [smul_apply, lowOutputMap_translation, map_smul]

theorem lowCommonDiagonal_translation (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (tau : OrbitParameter) (field : LowEnergyBulk lower) :
    lowCommonDiagonal parameters length lower lengthPositive positive (lowBulkTranslation lower tau field) =
      lowBulkTranslation lower tau (lowCommonDiagonal parameters length lower lengthPositive positive field) := by
  apply lp.ext
  funext index
  exact (scalarRadialMap lower (lowCommonDiagonalCurve parameters length lower positive index)
    (lowReferenceCoefficientConstant parameters length + 2)
    (lowCommonDiagonalCurve_bound parameters length lower lengthPositive positive index)).map_smul
      (orbitCharacter tau index.2.val) (field index)

end Grad.AnnularLowOrbit
