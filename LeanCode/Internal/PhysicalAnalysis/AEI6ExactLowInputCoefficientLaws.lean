import AEI5ActualLowSevenInputPacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

theorem lowNormalizedRadius_ae (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (field : LowEnergyBulk lower) (mode : LowAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowNormalizedRadius parameters lower length positive field mode radius =
        lowInputRadiusCurve parameters lower length positive mode radius • field (0, mode) radius :=
  lowModeScalarFamily_ae lower (lowInputRadiusCurve parameters lower length positive) 2 (by norm_num)
    (fun mode radius _ => lowInputRadiusCurve_bound parameters lower length positive mode radius) (lowComponent lower 0 field) mode

theorem lowNormalizedCell_ae (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (field : LowEnergyBulk lower) (mode : LowAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowNormalizedCell parameters lower length lengthPositive positive field mode radius =
        Complex.I • (lowInputCellCurve parameters lower length positive mode radius • field (0, mode) radius) := by
  let base := lowModeScalarFamily lower (lowInputCellCurve parameters lower length positive) (2 * length) (by positivity)
    (fun mode radius _ => lowInputCellCurve_bound parameters lower length lengthPositive positive mode radius) (lowComponent lower 0 field)
  have actual := lowModeScalarFamily_ae lower (lowInputCellCurve parameters lower length positive) (2 * length) (by positivity)
    (fun mode radius _ => lowInputCellCurve_bound parameters lower length lengthPositive positive mode radius) (lowComponent lower 0 field) mode
  filter_upwards [actual, Lp.coeFn_smul Complex.I (base mode)] with radius actual scaled
  change (Complex.I • base mode) radius = _
  rw [scaled]
  change Complex.I • base mode radius = _
  rw [actual]
  rfl

theorem lowNormalizedAngular_ae (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (field : LowEnergyBulk lower) (mode : LowAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowNormalizedAngular parameters lower length positive field mode radius =
        Complex.I • (lowInputAngularCurve parameters lower length positive mode radius • field (0, mode) radius) := by
  let base := lowModeScalarFamily lower (lowInputAngularCurve parameters lower length positive) 4 (by norm_num)
    (fun mode radius _ => lowInputAngularCurve_bound parameters lower length positive mode radius) (lowComponent lower 0 field)
  have actual := lowModeScalarFamily_ae lower (lowInputAngularCurve parameters lower length positive) 4 (by norm_num)
    (fun mode radius _ => lowInputAngularCurve_bound parameters lower length positive mode radius) (lowComponent lower 0 field) mode
  filter_upwards [actual, Lp.coeFn_smul Complex.I (base mode)] with radius actual scaled
  change (Complex.I • base mode) radius = _
  rw [scaled]
  change Complex.I • base mode radius = _
  rw [actual]
  rfl

theorem lowBulkSlot_ae {dimension : ℕ} (lower : ℝ) (slot : Fin dimension) (field : LowModeBulk lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : LowAnnularMode,
      lowBulkSlot lower slot field mode.val radius = (field mode radius 0) • operatorBasis slot := by
  filter_upwards [bulkMatrixUnit_ae lower slot 0 (lowBulkIntoFull lower field)] with radius actual
  intro mode
  simpa only [lowBulkSlot, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    lowBulkIntoFull_retained] using actual mode.val

end Grad.AnnularCurrentLow
