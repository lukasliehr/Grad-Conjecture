import AEI4OriginalLowRadialInputMultipliers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction

def lowNormalizedRadius (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) :
    LowEnergyBulk lower →L[ℂ] LowModeBulk lower :=
  (lowModeScalarFamily lower (lowInputRadiusCurve parameters lower length positive) 2 (by norm_num)
    (fun mode radius _ => lowInputRadiusCurve_bound parameters lower length positive mode radius)).comp (lowComponent lower 0)

def lowNormalizedCell (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) : LowEnergyBulk lower →L[ℂ] LowModeBulk lower :=
  Complex.I • (lowModeScalarFamily lower (lowInputCellCurve parameters lower length positive) (2 * length) (by positivity)
    (fun mode radius _ => lowInputCellCurve_bound parameters lower length lengthPositive positive mode radius)).comp (lowComponent lower 0)

def lowNormalizedAngular (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower) :
    LowEnergyBulk lower →L[ℂ] LowModeBulk lower :=
  Complex.I • (lowModeScalarFamily lower (lowInputAngularCurve parameters lower length positive) 4 (by norm_num)
    (fun mode radius _ => lowInputAngularCurve_bound parameters lower length positive mode radius)).comp (lowComponent lower 0)

theorem lowNormalizedRadius_bound (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (field : LowEnergyBulk lower) : ‖lowNormalizedRadius parameters lower length positive field‖ ≤ 2 * ‖field‖ := by
  exact (lowModeScalarFamily_bound lower (lowInputRadiusCurve parameters lower length positive) 2 (by norm_num)
    (fun mode radius _ => lowInputRadiusCurve_bound parameters lower length positive mode radius) (lowComponent lower 0 field)).trans
    (mul_le_mul_of_nonneg_left (lowComponent_bound lower 0 field) (by norm_num))

theorem lowNormalizedCell_bound (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (field : LowEnergyBulk lower) :
    ‖lowNormalizedCell parameters lower length lengthPositive positive field‖ ≤ 2 * length * ‖field‖ := by
  change ‖Complex.I • lowModeScalarFamily lower (lowInputCellCurve parameters lower length positive)
    (2 * length) (by positivity)
    (fun mode radius _ => lowInputCellCurve_bound parameters lower length lengthPositive positive mode radius) (lowComponent lower 0 field)‖ ≤ _
  rw [norm_smul, Complex.norm_I, one_mul]
  exact (lowModeScalarFamily_bound _ _ _ _ _ _).trans
    (mul_le_mul_of_nonneg_left (lowComponent_bound lower 0 field) (by positivity))

theorem lowNormalizedAngular_bound (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (field : LowEnergyBulk lower) : ‖lowNormalizedAngular parameters lower length positive field‖ ≤ 4 * ‖field‖ := by
  change ‖Complex.I • lowModeScalarFamily lower (lowInputAngularCurve parameters lower length positive)
    4 (by norm_num)
    (fun mode radius _ => lowInputAngularCurve_bound parameters lower length positive mode radius) (lowComponent lower 0 field)‖ ≤ _
  rw [norm_smul, Complex.norm_I, one_mul]
  exact (lowModeScalarFamily_bound _ _ _ _ _ _).trans
    (mul_le_mul_of_nonneg_left (lowComponent_bound lower 0 field) (by norm_num))

def lowBulkSlot {dimension : ℕ} (lower : ℝ) (slot : Fin dimension) :
    LowModeBulk lower →L[ℂ] DivisionRow dimension lower :=
  (bulkMatrixUnit lower slot 0).comp (lowBulkIntoFull lower).toContinuousLinearMap

theorem lowBulkSlot_bound {dimension : ℕ} (lower : ℝ) (slot : Fin dimension) (field : LowModeBulk lower) :
    ‖lowBulkSlot lower slot field‖ ≤ ‖field‖ :=
  (bulkMatrixUnit_bound lower slot 0 (lowBulkIntoFull lower field)).trans_eq
    ((lowBulkIntoFull lower).norm_map field)

/-- Exact homogeneous physical order (x,Rxi/r,xi_zeta,xi/r,0,0,0),
stored with rho^1/2 exp(Phi). No radial tilt is added to the low graph. -/
def lowNormalizedSevenInput (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) : LowEnergyBulk lower →L[ℂ] DivisionRow 7 lower :=
  (lowBulkSlot lower 0).comp (lowComponent lower 1) +
  (lowBulkSlot lower 1).comp (lowNormalizedAngular parameters lower length positive) +
  (lowBulkSlot lower 2).comp (lowNormalizedCell parameters lower length lengthPositive positive) +
  (lowBulkSlot lower 3).comp (lowNormalizedRadius parameters lower length positive)

theorem lowNormalizedSevenInput_bound (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (field : LowEnergyBulk lower) :
    ‖lowNormalizedSevenInput parameters lower length lengthPositive positive field‖ ≤ (7 + 2 * length) * ‖field‖ := by
  have x := (lowBulkSlot_bound (dimension := 7) lower 0 (lowComponent lower 1 field)).trans (lowComponent_bound lower 1 field)
  have angular := (lowBulkSlot_bound (dimension := 7) lower 1 (lowNormalizedAngular parameters lower length positive field)).trans
    (lowNormalizedAngular_bound parameters lower length positive field)
  have cell := (lowBulkSlot_bound (dimension := 7) lower 2 (lowNormalizedCell parameters lower length lengthPositive positive field)).trans
    (lowNormalizedCell_bound parameters lower length lengthPositive positive field)
  have radius := (lowBulkSlot_bound (dimension := 7) lower 3 (lowNormalizedRadius parameters lower length positive field)).trans
    (lowNormalizedRadius_bound parameters lower length positive field)
  change ‖((lowBulkSlot lower 0 (lowComponent lower 1 field) +
    lowBulkSlot lower 1 (lowNormalizedAngular parameters lower length positive field)) +
    lowBulkSlot lower 2 (lowNormalizedCell parameters lower length lengthPositive positive field)) +
    lowBulkSlot lower 3 (lowNormalizedRadius parameters lower length positive field)‖ ≤ _
  exact (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
    ((add_le_add (add_le_add (norm_add_le _ _) le_rfl) le_rfl).trans (by linarith)))

end Grad.AnnularCurrentLow
