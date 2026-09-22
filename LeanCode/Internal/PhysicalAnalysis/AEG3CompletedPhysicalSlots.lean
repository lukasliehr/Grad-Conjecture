import AEG2LiteralHighBulkEmbedding

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.SourceCollarDivision Grad.AnnularVariational Grad.MatrixMultiplier
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

/-- One literal component map on completed radial L2; the norm bound is one. -/
def radialMatrixUnit {input output : ℕ} (lower : ℝ) (row : Fin output) (column : Fin input) :
    RadialL2 input lower →L[ℂ] RadialL2 output lower :=
  matrixMultiplier (volume.restrict (Icc lower 1)) (fun _ => matrixUnit row column) 1
    continuous_const.aestronglyMeasurable (Filter.Eventually.of_forall fun _ => matrixUnit_norm_le row column)

theorem radialMatrixUnit_bound {input output : ℕ} (lower : ℝ) (row : Fin output) (column : Fin input)
    (field : RadialL2 input lower) : ‖radialMatrixUnit lower row column field‖ ≤ 1 * ‖field‖ :=
  norm_matrixMultiplier_apply_le _ _ _ _ _ field

theorem radialMatrixUnit_ae {input output : ℕ} (lower : ℝ) (row : Fin output) (column : Fin input)
    (field : RadialL2 input lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      radialMatrixUnit lower row column field radius = (field radius column) • operatorBasis row := by
  simpa only [radialMatrixUnit, matrixUnit_apply] using matrixMultiplier_apply_ae
    (volume.restrict (Icc lower 1)) (fun _ => matrixUnit row column) 1
      continuous_const.aestronglyMeasurable
      (Filter.Eventually.of_forall fun _ => matrixUnit_norm_le row column) field

/-- The completed scalar-to-vector slot inclusion preserves actual coefficients. -/
def bulkMatrixUnit {input output : ℕ} (lower : ℝ) (row : Fin output) (column : Fin input) :
    DivisionRow input lower →L[ℂ] DivisionRow output lower :=
  complexLpTwoMap (fun _ => radialMatrixUnit lower row column) 1 (by norm_num)
    (fun _ => radialMatrixUnit_bound lower row column)

theorem bulkMatrixUnit_bound {input output : ℕ} (lower : ℝ) (row : Fin output) (column : Fin input)
    (field : DivisionRow input lower) : ‖bulkMatrixUnit lower row column field‖ ≤ ‖field‖ := by
  simpa only [bulkMatrixUnit, one_mul] using complexLpTwoMap_bound
    (fun _ : ℤ × ℤ => radialMatrixUnit lower row column) 1 (by norm_num)
      (fun _ => radialMatrixUnit_bound lower row column) field

theorem bulkMatrixUnit_ae {input output : ℕ} (lower : ℝ) (row : Fin output) (column : Fin input)
    (field : DivisionRow input lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      bulkMatrixUnit lower row column field mode radius = (field mode radius column) • operatorBasis row := by
  rw [ae_all_iff]
  intro mode
  exact radialMatrixUnit_ae lower row column (field mode)

def highBulkSlot {dimension : ℕ} (lower : ℝ) (slot : Fin dimension) :
    AnnularBulk lower →L[ℂ] DivisionRow dimension lower :=
  (bulkMatrixUnit lower slot 0).comp (highBulkIntoFull lower).toContinuousLinearMap

theorem highBulkSlot_bound {dimension : ℕ} (lower : ℝ) (slot : Fin dimension)
    (field : AnnularBulk lower) : ‖highBulkSlot lower slot field‖ ≤ ‖field‖ :=
  (bulkMatrixUnit_bound lower slot 0 (highBulkIntoFull lower field)).trans_eq
    ((highBulkIntoFull lower).norm_map field)

theorem highBulkSlot_ae {dimension : ℕ} (lower : ℝ) (slot : Fin dimension)
    (field : AnnularBulk lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : HighAnnularMode,
      highBulkSlot lower slot field mode.val radius = (field mode radius 0) • operatorBasis slot := by
  filter_upwards [bulkMatrixUnit_ae lower slot 0 (highBulkIntoFull lower field)] with radius actual
  intro mode
  simpa only [highBulkSlot, ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap,
    highBulkIntoFull_high] using actual mode.val

end Grad.AnnularCurrentEnergy
