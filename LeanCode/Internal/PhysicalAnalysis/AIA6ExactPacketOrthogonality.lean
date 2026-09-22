import AIA5LiteralCircularBulkEntries

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCircularForm
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.Ledger

/-- The literal scalar slot maps are mutually orthogonal in completed radial L2. -/
theorem radialScalarSlots_inner {dimension : ℕ} (lower : ℝ) (first second : Fin dimension)
    (test field : RadialL2 1 lower) :
    inner ℂ (radialMatrixUnit lower first 0 test) (radialMatrixUnit lower second 0 field) =
      if first = second then inner ℂ test field else 0 := by
  by_cases same : first = second
  · subst second
    rw [if_pos rfl, L2.inner_def, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [radialMatrixUnit_ae lower first 0 test, radialMatrixUnit_ae lower first 0 field]
      with radius testLaw fieldLaw
    rw [testLaw, fieldLaw]
    simp [PiLp.inner_apply, operatorBasis]
  · rw [if_neg same, L2.inner_def]
    apply integral_eq_zero_of_ae
    filter_upwards [radialMatrixUnit_ae lower first 0 test, radialMatrixUnit_ae lower second 0 field]
      with radius testLaw fieldLaw
    rw [testLaw, fieldLaw]
    simp [PiLp.inner_apply, operatorBasis, Ne.symm same]

theorem bulkScalarSlots_inner {dimension : ℕ} (lower : ℝ) (first second : Fin dimension)
    (test field : DivisionRow 1 lower) :
    inner ℂ (bulkMatrixUnit lower first 0 test) (bulkMatrixUnit lower second 0 field) =
      if first = second then inner ℂ test field else 0 := by
  simp only [lp.inner_eq_tsum]
  change (∑' mode : ℤ × ℤ, inner ℂ (radialMatrixUnit lower first 0 (test mode))
    (radialMatrixUnit lower second 0 (field mode))) = _
  simp_rw [radialScalarSlots_inner]
  split_ifs <;> simp

/-- The exact original high-to-full inclusion preserves these orthogonal pairings. -/
theorem highBulkSlots_inner {dimension : ℕ} (lower : ℝ) (first second : Fin dimension)
    (test field : AnnularBulk lower) :
    inner ℂ (highBulkSlot lower first test) (highBulkSlot lower second field) =
      if first = second then inner ℂ test field else 0 := by
  change inner ℂ (bulkMatrixUnit lower first 0 (highBulkIntoFull lower test))
    (bulkMatrixUnit lower second 0 (highBulkIntoFull lower field)) = _
  rw [bulkScalarSlots_inner]
  rw [(highBulkIntoFull lower).inner_map_map]

/-- Concrete three-factor packet pairing, in the user-visible x,c,rV output order. -/
theorem highThreePacket_inner (lower : ℝ) (test0 test1 test2 field0 field1 field2 : AnnularBulk lower) :
    inner ℂ (highBulkSlot lower (0 : Fin 3) test0 + highBulkSlot lower (1 : Fin 3) test1 + highBulkSlot lower (2 : Fin 3) test2)
      (highBulkSlot lower (0 : Fin 3) field0 + highBulkSlot lower (1 : Fin 3) field1 + highBulkSlot lower (2 : Fin 3) field2) =
      inner ℂ test0 field0 + inner ℂ test1 field1 + inner ℂ test2 field2 := by
  simp [inner_add_left, inner_add_right, highBulkSlots_inner]

end Grad.AnnularCircularForm
