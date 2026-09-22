import AEG3CompletedPhysicalSlots

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularTiltedReference Grad.AnnularGrades Grad.AnnularFluxTrace

section Derivatives
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- Actual tilted physical radial derivative, before any coefficient action. -/
def highPhysicalDerivative : annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  (annularEnergyDerivative lower length positive -
    annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength).comp
      (bEnergyDecode lower length positive)

/-- The opposite phase derivative on the variational test. -/
def highPhysicalTestDerivative : annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  (annularEnergyDerivative lower length positive +
    annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength).comp
      (bEnergyDecode lower length positive)

theorem highPhysicalDerivative_bound (field : annularEnergySpace lower length positive) :
    ‖highPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field‖ ≤ 2 * ‖field‖ := by
  have squareRoot : Real.sqrt (15 / 16 : ℝ) ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have decoded := physicalEnergyDecode_bound lower length positive field
  have derivative := annularEnergyDerivative_bound lower length positive (bEnergyDecode lower length positive field)
  have phase := annularTiltEnergyPhase_bound parameters lower length positive lengthPositive widthHalf widthLength
    (bEnergyDecode lower length positive field)
  have phaseSmall := phase.trans (mul_le_mul_of_nonneg_right squareRoot (norm_nonneg _))
  calc
    _ ≤ ‖annularEnergyDerivative lower length positive (bEnergyDecode lower length positive field)‖ +
        ‖annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength
          (bEnergyDecode lower length positive field)‖ := norm_sub_le _ _
    _ ≤ ‖bEnergyDecode lower length positive field‖ + 1 * ‖bEnergyDecode lower length positive field‖ :=
      add_le_add derivative phaseSmall
    _ ≤ 2 * ‖field‖ := by linarith

theorem highPhysicalTestDerivative_bound (field : annularEnergySpace lower length positive) :
    ‖highPhysicalTestDerivative parameters lower length positive lengthPositive widthHalf widthLength field‖ ≤ 2 * ‖field‖ := by
  have squareRoot : Real.sqrt (15 / 16 : ℝ) ≤ 1 := (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have decoded := physicalEnergyDecode_bound lower length positive field
  have derivative := annularEnergyDerivative_bound lower length positive (bEnergyDecode lower length positive field)
  have phase := annularTiltEnergyPhase_bound parameters lower length positive lengthPositive widthHalf widthLength
    (bEnergyDecode lower length positive field)
  have phaseSmall := phase.trans (mul_le_mul_of_nonneg_right squareRoot (norm_nonneg _))
  calc
    _ ≤ ‖annularEnergyDerivative lower length positive (bEnergyDecode lower length positive field)‖ +
        ‖annularTiltEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength
          (bEnergyDecode lower length positive field)‖ := norm_add_le _ _
    _ ≤ ‖bEnergyDecode lower length positive field‖ + 1 * ‖bEnergyDecode lower length positive field‖ :=
      add_le_add derivative phaseSmall
    _ ≤ 2 * ‖field‖ := by linarith

/-- The literal normalized AHW eight-input packet. The four source slots vanish.
The cell slot is xi_zeta, retaining L in the operator that consumes it. -/
def highEightEnergyPacket : annularEnergySpace lower length positive →L[ℂ] DivisionRow 8 lower :=
  (highBulkSlot lower 0).comp (highPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength) +
  (highBulkSlot lower 1).comp ((highEnergyAngularRadius lower length positive).comp (bEnergyDecode lower length positive)) +
  (highBulkSlot lower 2).comp (((length : ℂ) • highEnergyCell lower length positive).comp (bEnergyDecode lower length positive)) +
  (highBulkSlot lower 3).comp ((highEnergyRadius lower length positive).comp (bEnergyDecode lower length positive))

theorem highEightEnergyPacket_bound (field : annularEnergySpace lower length positive) :
    ‖highEightEnergyPacket parameters lower length positive lengthPositive widthHalf widthLength field‖ ≤
      (4 + 2 * |length|) * ‖field‖ := by
  let decoded := bEnergyDecode lower length positive field
  have decodeBound : ‖decoded‖ ≤ ‖field‖ := physicalEnergyDecode_bound lower length positive field
  have first := (highBulkSlot_bound lower (0 : Fin 8) _).trans
    (highPhysicalDerivative_bound parameters lower length positive lengthPositive widthHalf widthLength field)
  have second := (highBulkSlot_bound lower (1 : Fin 8) (highEnergyAngularRadius lower length positive decoded)).trans
    ((highEnergyAngularRadius_bound lower length positive decoded).trans decodeBound)
  have third := highBulkSlot_bound lower (2 : Fin 8) ((length : ℂ) • highEnergyCell lower length positive decoded)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs] at third
  have cell := (highEnergyCell_bound lower length positive decoded).trans
    (mul_le_mul_of_nonneg_left decodeBound (by norm_num : (0 : ℝ) ≤ 2))
  have thirdBound := third.trans (mul_le_mul_of_nonneg_left cell (abs_nonneg length))
  have fourth := (highBulkSlot_bound lower (3 : Fin 8) (highEnergyRadius lower length positive decoded)).trans
    ((highEnergyRadius_bound lower length positive decoded).trans
      (mul_le_mul_of_nonneg_left decodeBound (by norm_num : (0 : ℝ) ≤ 1 / 3)))
  calc
    _ ≤ ‖highBulkSlot lower (0 : Fin 8)
        (highPhysicalDerivative parameters lower length positive lengthPositive widthHalf widthLength field)‖ +
      ‖highBulkSlot lower (1 : Fin 8) (highEnergyAngularRadius lower length positive decoded)‖ +
      ‖highBulkSlot lower (2 : Fin 8) ((length : ℂ) • highEnergyCell lower length positive decoded)‖ +
      ‖highBulkSlot lower (3 : Fin 8) (highEnergyRadius lower length positive decoded)‖ :=
        (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
          (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    _ ≤ 2 * ‖field‖ + ‖field‖ + |length| * (2 * ‖field‖) + (1 / 3 : ℝ) * ‖field‖ :=
      add_le_add (add_le_add (add_le_add first second) thirdBound) fourth
    _ ≤ (4 + 2 * |length|) * ‖field‖ := by nlinarith [norm_nonneg field]

/-- The three exact bulk test factors for pairing X, C, and rV. -/
def highEnergyTestPacket : annularEnergySpace lower length positive →L[ℂ] DivisionRow 3 lower :=
  (highBulkSlot lower 0).comp (highPhysicalTestDerivative parameters lower length positive lengthPositive widthHalf widthLength) +
  (highBulkSlot lower 1).comp ((highEnergyCell lower length positive).comp (bEnergyDecode lower length positive)) +
  (highBulkSlot lower 2).comp ((highEnergyAngularRadius lower length positive).comp (bEnergyDecode lower length positive))

theorem highEnergyTestPacket_bound (field : annularEnergySpace lower length positive) :
    ‖highEnergyTestPacket parameters lower length positive lengthPositive widthHalf widthLength field‖ ≤ 5 * ‖field‖ := by
  let decoded := bEnergyDecode lower length positive field
  have decodeBound : ‖decoded‖ ≤ ‖field‖ := physicalEnergyDecode_bound lower length positive field
  have first := (highBulkSlot_bound lower (0 : Fin 3) _).trans
    (highPhysicalTestDerivative_bound parameters lower length positive lengthPositive widthHalf widthLength field)
  have second := (highBulkSlot_bound lower (1 : Fin 3) (highEnergyCell lower length positive decoded)).trans
    ((highEnergyCell_bound lower length positive decoded).trans
      (mul_le_mul_of_nonneg_left decodeBound (by norm_num : (0 : ℝ) ≤ 2)))
  have third := (highBulkSlot_bound lower (2 : Fin 3) (highEnergyAngularRadius lower length positive decoded)).trans
    ((highEnergyAngularRadius_bound lower length positive decoded).trans decodeBound)
  calc
    _ ≤ ‖highBulkSlot lower (0 : Fin 3)
        (highPhysicalTestDerivative parameters lower length positive lengthPositive widthHalf widthLength field)‖ +
      ‖highBulkSlot lower (1 : Fin 3) (highEnergyCell lower length positive decoded)‖ +
      ‖highBulkSlot lower (2 : Fin 3) (highEnergyAngularRadius lower length positive decoded)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ 2 * ‖field‖ + 2 * ‖field‖ + ‖field‖ := add_le_add (add_le_add first second) third
    _ = 5 * ‖field‖ := by ring

end Derivatives
end Grad.AnnularCurrentEnergy
