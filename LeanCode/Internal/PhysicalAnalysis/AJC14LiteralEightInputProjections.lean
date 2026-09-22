import AJC12CompletedPhysicalFirstRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularStrongSolution
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentSource Grad.AnnularPhysicalSolution Grad.AnnularCircularForm
open Grad.AnnularCurrentGreen Grad.AnnularTiltedReference

theorem bulkScalarProjection_same {dimension : ℕ} (lower : ℝ) (slot : Fin dimension)
    (field : DivisionRow 1 lower) :
    bulkMatrixUnit lower (0 : Fin 1) slot (bulkMatrixUnit lower slot 0 field) = field := by
  apply ext_inner_left ℂ
  intro test
  rw [← bulkPhysicalSlot_pairing, bulkScalarSlots_inner, if_pos rfl]

private theorem projectEight {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (project : F →L[ℂ] E) (inject : Fin 8 → E →L[ℂ] F) (slot : Fin 8) (value : Fin 8 → E)
    (law : ∀ index, project (inject index (value index)) = if index = slot then value index else 0) :
    project ((inject 0 (value 0) + inject 1 (value 1) + inject 2 (value 2) + inject 3 (value 3)) +
      (inject 4 (value 4) + inject 5 (value 5) + inject 6 (value 6) + inject 7 (value 7))) = value slot := by
  simp only [map_add, law]
  fin_cases slot <;> simp

private theorem bulkEightProject (lower : ℝ) (slot : Fin 8) (value : Fin 8 → DivisionRow 1 lower) :
    bulkMatrixUnit lower (0 : Fin 1) slot
      ((bulkMatrixUnit lower (0 : Fin 8) 0 (value 0) + bulkMatrixUnit lower (1 : Fin 8) 0 (value 1) +
        bulkMatrixUnit lower (2 : Fin 8) 0 (value 2) + bulkMatrixUnit lower (3 : Fin 8) 0 (value 3)) +
        (bulkMatrixUnit lower (4 : Fin 8) 0 (value 4) + bulkMatrixUnit lower (5 : Fin 8) 0 (value 5) +
        bulkMatrixUnit lower (6 : Fin 8) 0 (value 6) + bulkMatrixUnit lower (7 : Fin 8) 0 (value 7))) = value slot := by
  apply projectEight (bulkMatrixUnit lower (0 : Fin 1) slot) (fun index => bulkMatrixUnit lower index 0) slot value
  intro index
  by_cases same : index = slot
  · subst index
    exact (bulkScalarProjection_same lower slot (value slot)).trans (if_pos rfl).symm
  · exact (bulkScalarProjection_distinct lower slot index (Ne.symm same) (value index)).trans (if_neg same).symm

variable (parameters : PhaseParameters) (lower L : ℝ) (positive : 0 < lower) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (field : annularEnergySpace lower L positive) (known : HighKnownSourceBulk lower)

/-- The first original eight-input coordinate is the actual physical derivative. -/
theorem fullHighEightPacket_first :
    bulkMatrixUnit lower (0 : Fin 1) (0 : Fin 8)
      (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (field, known)) =
    highBulkIntoFull lower (highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength field) := by
  let decoded := bEnergyDecode lower L positive field
  exact bulkEightProject lower 0 ![
    highBulkIntoFull lower (highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength field),
    highBulkIntoFull lower (highEnergyAngularRadius lower L positive decoded),
    highBulkIntoFull lower ((L : ℂ) • highEnergyCell lower L positive decoded),
    highBulkIntoFull lower (highEnergyRadius lower L positive decoded), known 0, known 1, known 2, known 3]

/-- The independent f occupies exactly slot seven of the full physical input. -/
theorem fullHighEightPacket_f :
    bulkMatrixUnit lower (0 : Fin 1) (7 : Fin 8)
      (fullHighEightPacket parameters lower L positive lengthPositive widthHalf widthLength (field, known)) = known 3 := by
  let decoded := bEnergyDecode lower L positive field
  exact bulkEightProject lower 7 ![
    highBulkIntoFull lower (highPhysicalDerivative parameters lower L positive lengthPositive widthHalf widthLength field),
    highBulkIntoFull lower (highEnergyAngularRadius lower L positive decoded),
    highBulkIntoFull lower ((L : ℂ) • highEnergyCell lower L positive decoded),
    highBulkIntoFull lower (highEnergyRadius lower L positive decoded), known 0, known 1, known 2, known 3]

end Grad.AnnularStrongSolution
