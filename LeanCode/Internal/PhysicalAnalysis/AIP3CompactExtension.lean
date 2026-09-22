import AIP2ActualDiskFourier
import ClosedJetSmoothExtension
import P0910Geometry

noncomputable section
open Set

namespace Grad.InteriorPeriodization
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.DiskExtension.Operator Grad.DiskExtension.Seeley

theorem normalizedSingleCore_weighted (parameters : PhaseParameters) (field : ClosedJet 1) :
    weightedSmoothEquiv parameters (normalizedSingleCore parameters field) = constantDiskCellJet field := by
  apply (weightedSmoothEquiv parameters).symm.injective
  rw [LinearEquiv.symm_apply_apply]
  apply Subtype.ext
  funext cell
  rw [weightedSmoothEquiv_symm_apply, constantDiskCellJet,
    diskCellFourierCoefficientJet_ordinaryReconstructedClosedJet]
  by_cases zero : cell = 0
  · subst cell
    rfl
  · change (if cell = 0 then phaseInverseWeightedJet parameters 0 field else 0) =
      phaseInverseWeightedJet parameters cell (if cell = 0 then field else 0)
    rw [if_neg zero, if_neg zero]
    exact ((phaseInverseWeightedJetLinear parameters cell).map_zero).symm

/-- A compactly supported interior field has zero Seeley exterior: every
active reflected point lies outside radius5/6, beyond the field support. -/
theorem compact_exteriorSummand_zero (field : ClosedJet 1)
    (supported : ∀ point : ClosedDisk, (3 / 4 : ℝ) < ‖point.val‖ → field.value point = 0)
    (index : ℕ) (point : SpatialPlane) (cell : CellCircle) (outside : 1 < ‖point‖) :
    exteriorSummandFromValue (constantDiskCellJet field).value index point cell = 0 := by
  classical
  by_cases inactive : plateauCutoff (node index * (‖point‖ - 1)) = 0
  · simp only [exteriorSummandFromValue, inactive, mul_zero, Complex.ofReal_zero, zero_smul]
  · have active := cutoff_nonzero_activeRange index point inactive
    rw [collar_constants.2.2.1] at active
    have range : node index * (‖point‖ - 1) < 1 := by linarith
    have member := reflectedPoint_mem_closedUnitDisk index point outside range
    have norm := reflectedPoint_norm index point outside range
    have far : (3 / 4 : ℝ) < ‖reflectedPoint index point‖ := by linarith
    simp only [exteriorSummandFromValue, closedDiskLift, dif_pos member]
    rw [constantDiskCellJet_value, supported ⟨reflectedPoint index point, member⟩ far, smul_zero]

theorem compact_ambientExtension_zero (field : ClosedJet 1)
    (supported : ∀ point : ClosedDisk, (3 / 4 : ℝ) < ‖point.val‖ → field.value point = 0)
    (point : SpatialPlane) (cell : CellCircle) (outside : 1 < ‖point‖) :
    ambientExtensionFromValue (constantDiskCellJet field).value point cell = 0 := by
  classical
  have notInside : point ∉ closedUnitDisk := by
    change ¬ ‖point‖ ≤ 1
    exact not_le.mpr outside
  simp only [ambientExtensionFromValue, dif_neg notInside, exteriorSeriesFromValue]
  calc
    _ = ∑' _ : ℕ, (0 : ComplexEuclidean 1) :=
      tsum_congr (fun index => compact_exteriorSummand_zero field supported index point cell outside)
    _ = 0 := tsum_zero

theorem compact_ambientExtension_literal (field : ClosedJet 1)
    (supported : ∀ point : ClosedDisk, (3 / 4 : ℝ) < ‖point.val‖ → field.value point = 0)
    (point : SpatialPlane) (cell : CellCircle) :
    ambientExtensionFromValue (constantDiskCellJet field).value point cell =
      closedDiskLift field.value point := by
  classical
  by_cases inside : point ∈ closedUnitDisk
  · simp only [ambientExtensionFromValue, dif_pos inside, closedDiskLift]
    exact constantDiskCellJet_value field ⟨point, inside⟩ cell
  · have outside : 1 < ‖point‖ := lt_of_not_ge inside
    rw [compact_ambientExtension_zero field supported point cell outside]
    simp only [closedDiskLift, dif_neg inside]

end Grad.InteriorPeriodization
