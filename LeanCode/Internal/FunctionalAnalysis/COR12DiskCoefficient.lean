import COR12CellParseval

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.COR12Extension

open Grad.ClosedJets
open Grad.CartesianState
open Grad.DiskExtension.Operator

local instance cor12DiskCoefficientCellPeriodPositive :
    Fact (0 < (2 * Real.pi : ℝ)) :=
  ⟨mul_pos (by norm_num) Real.pi_pos⟩

theorem list_ofFn_repeatedCell_planar
    (first second cellOrder : ℕ) :
    List.ofFn
        (repeatedCellDerivativeWord
          (fp17LiftPlanarWord (cartesianMultiIndexWord (first, second)))
          cellOrder) =
      List.replicate cellOrder 2 ++
        (List.replicate first 0 ++ List.replicate second 1) := by
  apply List.ext_get
  · simp [cartesianOrder]
    omega
  · intro position firstBound secondBound
    simp only [List.get_eq_getElem]
    by_cases beforeCell : position < cellOrder
    · rw [List.getElem_append_left (by simpa using beforeCell)]
      simp [repeatedCellDerivativeWord, beforeCell]
    · rw [List.getElem_append_right (by
          simpa using Nat.le_of_not_gt beforeCell)]
      by_cases beforeFirst : position - cellOrder < first
      · rw [List.getElem_append_left (by simpa using beforeFirst)]
        simp [repeatedCellDerivativeWord, fp17LiftPlanarWord,
          fp17PlanarCoordinate, cartesianMultiIndexWord, cartesianOrder,
          beforeCell, beforeFirst]
      · rw [List.getElem_append_right (by
            simpa using Nat.le_of_not_gt beforeFirst)]
        simp [repeatedCellDerivativeWord, fp17LiftPlanarWord,
          fp17PlanarCoordinate, cartesianMultiIndexWord, cartesianOrder,
          beforeCell, beforeFirst]

theorem mixedWordMultiIndex_repeatedCell_planar
    (index : CartesianMultiIndex) (cellOrder : ℕ) :
    mixedWordMultiIndex
        (repeatedCellDerivativeWord
          (fp17LiftPlanarWord (cartesianMultiIndexWord index)) cellOrder) =
      (index, cellOrder) := by
  rcases index with ⟨first, second⟩
  rw [mixedWordMultiIndex,
    list_ofFn_repeatedCell_planar first second cellOrder]
  norm_num [List.count_replicate, Fin.ext_iff]

theorem closedDiskCellMultiDerivative_eq_repeatedCell
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (index : CartesianMultiIndex) (cellOrder : ℕ) :
    closedDiskCellMultiDerivative field (index, cellOrder) =
      closedMixedDerivative field (cartesianOrder index + cellOrder)
        (repeatedCellDerivativeWord
          (fp17LiftPlanarWord (cartesianMultiIndexWord index)) cellOrder) := by
  rw [closedMixedDerivative_eq_multiIndexDerivative]
  rw [mixedWordMultiIndex_repeatedCell_planar]

theorem diskCellFourierValue_closedDiskCellMultiDerivative
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (index : CartesianMultiIndex) (cellOrder : ℕ) (cell : ℤ) :
    diskCellFourierValue
        (closedDiskCellMultiDerivative field (index, cellOrder)) cell =
      cellDerivativeFactor cell cellOrder •
        closedMultiDerivative (diskCellFourierCoefficientJet field cell) index := by
  rw [closedDiskCellMultiDerivative_eq_repeatedCell]
  rw [diskCellFourierValue_repeatedCell]
  rw [closedMultiDerivative_diskCellFourierCoefficientJet]
  rfl

def diskDerivativeCellSlice {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : DiskCellMultiIndex)
    (point : ClosedDisk) : C(CellCircle, ComplexEuclidean dimension) :=
  (closedDiskCellMultiDerivative field index).comp
    ⟨fun circle => (point, circle), continuous_const.prodMk continuous_id⟩

theorem diskDerivativeCellSlice_fourierCoeff {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : DiskCellMultiIndex)
    (point : ClosedDisk) (cell : ℤ) :
    fourierCoeff (diskDerivativeCellSlice field index point) cell =
      diskCellFourierValue
        (closedDiskCellMultiDerivative field index) cell point := by
  rw [diskCellFourierValue_apply]
  rfl

theorem diskDerivativeCellSlice_parseval {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : DiskCellMultiIndex)
    (point : ClosedDisk) :
    (∫ circle : CellCircle,
        ‖closedDiskCellMultiDerivative field index (point, circle)‖ ^ 2
          ∂AddCircle.haarAddCircle) =
      ∑' cell : ℤ,
        ‖diskCellFourierValue
          (closedDiskCellMultiDerivative field index) cell point‖ ^ 2 := by
  rw [show (fun circle : CellCircle =>
      ‖closedDiskCellMultiDerivative field index (point, circle)‖ ^ 2) =
      fun circle : CellCircle =>
        ‖diskDerivativeCellSlice field index point circle‖ ^ 2 by rfl]
  rw [cell_euclidean_continuous_parseval]
  apply tsum_congr
  intro cell
  rw [diskDerivativeCellSlice_fourierCoeff]

theorem diskDerivativeCellSlice_parseval_coefficient {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : CartesianMultiIndex)
    (cellOrder : ℕ) (point : ClosedDisk) :
    (∫ circle : CellCircle,
        ‖closedDiskCellMultiDerivative field (index, cellOrder)
          (point, circle)‖ ^ 2 ∂AddCircle.haarAddCircle) =
      ∑' cell : ℤ, |(cell : ℝ)| ^ (2 * cellOrder) *
        ‖closedMultiDerivative
          (diskCellFourierCoefficientJet field cell) index point‖ ^ 2 := by
  rw [diskDerivativeCellSlice_parseval]
  apply tsum_congr
  intro cell
  rw [diskCellFourierValue_closedDiskCellMultiDerivative,
    ContinuousMap.smul_apply, norm_smul, cellDerivativeFactor_norm, mul_pow]
  ring

end Grad.COR12Extension
