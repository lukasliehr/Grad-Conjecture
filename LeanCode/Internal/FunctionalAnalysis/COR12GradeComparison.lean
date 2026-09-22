import COR12DiskEnergy

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Grad.COR12Extension

open Grad.ClosedJets
open Grad.CartesianState
open Grad.DiskExtension.Operator
open Grad.FourierGrade

theorem fourierMultiIndex_mem_of_order {grade : ℕ} (index : DiskCellMultiIndex)
    (bound : diskCellOrder index ≤ grade) : index ∈ fourierMultiIndices grade := by
  apply mem_fourierMultiIndices.mpr
  simp only [diskCellOrder] at bound
  exact ⟨by omega, by omega, by omega, bound⟩

theorem diskCoefficientCoordinateEnergy_nonnegative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : DiskCellMultiIndex) :
    0 ≤ diskCoefficientCoordinateEnergy field index := by
  exact tsum_nonneg (fun _ => by positivity)

theorem diskCoefficientCoordinateEnergy_le_total {dimension grade : ℕ}
    (field : DiskCellClosedJet dimension) {index : DiskCellMultiIndex}
    (member : index ∈ fourierMultiIndices grade) :
    diskCoefficientCoordinateEnergy field index ≤
      (2 * Real.pi) * diskDerivativeEnergy grade field := by
  rw [diskDerivativeEnergy_parseval]
  exact Finset.single_le_sum
    (fun candidate _ => diskCoefficientCoordinateEnergy_nonnegative field candidate) member

theorem diskCoefficientCoordinateEnergy_weighted {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (index : DiskCellMultiIndex) :
    diskCoefficientCoordinateEnergy (weightedSmoothEquiv parameters field) index =
      ∑' cell : ℤ, |(cell : ℝ)| ^ (2 * index.2) *
        ‖closedDerivativeL2 index.1 (phaseWeightedJet parameters cell (field.1 cell))‖ ^ 2 := by
  unfold diskCoefficientCoordinateEnergy
  simp only [diskCellFourierCoefficientJet_weightedSmoothEquiv]

theorem diskCoefficientCoordinateEnergy_le_original {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    {index : DiskCellMultiIndex} (member : index ∈ fourierMultiIndices grade) :
    diskCoefficientCoordinateEnergy (weightedSmoothEquiv parameters field) index ≤
      ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 := by
  rcases mem_fourierMultiIndices.mp member with ⟨firstBound, secondBound, _, orderBound⟩
  let planar : GradeMultiIndex grade :=
    ⟨(⟨index.1.1, Nat.lt_succ_of_le firstBound⟩,
      ⟨index.1.2, Nat.lt_succ_of_le secondBound⟩), by
        change index.1.1 + index.1.2 ≤ grade
        simp only [diskCellOrder] at orderBound
        omega⟩
  have weightOrder : index.2 ≤ grade - cartesianOrder index.1 := by
    simp only [diskCellOrder, cartesianOrder] at orderBound ⊢
    omega
  have comparison : diskCoefficientCoordinateEnergy (weightedSmoothEquiv parameters field) index ≤
      originalCoordinateEnergy parameters field planar := by
    apply (diskCoefficientCoordinate_summable
      (weightedSmoothEquiv parameters field) index).tsum_le_tsum _
        (originalCoordinateEnergy_summable parameters field planar)
    intro cell
    rw [diskCellFourierCoefficientJet_weightedSmoothEquiv]
    change _ ≤ cellFrequency cell ^ (2 * (grade - cartesianOrder index.1)) *
      ‖closedDerivativeL2 index.1 (phaseWeightedJet parameters cell (field.1 cell))‖ ^ 2
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact (pow_le_pow_left₀ (abs_nonneg _) (cell_abs_le_frequency cell) _).trans
      (pow_le_pow_right₀ (cellFrequency_one_le cell) (Nat.mul_le_mul_left 2 weightOrder))
  exact comparison.trans (originalCoordinateEnergy_le_norm_sq parameters field planar)

theorem diskDerivativeEnergy_le_original {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) (grade : ℕ) :
    (2 * Real.pi) * diskDerivativeEnergy grade (weightedSmoothEquiv parameters field) ≤
      (Nat.choose (grade + 3) 3 : ℝ) * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 := by
  rw [diskDerivativeEnergy_parseval]
  calc
    (∑ index ∈ fourierMultiIndices grade,
        diskCoefficientCoordinateEnergy (weightedSmoothEquiv parameters field) index) ≤
      ∑ _index ∈ fourierMultiIndices grade,
        ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 :=
      Finset.sum_le_sum (fun _ member =>
        diskCoefficientCoordinateEnergy_le_original parameters field member)
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, ← derivativeCount, derivativeCount_eq_choose]

theorem cellFrequency_pow_le_two_endpoints (cell : ℤ) {order grade : ℕ}
    (bound : order ≤ grade) :
    cellFrequency cell ^ (2 * order) ≤
      (2 : ℝ) ^ grade * (1 + |(cell : ℝ)| ^ (2 * order)) := by
  have squared : cellFrequency cell ^ 2 = 1 + (cell : ℝ) ^ 2 := by
    rw [cellFrequency_formula, Real.sq_sqrt (by positivity)]
  rw [pow_mul, squared]
  have added := add_pow_le (by norm_num : (0 : ℝ) ≤ 1)
    (sq_nonneg (cell : ℝ)) order
  have added' : (1 + (cell : ℝ) ^ 2) ^ order ≤
      (2 : ℝ) ^ (order - 1) * (1 + |(cell : ℝ)| ^ (2 * order)) := by
    have absPower : ((cell : ℝ) ^ 2) ^ order = |(cell : ℝ)| ^ (2 * order) := by
      rw [← sq_abs (cell : ℝ), ← pow_mul]
    simpa only [one_pow, absPower] using added
  exact added'.trans (mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ((Nat.sub_le order 1).trans bound))
    (by positivity))

theorem originalCoordinateEnergy_le_endpoints {dimension grade : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension)
    (index : GradeMultiIndex grade) :
    originalCoordinateEnergy parameters field index ≤
      (2 : ℝ) ^ grade *
        (diskCoefficientCoordinateEnergy (weightedSmoothEquiv parameters field)
          (index.toCartesian, 0) +
        diskCoefficientCoordinateEnergy (weightedSmoothEquiv parameters field)
          (index.toCartesian, grade - cartesianOrder index.toCartesian)) := by
  let order := grade - cartesianOrder index.toCartesian
  have sumZero := diskCoefficientCoordinate_summable
    (weightedSmoothEquiv parameters field) (index.toCartesian, 0)
  have sumTop := diskCoefficientCoordinate_summable
    (weightedSmoothEquiv parameters field) (index.toCartesian, order)
  have bound := (originalCoordinateEnergy_summable parameters field index).tsum_le_tsum
    (fun cell => by
      rw [diskCellFourierCoefficientJet_weightedSmoothEquiv]
      dsimp only [Prod.fst, Prod.snd]
      have frequency := cellFrequency_pow_le_two_endpoints cell
        (Nat.sub_le grade (cartesianOrder index.toCartesian))
      have weighted := mul_le_mul_of_nonneg_right frequency
        (sq_nonneg ‖closedDerivativeL2 index.toCartesian
          (phaseWeightedJet parameters cell (field.1 cell))‖)
      convert weighted using 1
      simp only [Nat.mul_zero, pow_zero, one_mul, order]
      ring)
    ((sumZero.add sumTop).mul_left ((2 : ℝ) ^ grade))
  simpa only [tsum_mul_left, Summable.tsum_add sumZero sumTop,
    originalCoordinateEnergy, diskCoefficientCoordinateEnergy, order] using bound

def originalDiskEnergyFactor (grade : ℕ) : ℝ :=
  (Fintype.card (GradeMultiIndex grade) : ℝ) * (2 : ℝ) ^ grade * 2

theorem originalDiskEnergyFactor_nonnegative (grade : ℕ) :
    0 ≤ originalDiskEnergyFactor grade := by
  unfold originalDiskEnergyFactor
  positivity

theorem original_norm_sq_le_diskDerivativeEnergy {dimension : ℕ}
    (parameters : PhaseParameters) (field : ACore parameters dimension) (grade : ℕ) :
    ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 ≤
      originalDiskEnergyFactor grade *
        ((2 * Real.pi) * diskDerivativeEnergy grade (weightedSmoothEquiv parameters field)) := by
  rw [originalGrade_norm_sq_eq_sum_coordinateEnergy]
  have eachIndex : ∀ index : GradeMultiIndex grade,
      originalCoordinateEnergy parameters field index ≤
        ((2 : ℝ) ^ grade * 2) *
          ((2 * Real.pi) * diskDerivativeEnergy grade (weightedSmoothEquiv parameters field)) := by
    intro index
    have indexBound : cartesianOrder index.toCartesian ≤ grade := index.property
    have memberZero : (index.toCartesian, 0) ∈ fourierMultiIndices grade := by
      apply fourierMultiIndex_mem_of_order
      simpa only [diskCellOrder, cartesianOrder, Nat.add_zero] using indexBound
    have memberTop : (index.toCartesian, grade - cartesianOrder index.toCartesian) ∈
        fourierMultiIndices grade := by
      apply fourierMultiIndex_mem_of_order
      change cartesianOrder index.toCartesian + (grade - cartesianOrder index.toCartesian) ≤ grade
      omega
    have zeroBound := diskCoefficientCoordinateEnergy_le_total
      (weightedSmoothEquiv parameters field) memberZero
    have topBound := diskCoefficientCoordinateEnergy_le_total
      (weightedSmoothEquiv parameters field) memberTop
    have endpoints := originalCoordinateEnergy_le_endpoints parameters field index
    nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) grade]
  calc
    (∑ index : GradeMultiIndex grade, originalCoordinateEnergy parameters field index) ≤
        ∑ _index : GradeMultiIndex grade, ((2 : ℝ) ^ grade * 2) *
          ((2 * Real.pi) * diskDerivativeEnergy grade (weightedSmoothEquiv parameters field)) :=
      Finset.sum_le_sum (fun index _ => eachIndex index)
    _ = _ := by simp [originalDiskEnergyFactor]; ring

end Grad.COR12Extension
