import SCD4PolarDivision

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

def shiftedSupGradeIndex {grade order : ℕ} (word : CartesianWord order)
    (paid : order + 2 ≤ grade) (slot : Fin 6) : GradeMultiIndex grade :=
  (gradeMultiIndexEquiv grade).symm ⟨m15DiskSupIndex word slot, by
    rw [m15DiskSupIndex_order]
    have bound := diskSupMultiIndex_order_le_two slot
    omega⟩

theorem shiftedSupGradeIndex_value {grade order : ℕ} (word : CartesianWord order)
    (paid : order + 2 ≤ grade) (slot : Fin 6) :
    (shiftedSupGradeIndex word paid slot).toCartesian = m15DiskSupIndex word slot := by
  exact congrArg Subtype.val ((gradeMultiIndexEquiv grade).apply_symm_apply _)

/-- Pay only the two M4 Cartesian grades, retaining every remaining cell power. -/
theorem shiftedSupCoordinate_bound {dimension grade order power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (word : CartesianWord order) (paid : order + power + 2 ≤ grade) (slot : Fin 6) :
    cellFrequency cell ^ power *
      ‖closedDerivativeL2 (diskSupMultiIndex slot)
        (shiftedClosedJet (phaseWeightedJet parameters cell field) word)‖ ≤
      ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  let index := shiftedSupGradeIndex word (by omega : order + 2 ≤ grade) slot
  have coordinateBound := PiLp.norm_apply_le (cellGradeRowLinear (grade := grade) parameters cell field) index
  rw [cellGradeRowLinear_apply, norm_smul, Complex.norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (cellFrequency_pos cell)] at coordinateBound
  have indexValue : index.toCartesian = m15DiskSupIndex word slot := shiftedSupGradeIndex_value word _ slot
  rw [shiftedClosedDerivativeL2_eq_m15Coordinate]
  apply le_trans _ coordinateBound
  rw [indexValue]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  apply pow_le_pow_right₀ (cellFrequency_one_le cell)
  rw [m15DiskSupIndex_order]
  have bound := diskSupMultiIndex_order_le_two slot
  omega

theorem shiftedSupEnergy_bound {dimension grade order power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (word : CartesianWord order) (paid : order + power + 2 ≤ grade) :
    cellFrequency cell ^ power *
      Real.sqrt (diskSupEnergy (shiftedClosedJet (phaseWeightedJet parameters cell field) word)) ≤
      6 * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  have frequencyPositive := cellFrequency_pos cell
  let shifted := shiftedClosedJet (phaseWeightedJet parameters cell field) word
  let row := cellGradeRowLinear (grade := grade) parameters cell field
  have energyNonnegative : 0 ≤ diskSupEnergy shifted :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have weightedSquares : (cellFrequency cell ^ power) ^ 2 * diskSupEnergy shifted ≤ 6 * ‖row‖ ^ 2 := by
    unfold diskSupEnergy
    rw [Finset.mul_sum]
    calc
      _ = ∑ slot : Fin 6,
          (cellFrequency cell ^ power * ‖closedDerivativeL2 (diskSupMultiIndex slot) shifted‖) ^ 2 := by
        apply Finset.sum_congr rfl
        intro slot _
        ring
      _ ≤ ∑ _slot : Fin 6, ‖row‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro slot _
        exact pow_le_pow_left₀ (by positivity)
          (shiftedSupCoordinate_bound parameters cell field word paid slot) 2
      _ = _ := by simp
  have nonnegative : 0 ≤ cellFrequency cell ^ power * Real.sqrt (diskSupEnergy shifted) := by
    positivity
  have square : (cellFrequency cell ^ power * Real.sqrt (diskSupEnergy shifted)) ^ 2 =
      (cellFrequency cell ^ power) ^ 2 * diskSupEnergy shifted := by
    rw [mul_pow, Real.sq_sqrt energyNonnegative]
  change cellFrequency cell ^ power * Real.sqrt (diskSupEnergy shifted) ≤ 6 * ‖row‖
  nlinarith [norm_nonneg row, sq_nonneg ‖row‖]

theorem weighted_word_sup_paid {dimension grade order power : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (word : CartesianWord order) (paid : order + power + 2 ≤ grade) :
    cellFrequency cell ^ power * ‖closedDerivative (phaseWeightedJet parameters cell field) order word‖ ≤
      (6 * diskSupConstant) * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  have frequencyPositive := cellFrequency_pos cell
  have supBound : ‖closedDerivative (phaseWeightedJet parameters cell field) order word‖ ≤
      diskSupConstant * Real.sqrt (diskSupEnergy
        (shiftedClosedJet (phaseWeightedJet parameters cell field) word)) := by
    apply (ContinuousMap.norm_le _ (mul_nonneg diskSupConstant_pos.le (Real.sqrt_nonneg _))).mpr
    intro point
    exact diskSup_bound (shiftedClosedJet _ word) point
  calc
    _ ≤ cellFrequency cell ^ power * (diskSupConstant * Real.sqrt (diskSupEnergy
        (shiftedClosedJet (phaseWeightedJet parameters cell field) word))) :=
      mul_le_mul_of_nonneg_left supBound (by positivity)
    _ = diskSupConstant * (cellFrequency cell ^ power * Real.sqrt (diskSupEnergy
        (shiftedClosedJet (phaseWeightedJet parameters cell field) word))) := by ring
    _ ≤ diskSupConstant * (6 * ‖cellGradeRowLinear (grade := grade) parameters cell field‖) :=
      mul_le_mul_of_nonneg_left (shiftedSupEnergy_bound parameters cell field word paid) diskSupConstant_pos.le
    _ = _ := by ring

end Grad.SourceCollarDivision
