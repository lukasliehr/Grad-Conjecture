import BL4ProfileCalculus

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

def normalizedRadialWeight (parameters : PhaseParameters) (cell : ℤ) (time : ℝ) : ℝ :=
  radialWeight parameters cell time / Real.exp (boundaryPhase parameters cell)

theorem normalizedRadialWeight_pos (parameters : PhaseParameters) (cell : ℤ) (time : ℝ) :
    0 < normalizedRadialWeight parameters cell time :=
  div_pos (cartesianWeight_pos parameters cell _) (Real.exp_pos _)

theorem normalizedRadialWeight_smooth (parameters : PhaseParameters) (cell : ℤ) :
    ContDiff ℝ ∞ (normalizedRadialWeight parameters cell) :=
  (radialWeight_smooth parameters cell).div_const _

theorem normalizedRadialWeight_iterated_bound (parameters : PhaseParameters) (cell : ℤ)
    (order : ℕ) (time : ℝ) :
    ‖iteratedDeriv order (normalizedRadialWeight parameters cell) time‖ ≤
      physicalWeightDerivativeConstant order parameters.gamma * normalizedRadialWeight parameters cell time *
        cellFrequency cell ^ order := by
  change ‖iteratedDeriv order (fun source => radialWeight parameters cell source /
    Real.exp (boundaryPhase parameters cell)) time‖ ≤ _
  rw [iteratedDeriv_div_const, norm_div, Real.norm_of_nonneg (Real.exp_pos _).le]
  have bound := div_le_div_of_nonneg_right (radialWeight_iterated_bound parameters cell order time)
    (Real.exp_pos (boundaryPhase parameters cell)).le
  apply bound.trans_eq
  unfold normalizedRadialWeight
  ring

def profileDerivativeConstant (order : ℕ) (gamma : ℝ) : ℝ :=
  ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) * cutoffExponentialConstant index *
    physicalWeightDerivativeConstant (order - index) gamma

theorem profileDerivativeConstant_nonnegative (order : ℕ) (gamma : ℝ)
    (gammaNonnegative : 0 ≤ gamma) : 0 ≤ profileDerivativeConstant order gamma :=
  Finset.sum_nonneg (fun _index _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (cutoffExponentialConstant_nonnegative _))
    (physicalWeightDerivativeConstant_nonnegative _ _ gammaNonnegative))

theorem split_frequency_power_bound (mode : ℤ × ℤ) (order index : ℕ) (indexBound : index ≤ order) :
    boundaryFrequency mode ^ index * cellFrequency mode.2 ^ (order - index) ≤
      boundaryFrequency mode ^ order := by
  calc
    _ ≤ boundaryFrequency mode ^ index * boundaryFrequency mode ^ (order - index) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (cellFrequency_pos _).le (cellFrequency_le_boundaryFrequency mode) _)
        (pow_nonneg (boundaryFrequency_pos _).le _)
    _ = _ := by rw [← pow_add, Nat.add_sub_of_le indexBound]

theorem conjugatedProfile_product (parameters : PhaseParameters) (mode : ℤ × ℤ) :
    conjugatedProfile parameters mode = fun time =>
      cutoffExponentialProfile mode time * normalizedRadialWeight parameters mode.2 time := by
  funext time
  rw [conjugatedProfile, conjugatedExponentialProfile_weight]
  unfold cutoffExponentialProfile normalizedRadialWeight radialWeight
  ring

theorem conjugatedProfile_iterated_preliminary (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (order : ℕ) (time : ℝ) (inside : time ∈ Icc (0 : ℝ) (1 / 4)) :
    ‖iteratedDeriv order (conjugatedProfile parameters mode) time‖ ≤
      profileDerivativeConstant order parameters.gamma * boundaryFrequency mode ^ order *
        conjugatedExponentialProfile parameters mode time := by
  rw [conjugatedProfile_product]
  have product := norm_iteratedDeriv_product_le _ _ (cutoffExponentialProfile_smooth mode)
    (normalizedRadialWeight_smooth parameters mode.2) order time
  apply product.trans
  simp only [profileDerivativeConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index member
  have indexBound : index ≤ order := by have := Finset.mem_range.mp member; omega
  have cutoffBound := cutoffExponentialProfile_iterated_bound mode index time inside
  have weightBound := normalizedRadialWeight_iterated_bound parameters mode.2 (order - index) time
  have firstNonnegative : 0 ≤ (order.choose index : ℝ) * cutoffExponentialConstant index :=
    mul_nonneg (Nat.cast_nonneg _) (cutoffExponentialConstant_nonnegative _)
  have combinedNonnegative : 0 ≤ (order.choose index : ℝ) * cutoffExponentialConstant index *
      physicalWeightDerivativeConstant (order - index) parameters.gamma :=
    mul_nonneg firstNonnegative (physicalWeightDerivativeConstant_nonnegative _ _ parameters.gamma_pos.le)
  calc
    _ ≤ (order.choose index : ℝ) *
        (cutoffExponentialConstant index * boundaryFrequency mode ^ index *
          Real.exp (-boundaryFrequency mode * time)) *
        (physicalWeightDerivativeConstant (order - index) parameters.gamma *
          normalizedRadialWeight parameters mode.2 time * cellFrequency mode.2 ^ (order - index)) := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left cutoffBound (Nat.cast_nonneg _)) weightBound
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg
          (mul_nonneg (cutoffExponentialConstant_nonnegative _) (pow_nonneg (boundaryFrequency_pos _).le _))
          (Real.exp_pos _).le))
    _ = ((order.choose index : ℝ) * cutoffExponentialConstant index *
        physicalWeightDerivativeConstant (order - index) parameters.gamma) *
        (boundaryFrequency mode ^ index * cellFrequency mode.2 ^ (order - index)) *
        conjugatedExponentialProfile parameters mode time := by
      rw [conjugatedExponentialProfile_weight]
      unfold normalizedRadialWeight radialWeight
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (split_frequency_power_bound mode order index indexBound) combinedNonnegative)
      (Real.exp_pos _).le

/-- N27 with genuine iterated derivatives and the exact strict decay margin. -/
theorem conjugatedProfile_iterated_decay (parameters : PhaseParameters) (mode : ℤ × ℤ)
    (order : ℕ) (time : ℝ) (inside : time ∈ Icc (0 : ℝ) (1 / 4)) :
    ‖iteratedDeriv order (conjugatedProfile parameters mode) time‖ ≤
      profileDerivativeConstant order parameters.gamma * boundaryFrequency mode ^ order *
        Real.exp (-boundaryDecayRate parameters * boundaryFrequency mode * time) := by
  apply (conjugatedProfile_iterated_preliminary parameters mode order time inside).trans
  exact mul_le_mul_of_nonneg_left
    (conjugatedExponentialProfile_decay parameters mode time inside.1 (by linarith [inside.2]))
    (mul_nonneg (profileDerivativeConstant_nonnegative _ _ parameters.gamma_pos.le)
      (pow_nonneg (boundaryFrequency_pos _).le _))

end Grad.BoundaryLift
