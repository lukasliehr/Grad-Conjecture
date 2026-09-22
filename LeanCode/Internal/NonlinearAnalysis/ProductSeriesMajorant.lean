import ProductWeightedCell
import ProductFiniteTensorSum

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.NonlinearProduct

open Grad.ClosedJets Grad.CartesianState

/-- This all-grade majorant is only used to construct the actual smooth
coefficient series. The public three-grade estimate uses exact allocations. -/
def seriesInputMajorant {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order : ℕ) (cell : ℤ) : ℝ :=
  ∑ rank ∈ Finset.range (order + 1), cellFrequency cell ^ order *
    ‖jetOperatorDerivative rank (phaseWeightedJet parameters cell (field.val cell))‖

theorem seriesInputMajorant_nonnegative {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order : ℕ) (cell : ℤ) :
    0 ≤ seriesInputMajorant parameters field order cell :=
  Finset.sum_nonneg (fun rank _ => mul_nonneg (pow_nonneg (cellFrequency_pos cell).le order)
    (norm_nonneg (jetOperatorDerivative rank (phaseWeightedJet parameters cell (field.val cell)))))

theorem seriesInputMajorant_summable {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order : ℕ) :
    Summable (seriesInputMajorant parameters field order) :=
  (hasSum_sum (fun rank (_ : rank ∈ Finset.range (order + 1)) =>
    (weighted_operator_sup_summable parameters field rank order).hasSum)).summable

theorem weighted_point_operator_le_majorant {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (order rank : ℕ) (rankBound : rank ≤ order)
    (cell : ℤ) (point : ClosedDisk) :
    cellFrequency cell ^ order *
      ‖jetOperatorDerivative rank (phaseWeightedJet parameters cell (field.val cell)) point‖ ≤
      seriesInputMajorant parameters field order cell := by
  apply (mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm
    (jetOperatorDerivative rank (phaseWeightedJet parameters cell (field.val cell))) point)
    (pow_nonneg (cellFrequency_pos cell).le order)).trans
  exact Finset.single_le_sum
    (f := fun candidate : ℕ => cellFrequency cell ^ order *
      ‖jetOperatorDerivative candidate (phaseWeightedJet parameters cell (field.val cell))‖)
    (fun candidate _ => mul_nonneg (pow_nonneg (cellFrequency_pos cell).le order)
      (norm_nonneg (jetOperatorDerivative candidate (phaseWeightedJet parameters cell (field.val cell)))))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le rankBound))

theorem productFrequency_power_le_product {arity : ℕ} (positiveArity : 0 < arity)
    (cells : Fin arity → ℤ) (order power : ℕ) (powerBound : power ≤ order) :
    productFrequency cells ^ power ≤ (arity : ℝ) ^ order *
      ∏ index, cellFrequency (cells index) ^ order := by
  have each (index : Fin arity) : cellFrequency (cells index) ≤ ∏ other, cellFrequency (cells other) := by
    simpa only [max_eq_left (cellFrequency_one_le _)] using
      Finset.le_prod_max_one (Finset.mem_univ index) (fun other => cellFrequency (cells other))
  have frequencyBound : productFrequency cells ≤
      (arity : ℝ) * ∏ index, cellFrequency (cells index) := by
    calc
      _ ≤ ∑ _index : Fin arity, ∏ other, cellFrequency (cells other) :=
        Finset.sum_le_sum (fun index _ => each index)
      _ = _ := by simp
  calc
    _ ≤ ((arity : ℝ) * ∏ index, cellFrequency (cells index)) ^ power :=
      pow_le_pow_left₀ (productFrequency_nonnegative cells) frequencyBound power
    _ = (arity : ℝ) ^ power * ∏ index, cellFrequency (cells index) ^ power := by
      rw [mul_pow, Finset.prod_pow]
    _ ≤ _ := mul_le_mul
      (pow_le_pow_right₀ (by exact_mod_cast positiveArity : (1 : ℝ) ≤ arity) powerBound)
      (Finset.prod_le_prod (fun _ _ => pow_nonneg (cellFrequency_pos _).le power)
        (fun _ _ => pow_le_pow_right₀ (cellFrequency_one_le _) powerBound))
      (Finset.prod_nonneg (fun _ _ => pow_nonneg (cellFrequency_pos _).le power))
      (pow_nonneg (Nat.cast_nonneg _) order)

theorem derivativeAllocation_series_bound {arity : ℕ} {dimensions : Fin arity → ℕ}
    (parameters : PhaseParameters) (fields : (index : Fin arity) → ACore parameters (dimensions index))
    (cells : Fin arity → ℤ) (order rank : ℕ) (rankBound : rank ≤ order) (point : ClosedDisk) :
    (∏ index, cellFrequency (cells index) ^ order) * derivativeAllocation arity
      (fun index derivative => ‖jetOperatorDerivative derivative
        (phaseWeightedJet parameters (cells index) ((fields index).val (cells index))) point‖) rank ≤
      allocationMultiplicity arity rank * ∏ index, seriesInputMajorant parameters (fields index) order (cells index) := by
  apply derivativeAllocation_le_of_allocation_bound _ (fun _ _ => norm_nonneg _) _ _ _
    (Finset.prod_nonneg (fun _ _ => pow_nonneg (cellFrequency_pos _).le order))
  intro orders ordersTotal
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun _ _ => mul_nonneg (pow_nonneg (cellFrequency_pos _).le order) (norm_nonneg _))
  intro index _
  have oneOrder : orders index ≤ rank := by
    rw [← ordersTotal]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ index)
  exact weighted_point_operator_le_majorant parameters (fields index) order (orders index)
    (oneOrder.trans rankBound) (cells index) point

end Grad.NonlinearProduct
