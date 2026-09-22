import AW3Interface

noncomputable section

open Grad.PDEBootstrap Grad.GenericCarriers Grad.AnalyticWeights.Calculus
open scoped ContDiff BigOperators

namespace Grad.AnalyticWeights.Higher

universe valueUniverse

theorem ordered_norm_sq {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (rank : ℕ) (function : Spatial → Value) (point : Spatial) :
    ‖orderedTensor rank function point‖ ^ 2 =
      ∑ word : Fin rank → Fin 2, ‖orderedDerivative rank word function point‖ ^ 2 :=
  tensor_norm_sq rank (orderedTensor rank function point)

theorem coordinateGoal : CoordinateGoal.{valueUniverse} :=
  ⟨fun _ _ _ => ordered_norm_sq, fun _ _ _ => rfl⟩

theorem direction_norm (direction : Fin 2) : ‖spatialDirection direction‖ = 1 := by
  change ‖WithLp.toLp 2 (Pi.single direction (1 : ℝ) : Fin 2 → ℝ)‖ = 1
  simp

theorem orderedDerivative_norm_le {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (rank : ℕ) (word : Fin rank → Fin 2) (function : Spatial → Value) (point : Spatial) :
    ‖orderedDerivative rank word function point‖ ≤ ‖iteratedFDeriv ℝ rank function point‖ := by
  simpa only [orderedDerivative, direction_norm, Finset.prod_const_one, mul_one] using
    (iteratedFDeriv ℝ rank function point).le_opNorm (fun position => spatialDirection (word position))

theorem orderedTensor_norm_le {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (rank : ℕ) (function : Spatial → Value) (point : Spatial) :
    ‖orderedTensor rank function point‖ ≤ (2 : ℝ) ^ rank * ‖iteratedFDeriv ℝ rank function point‖ := by
  have countPositive : 1 ≤ (2 : ℝ) ^ rank := one_le_pow₀ (by norm_num)
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by positivity) (norm_nonneg _))).mp
  rw [ordered_norm_sq]
  calc
    _ ≤ ∑ _word : Fin rank → Fin 2, ‖iteratedFDeriv ℝ rank function point‖ ^ 2 :=
      Finset.sum_le_sum (fun word _ => pow_le_pow_left₀ (norm_nonneg _)
        (orderedDerivative_norm_le rank word function point) 2)
    _ = (2 : ℝ) ^ rank * ‖iteratedFDeriv ℝ rank function point‖ ^ 2 := by
      simp
    _ ≤ ((2 : ℝ) ^ rank * ‖iteratedFDeriv ℝ rank function point‖) ^ 2 := by
      nlinarith [sq_nonneg ‖iteratedFDeriv ℝ rank function point‖]

theorem derivativeBound_of_norm_le {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (rank : ℕ) (function : Spatial → Value) (point : Spatial) (bound : ℝ)
    (normBound : ‖iteratedFDeriv ℝ rank function point‖ ≤ bound) :
    DerivativeBound rank function point ((2 : ℝ) ^ rank * bound) := by
  have boundNonnegative := (norm_nonneg _).trans normBound
  refine ⟨normBound.trans ?_, (orderedTensor_norm_le rank function point).trans ?_⟩
  · exact le_mul_of_one_le_left boundNonnegative (one_le_pow₀ (by norm_num))
  · exact mul_le_mul_of_nonneg_left normBound (by positivity)

theorem rankZeroGoal : RankZeroGoal.{valueUniverse} := by
  constructor
  · intro Value _ _ word function point
    refine ⟨rfl, norm_iteratedFDeriv_zero, ?_⟩
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [ordered_norm_sq, Fintype.sum_unique]
    rfl
  · intro sigma gamma scale output input point
    refine ⟨by simp [weightCost], by simp [allocationPolynomial],
      (Grad.AnalyticWeights.Calculus.formulaGoal sigma gamma scale output point).2.2.2.2, ?_⟩
    rw [weightRatio, physicalWeight_exp, inverseWeight_exp, ← Real.exp_add]
    rfl

end Grad.AnalyticWeights.Higher
