import AKCX34ActualPhaseHigherBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.SpatialMultiplier Grad.CellWeights
open Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher

def startupPhaseProductConstant (gamma scale : ℝ) {order : ℕ} (upper : JetIndex order) : ℝ :=
  ∑ lower ∈ below upper, (binomial upper lower : ℝ) *
    startupPhaseDerivativeConstant gamma scale (degree (difference upper lower)+1) *
    startupPhaseDerivativeConstant gamma scale (degree lower+1)

theorem startupPhaseProductConstant_nonnegative (gamma scale : ℝ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    {order : ℕ} (upper : JetIndex order) : 0 ≤ startupPhaseProductConstant gamma scale upper :=
  Finset.sum_nonneg (fun lower _ => mul_nonneg
    (mul_nonneg (Nat.cast_nonneg (binomial upper lower)) (startupPhaseDerivativeConstant_nonnegative gamma scale gammaNonnegative scaleNonnegative (degree (difference upper lower)+1)))
    (startupPhaseDerivativeConstant_nonnegative gamma scale gammaNonnegative scaleNonnegative (degree lower+1)))

theorem startupPhaseProduct_scalar_bound (sigma gamma scale : ℝ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    {order : ℕ} (upper : JetIndex order) (cell : ℤ) (outer inner : Fin 2) (point : Spatial) :
    |scalarDerivative upper.val (fun point => startupScaledPhaseSlope sigma gamma scale cell outer point *
      startupScaledPhaseSlope sigma gamma scale cell inner point) point| ≤
      startupPhaseProductConstant gamma scale upper * cellWeight cell ^ (degree upper+2) := by
  rw [scalarDerivative_mul order upper _ _ (startupScaledPhaseSlope_smooth sigma gamma scale cell outer)
    (startupScaledPhaseSlope_smooth sigma gamma scale cell inner)]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [startupPhaseProductConstant,Finset.sum_mul]
  apply Finset.sum_le_sum
  intro lower member
  have included := (mem_below upper lower).mp member
  have degreeSum : (degree (difference upper lower)+1)+(degree lower+1) = degree upper+2 := by
    change ((upper.val.1-lower.val.1)+(upper.val.2-lower.val.2)+1)+(lower.val.1+lower.val.2+1) = upper.val.1+upper.val.2+2
    rcases included with ⟨first,second⟩
    omega
  rw [abs_mul,abs_mul,abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ ((binomial upper lower : ℝ) *
        (startupPhaseDerivativeConstant gamma scale (degree (difference upper lower)+1) * cellWeight cell ^ (degree (difference upper lower)+1))) *
        (startupPhaseDerivativeConstant gamma scale (degree lower+1) * cellWeight cell ^ (degree lower+1)) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (startupPhaseSlope_scalar_bound sigma gamma scale gammaNonnegative scaleNonnegative (difference upper lower) cell outer point) (Nat.cast_nonneg _))
        (startupPhaseSlope_scalar_bound sigma gamma scale gammaNonnegative scaleNonnegative lower cell inner point)
        (abs_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
          (mul_nonneg (startupPhaseDerivativeConstant_nonnegative gamma scale gammaNonnegative scaleNonnegative _) (pow_nonneg (cellWeight_pos cell).le _)))
    _ = _ := by
      rw [show (binomial upper lower : ℝ) *
          (startupPhaseDerivativeConstant gamma scale (degree (difference upper lower)+1) * cellWeight cell ^ (degree (difference upper lower)+1)) *
          (startupPhaseDerivativeConstant gamma scale (degree lower+1) * cellWeight cell ^ (degree lower+1)) =
          ((binomial upper lower : ℝ) * startupPhaseDerivativeConstant gamma scale (degree (difference upper lower)+1) *
            startupPhaseDerivativeConstant gamma scale (degree lower+1)) *
            (cellWeight cell ^ (degree (difference upper lower)+1) * cellWeight cell ^ (degree lower+1)) by ring]
      rw [← pow_add,degreeSum]

private theorem phaseScalarDerivative_add {order : ℕ} (index : JetIndex order)
    (first second : Spatial → ℝ) (one : ContDiff ℝ ∞ first) (two : ContDiff ℝ ∞ second) (point : Spatial) :
    scalarDerivative index.val (fun point => first point+second point) point =
      scalarDerivative index.val first point+scalarDerivative index.val second point := by
  change (iteratedFDeriv ℝ (degree index) (first+second) point) _ = _
  rw [iteratedFDeriv_add_apply ((one.of_le (by exact_mod_cast le_top)).contDiffAt)
    ((two.of_le (by exact_mod_cast le_top)).contDiffAt)]
  rfl

theorem startupPhaseSecond_scalar_bound (sigma gamma scale : ℝ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    {order : ℕ} (index : JetIndex order) (cell : ℤ) (outer inner : Fin 2) (point : Spatial) :
    |scalarDerivative index.val (startupScaledPhaseSecond sigma gamma scale cell outer inner) point| ≤
      (startupPhaseDerivativeConstant gamma scale (degree index+2)+startupPhaseProductConstant gamma scale index) *
        cellWeight cell ^ (degree index+2) := by
  unfold startupScaledPhaseSecond
  rw [phaseScalarDerivative_add index _ _
    (startupTestDerivative_smooth _ (startupScaledPhaseSlope_smooth sigma gamma scale cell inner) outer)
    ((startupScaledPhaseSlope_smooth sigma gamma scale cell outer).mul (startupScaledPhaseSlope_smooth sigma gamma scale cell inner))]
  apply (abs_add_le _ _).trans
  exact (add_le_add (startupPhaseHessian_scalar_bound sigma gamma scale gammaNonnegative scaleNonnegative index cell outer inner point)
    (startupPhaseProduct_scalar_bound sigma gamma scale gammaNonnegative scaleNonnegative index cell outer inner point)).trans_eq (add_mul _ _ _).symm

/-- The full Hessian plus gradient-square term pays the exact finite rank+2 reserve. -/
def startupPhaseSecondSymbol (sigma gamma scale : ℝ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (order : ℕ) (outer inner : Fin 2) : StartupCellSpatialSymbol order (order+2) where
  toFun cell := startupScaledPhaseSecond sigma gamma scale cell outer inner
  smooth cell := startupScaledPhaseSecond_smooth sigma gamma scale cell outer inner
  bound index := startupPhaseDerivativeConstant gamma scale (degree index+2)+startupPhaseProductConstant gamma scale index
  nonnegative index := add_nonneg
    (startupPhaseDerivativeConstant_nonnegative gamma scale gammaNonnegative scaleNonnegative (degree index+2))
    (startupPhaseProductConstant_nonnegative gamma scale gammaNonnegative scaleNonnegative index)
  derivative_bound index cell point :=
    (startupPhaseSecond_scalar_bound sigma gamma scale gammaNonnegative scaleNonnegative index cell outer inner point).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (cellWeight_one_le cell) (Nat.add_le_add_right index.property 2))
        (add_nonneg (startupPhaseDerivativeConstant_nonnegative gamma scale gammaNonnegative scaleNonnegative (degree index+2))
          (startupPhaseProductConstant_nonnegative gamma scale gammaNonnegative scaleNonnegative index)))

end Grad.CartesianStartup
