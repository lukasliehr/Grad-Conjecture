import AKCX33SameCellMultiplierGraphs

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.WeightedJets.SpatialMultiplier Grad.CellWeights Grad.WeakTesting Grad.WeakTesting.Commutation
open Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher

private theorem phaseOrderedDerivative_snoc {rank : ℕ} (word : Fin rank → Fin 2)
    (direction : Fin 2) (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) :
    orderedTestDerivative (rank+1) (Fin.snoc word direction) test =
      orderedTestDerivative rank word (differentiate direction test) := by
  rw [← listDerivative_ofFn _ _ _ smooth,← listDerivative_ofFn _ _ _ (differentiate_contDiff direction test smooth)]
  rw [List.ofFn_succ']
  simp [listDerivative,List.foldr_append]

def startupPhaseDerivativeConstant (gamma scale : ℝ) (rank : ℕ) : ℝ :=
  profileConstant rank * gamma * scale ^ rank

theorem startupPhaseDerivativeConstant_nonnegative (gamma scale : ℝ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale) (rank : ℕ) :
    0 ≤ startupPhaseDerivativeConstant gamma scale rank :=
  mul_nonneg (mul_nonneg (profileConstant_nonnegative rank) gammaNonnegative) (pow_nonneg scaleNonnegative _)

theorem startupPhaseOrdered_bound (sigma gamma scale : ℝ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (rank : ℕ) (positive : 1 ≤ rank) (word : Fin rank → Fin 2) (cell : ℤ) (point : Spatial) :
    |orderedTestDerivative rank word (physicalPhase sigma gamma scale cell) point| ≤
      startupPhaseDerivativeConstant gamma scale rank * cellWeight cell ^ rank := by
  exact (orderedDerivative_norm_le rank word (physicalPhase sigma gamma scale cell) point).trans
    (physicalPhase_iterated_norm_bound sigma gamma scale cell gammaNonnegative scaleNonnegative rank positive point)

theorem startupPhaseSlope_scalar_bound (sigma gamma scale : ℝ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    {order : ℕ} (index : JetIndex order) (cell : ℤ) (direction : Fin 2) (point : Spatial) :
    |scalarDerivative index.val (startupScaledPhaseSlope sigma gamma scale cell direction) point| ≤
      startupPhaseDerivativeConstant gamma scale (degree index+1) * cellWeight cell ^ (degree index+1) := by
  change |orderedTestDerivative (degree index) (derivativeWord index)
    (differentiate direction (physicalPhase sigma gamma scale cell)) point| ≤ _
  rw [← phaseOrderedDerivative_snoc _ _ _ (physicalPhase_contDiff sigma gamma scale cell)]
  exact startupPhaseOrdered_bound sigma gamma scale gammaNonnegative scaleNonnegative _ (by omega) _ cell point

theorem startupPhaseHessian_scalar_bound (sigma gamma scale : ℝ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    {order : ℕ} (index : JetIndex order) (cell : ℤ) (outer inner : Fin 2) (point : Spatial) :
    |scalarDerivative index.val (Grad.RepresentedKernel.SpatialProduct.directionDerivative outer
      (startupScaledPhaseSlope sigma gamma scale cell inner)) point| ≤
      startupPhaseDerivativeConstant gamma scale (degree index+2) * cellWeight cell ^ (degree index+2) := by
  change |orderedTestDerivative (degree index) (derivativeWord index)
    (differentiate outer (differentiate inner (physicalPhase sigma gamma scale cell))) point| ≤ _
  rw [← phaseOrderedDerivative_snoc _ _ _ (differentiate_contDiff inner _ (physicalPhase_contDiff sigma gamma scale cell)),
    ← phaseOrderedDerivative_snoc _ _ _ (physicalPhase_contDiff sigma gamma scale cell)]
  exact startupPhaseOrdered_bound sigma gamma scale gammaNonnegative scaleNonnegative _ (by omega) _ cell point

/-- All derivatives of the genuine original phase slope pay only rank+1 cell powers. -/
def startupPhaseSlopeSymbol (sigma gamma scale : ℝ)
    (gammaNonnegative : 0 ≤ gamma) (scaleNonnegative : 0 ≤ scale)
    (order : ℕ) (direction : Fin 2) : StartupCellSpatialSymbol order (order+1) where
  toFun cell := startupScaledPhaseSlope sigma gamma scale cell direction
  smooth cell := startupScaledPhaseSlope_smooth sigma gamma scale cell direction
  bound index := startupPhaseDerivativeConstant gamma scale (degree index+1)
  nonnegative index := startupPhaseDerivativeConstant_nonnegative gamma scale gammaNonnegative scaleNonnegative (degree index+1)
  derivative_bound index cell point :=
    (startupPhaseSlope_scalar_bound sigma gamma scale gammaNonnegative scaleNonnegative index cell direction point).trans
      (mul_le_mul_of_nonneg_left
        (pow_le_pow_right₀ (cellWeight_one_le cell) (Nat.add_le_add_right index.property 1))
        (startupPhaseDerivativeConstant_nonnegative gamma scale gammaNonnegative scaleNonnegative _))

end Grad.CartesianStartup
