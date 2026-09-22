import AKDN49ActualForcingProductSmooth

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularReconstruction Grad.AnnularGeneralSourceRegularity
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothness Grad.AnnularCurrentLow Grad.QuotientProjection
open Grad.GaugeCoefficients.Physical.Allocation

/-- The literal three prescribed slots, acted on by any actual physical
row, have one joint source payment at the original analytic width. -/
theorem actualKnownRow_jointEnergy (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (total extra power rank : ℕ)
    (paid : extra+power+rank ≤ total) (row : Fin 3) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ state : RetainedInverseState parameters length compact,
    physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 10 ≤ 1 →
    ∀ source : SmoothQuotient parameters,
    (∫⁻ radius in Icc lower 1, ENNReal.ofReal
      (‖(1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)) •
        vectorEulerWithinIteratedDerivative (Icc lower 1) rank
          (fun point => radialConjugatedAction parameters lower positive bounded.le
            (lowPhysicalRowKernel parameters length compact state row) power 0 point
            (actualCartesianKnownSevenCurve parameters length lower positive bounded source power point)) radius‖^2)) ≤
      ENNReal.ofReal ((constant*(‖quotientEta parameters (4+total) source‖+
        (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*
          ‖quotientEta parameters 4 source‖))^2) := by
  obtain ⟨first,first0,firstEnergy⟩ := actualPhysicalPrimitive_jointEnergy parameters length compact lower
    positive bounded total extra power rank paid row 4 0
  obtain ⟨second,second0,secondEnergy⟩ := actualPhysicalPrimitive_jointEnergy parameters length compact lower
    positive bounded total extra power rank paid row 5 1
  obtain ⟨third,third0,thirdEnergy⟩ := actualPhysicalPrimitive_jointEnergy parameters length compact lower
    positive bounded total extra power rank paid row 6 2
  refine ⟨2*(2*(first+second)+third),by positivity,?_⟩
  intro state unit source
  let weight := 1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+extra)
  let payment := ‖quotientEta parameters (4+total) source‖+
    (1+physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (10+total))*
      ‖quotientEta parameters 4 source‖
  have payment0 : 0 ≤ payment := add_nonneg (norm_nonneg _)
    (mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) (norm_nonneg _))
  let curves := actualPhysicalPrimitiveCurve parameters length compact lower positive bounded state source row
  have smooth (injection : Fin 7) (slot : Fin 4) : ContDiffOn ℝ rank (curves injection slot power) (Icc lower 1) :=
    contDiffOn_infty.mp (actualPhysicalPrimitiveCurve_smooth parameters length compact lower positive bounded state source row injection slot power) rank
  have pairEnergy := eulerCurve_squareEnergy_add lower bounded (curves 4 0 power) (curves 5 1 power)
    rank (smooth 4 0) (smooth 5 1) weight (first*payment) (second*payment)
    (mul_nonneg first0 payment0) (mul_nonneg second0 payment0) (firstEnergy state unit source) (secondEnergy state unit source)
  have fullEnergy := eulerCurve_squareEnergy_add lower bounded
    (fun point => curves 4 0 power point+curves 5 1 power point) (curves 6 2 power)
    rank ((smooth 4 0).add (smooth 5 1)) (smooth 6 2) weight (2*(first*payment+second*payment)) (third*payment)
    (by positivity) (mul_nonneg third0 payment0) pairEnergy (thirdEnergy state unit source)
  have same := eulerCurve_squareEnergy_congr lower
    (fun point => radialConjugatedAction parameters lower positive bounded.le
      (lowPhysicalRowKernel parameters length compact state row) power 0 point
      (actualCartesianKnownSevenCurve parameters length lower positive bounded source power point))
    (fun point => (curves 4 0 power point+curves 5 1 power point)+curves 6 2 power point) (by
      intro point _
      dsimp only [actualCartesianKnownSevenCurve]
      rw [map_add,map_add]
      rfl) rank weight
  exact same.le.trans (fullEnergy.trans_eq (by congr 1; ring))

end Grad.OriginalCartesianTameEstimate
