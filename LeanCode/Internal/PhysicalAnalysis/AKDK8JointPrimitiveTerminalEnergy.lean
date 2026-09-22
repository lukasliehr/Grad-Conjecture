import AKDK7ActualPrimitiveEulerPayment

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ENNReal
namespace Grad.OriginalTerminalAllocation
open Grad.CartesianState Grad.OriginalCartesianTameEstimate Grad.AnnularGeneralSourceRegularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.QuotientProjection Grad.ExhaustionSourceAllocation

/-- The zero coefficient allocation and q=0 are included explicitly. -/
theorem originalSource_allocation (offset grade order : ℕ) (orderLe : order≤grade) :
    ∃ constant : ℝ, 0≤constant ∧ ∀ (parameters : PhaseParameters) (field : ACore parameters 3)
      (rho epsilon : ℝ) (source : SmoothQuotient parameters),
      physicalBudget parameters field rho epsilon offset≤1 →
      (1+physicalBudget parameters field rho epsilon (offset+order))*‖quotientEta parameters (4+(grade-order)) source‖ ≤
        constant*(‖quotientEta parameters (4+grade) source‖+
          (1+physicalBudget parameters field rho epsilon (offset+grade))*‖quotientEta parameters 4 source‖) := by
  by_cases zero : order=0
  · subst order
    refine ⟨2,by norm_num,?_⟩
    intro parameters field rho epsilon source low
    simp only [Nat.add_zero,Nat.sub_zero]
    have first := mul_le_mul_of_nonneg_right (show 1+physicalBudget parameters field rho epsilon offset≤2 by linarith) (norm_nonneg (quotientEta parameters (4+grade) source))
    have extra := mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative parameters field rho epsilon (offset+grade))) (norm_nonneg (quotientEta parameters 4 source))
    linarith
  have positive : 0<order := Nat.pos_of_ne_zero zero
  obtain ⟨remainder,remainder0,bound⟩ := originalSource_positiveOrder_oneHigh offset grade order (by omega) positive orderLe 1 (by norm_num)
  refine ⟨1+remainder,by linarith,?_⟩
  intro parameters field rho epsilon source low
  have estimate := bound parameters field rho epsilon source low
  have extra := mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative parameters field rho epsilon (offset+grade))) (norm_nonneg (quotientEta parameters 4 source))
  nlinarith only [estimate,extra,mul_nonneg remainder0 (norm_nonneg (quotientEta parameters (4+grade) source))]

/-- Exact primitive source terminals in ordered SR19 words. Coefficient,
Euler and tangential ranks share ONE q; the low source payment is F4. -/
theorem actualPrimitive_jointTerminalEnergy (parameters : PhaseParameters) (length lower : ℝ)
    (positive : 0<lower) (bounded : lower<1) (grade order power rank : ℕ)
    (paid : order+power+rank≤grade) :
    ∃ constants : Fin 4 → ℝ, (∀ slot,0≤constants slot) ∧
    ∀ (field : ACore parameters 3) (rho epsilon : ℝ), physicalBudget parameters field rho epsilon 10≤1 →
    ∀ (source : SmoothQuotient parameters) (slot : Fin 4),
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖(1+physicalBudget parameters field rho epsilon (10+order)) •
          vectorEulerWithinIteratedDerivative (Icc lower 1) rank
            (actualCartesianPrimitiveCurve parameters length lower positive bounded source slot power) radius‖^2)) ≤
        ENNReal.ofReal ((constants slot*(‖quotientEta parameters (4+grade) source‖+
          (1+physicalBudget parameters field rho epsilon (10+grade))*‖quotientEta parameters 4 source‖))^2) := by
  obtain ⟨primitive,primitive0,energy⟩ := actualPrimitiveCurve_eulerFourEnergy parameters length lower positive bounded power rank
  obtain ⟨allocation,allocation0,allocate⟩ := originalSource_allocation 10 grade order (by omega)
  refine ⟨fun slot => primitive slot*allocation,fun slot => mul_nonneg (primitive0 slot) allocation0,?_⟩
  intro field rho epsilon low source slot
  let budget := 1+physicalBudget parameters field rho epsilon (10+order)
  have budget0 : 0≤budget := add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have multiplied := boundedScalar_squareEnergy lower (fun _ => budget)
    (vectorEulerWithinIteratedDerivative (Icc lower 1) rank (actualCartesianPrimitiveCurve parameters length lower positive bounded source slot power))
    budget (primitive slot*‖quotientEta parameters (power+rank+4) source‖) budget0
    (fun _ _ => (Real.norm_of_nonneg budget0).le) (energy source slot)
  apply multiplied.trans
  apply ENNReal.ofReal_le_ofReal
  have total0 : 0≤‖quotientEta parameters (4+grade) source‖+
      (1+physicalBudget parameters field rho epsilon (10+grade))*‖quotientEta parameters 4 source‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) (norm_nonneg _))
  apply (sq_le_sq₀ (mul_nonneg budget0 (mul_nonneg (primitive0 slot) (norm_nonneg _)))
    (mul_nonneg (mul_nonneg (primitive0 slot) allocation0) total0)).mpr
  have middle := originalSourceNorm_monotone parameters source (by omega : power+rank+4≤4+(grade-order))
  have payment := (mul_le_mul_of_nonneg_left middle budget0).trans (allocate parameters field rho epsilon source low)
  have result := mul_le_mul_of_nonneg_left payment (primitive0 slot)
  dsimp only [budget] at result ⊢
  nlinarith only [result]

end Grad.OriginalTerminalAllocation
