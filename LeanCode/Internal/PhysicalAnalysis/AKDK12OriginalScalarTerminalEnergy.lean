import AKDK8JointPrimitiveTerminalEnergy
import AKDK11NativePureTerminalEnergy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ENNReal
namespace Grad.OriginalTerminalAllocation
open Grad.CartesianState Grad.OriginalCartesianTameEstimate Grad.AnnularGeneralSourceRegularity
open Grad.GaugeCoefficients.Physical.Allocation Grad.QuotientProjection Grad.ExhaustionSourceAllocation
open Grad.NonlinearProduct

/-- Each original scalar source row, including the source-2 term in the
literal G3 expansion, has the same joint allocation and independent F4.
The constant is chosen before the coefficient state and source, at one
fixed original collar. -/
theorem actualScalarSource_jointTerminalEnergy (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0<lower) (bounded : lower<1) (grade order power rank : ℕ)
    (paid : order+power+rank≤grade) :
    ∃ constant : ℝ, 0≤constant ∧
    ∀ (field : ACore parameters 3) (rho epsilon : ℝ), physicalBudget parameters field rho epsilon 10≤1 →
    ∀ (source : SmoothQuotient parameters) (row : Fin 4),
      (∫⁻ radius in Icc lower 1, ENNReal.ofReal
        (‖(1+physicalBudget parameters field rho epsilon (10+order)) •
          vectorEulerWithinIteratedDerivative (Icc lower 1) rank
            (cartesianWeightedRadialCurve parameters lower positive bounded (source row) power 0) radius‖^2)) ≤
        ENNReal.ofReal ((constant*(‖quotientEta parameters (4+grade) source‖+
          (1+physicalBudget parameters field rho epsilon (10+grade))*‖quotientEta parameters 4 source‖))^2) := by
  obtain ⟨allocation,allocation0,allocate⟩ := originalSource_allocation 10 grade order (by omega)
  let curveConstant := originalEulerCurveConstant lower power rank
  have curve0 : 0≤curveConstant := originalEulerCurveConstant_nonnegative lower positive power rank
  refine ⟨curveConstant*allocation,mul_nonneg curve0 allocation0,?_⟩
  intro field rho epsilon low source row
  let budget := 1+physicalBudget parameters field rho epsilon (10+order)
  have budget0 : 0≤budget := add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)
  have energy := actualCartesianCurve_eulerCollarEnergy parameters lower positive bounded
    (by omega : power+rank≤4+(grade-order)) (source row)
  have multiplied := boundedScalar_squareEnergy lower (fun _ => budget)
    (vectorEulerWithinIteratedDerivative (Icc lower 1) rank
      (cartesianWeightedRadialCurve parameters lower positive bounded (source row) power 0))
    budget (curveConstant*originalGradeNorm (4+(grade-order)) (source row)) budget0
    (fun _ _ => (Real.norm_of_nonneg budget0).le) energy
  apply multiplied.trans
  apply ENNReal.ofReal_le_ofReal
  have total0 : 0≤‖quotientEta parameters (4+grade) source‖+
      (1+physicalBudget parameters field rho epsilon (10+grade))*‖quotientEta parameters 4 source‖ :=
    add_nonneg (norm_nonneg _) (mul_nonneg (add_nonneg zero_le_one (physicalBudget_nonnegative _ _ _ _ _)) (norm_nonneg _))
  apply (sq_le_sq₀ (mul_nonneg budget0 (mul_nonneg curve0 (originalGradeNorm_nonnegative _ _)))
    (mul_nonneg (mul_nonneg curve0 allocation0) total0)).mpr
  have middle : originalGradeNorm (4+(grade-order)) (source row)≤‖quotientEta parameters (4+(grade-order)) source‖ :=
    originalScalarCore_norm_le parameters (4+(grade-order)) source row
  have payment := (mul_le_mul_of_nonneg_left middle budget0).trans (allocate parameters field rho epsilon source low)
  have result := mul_le_mul_of_nonneg_left payment curve0
  dsimp only [budget] at result ⊢
  nlinarith only [result]

end Grad.OriginalTerminalAllocation
