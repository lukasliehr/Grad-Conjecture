import GC14ActualFrameProof

noncomputable section

set_option maxHeartbeats 800000

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

/-- The complete CT_GC14 single output: the original AP18 coefficient
adapter together with the literal actual-state AP20–AP21 construction. -/
theorem actualPhysicalCoefficientBlock : AP18Goal ∧ ActualFrameGoal :=
  ⟨ap18Goal, actualFrameGoal⟩

def actualPrimitiveLowRadius (parameters : PhaseParameters) (L radius : ℝ) : ℝ :=
  (4 * (actualFrameConstant parameters L radius 0 + 1))⁻¹

theorem actualPrimitiveLowRadius_positive (parameters : PhaseParameters) {L : ℝ} (positive : 0 < L)
    (radius : ℝ) : 0 < actualPrimitiveLowRadius parameters L radius := by
  have constant := actualFrameConstant_nonnegative parameters positive radius 0
  unfold actualPrimitiveLowRadius
  positivity

/-- A single finite `B10` neighborhood gives the base primitive coefficient
margin. No condition on an arbitrarily high grade appears here. -/
theorem actualPrimitive_low_margin {L ell radius : ℝ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (radiusNonnegative : 0 ≤ radius) (rho alpha delta parameter epsilon : ℝ)
    (rhoSmall : |rho| ≤ 1) (alphaSmall : |alpha| ≤ radius) (deltaSmall : |delta| ≤ radius)
    (parameterSmall : |parameter| ≤ radius) (epsilonSmall : |epsilon| ≤ 1)
    (field : ACore parameters 3)
    (low : stateBudget parameters (GradeCore.ofCoreLinear (grade := 10) field) rho epsilon ≤
      actualPrimitiveLowRadius parameters L radius) :
    let coefficients := actualFrameCoefficients parameters admissible rho alpha delta parameter epsilon
      (GradeCore.ofCoreLinear (grade := 4) field)
    ‖coefficients.frameDeviation‖ + ‖coefficients.seedDeviation‖ + ‖coefficients.seedDerivative‖ ≤ 1 / 4 := by
  have gradeBound := cartesianGrade_norm_mono (dimension := 3) parameters (by norm_num : 4 ≤ 10) field
  have budget : stateBudget parameters (GradeCore.ofCoreLinear (grade := 4) field) rho epsilon ≤
      actualPrimitiveLowRadius parameters L radius := by
    unfold stateBudget at low ⊢
    linarith
  have constant := actualFrameConstant_nonnegative parameters admissible.1 radius 0
  have denominator : 0 < 4 * (actualFrameConstant parameters L radius 0 + 1) := by positivity
  have scalarBound : actualFrameConstant parameters L radius 0 *
      actualPrimitiveLowRadius parameters L radius ≤ 1 / 4 := by
    unfold actualPrimitiveLowRadius
    rw [← div_eq_mul_inv]
    apply (div_le_iff₀ denominator).mpr
    linarith
  exact (actualFrameCoefficients_norm_bound parameters admissible radiusNonnegative rho alpha delta parameter epsilon
    rhoSmall alphaSmall deltaSmall parameterSmall epsilonSmall (GradeCore.ofCoreLinear (grade := 4) field)).trans
      ((mul_le_mul_of_nonneg_left budget constant).trans scalarBound)

end Grad.GaugeCoefficients.Physical.Frame
