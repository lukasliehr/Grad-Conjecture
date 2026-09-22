import ACE7VolterraPositiveKernel

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial
open Grad.NonlinearProduct

theorem powerDilationJet_derivative_uniform {dimension order : ℕ} (power : ℕ) (field : ClosedJet dimension)
    (word : CartesianWord order) :
    ‖closedDerivative (powerDilationJet power field) order word‖ ≤
      ‖closedDerivative field order word‖ / (power + 1 : ℝ) := by
  apply (powerDilationJet_derivative_norm power field word).trans
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < power + order + 1)
    (by positivity : (0 : ℝ) < power + 1)).mpr
  nlinarith [norm_nonneg (closedDerivative field order word), (Nat.cast_nonneg order : (0 : ℝ) ≤ order)]

/-- Every Cartesian derivative of the positive kernel has exactly the W6
factorial mass as a uniform operator majorant. -/
theorem positiveKernel_derivative_norm {dimension order : ℕ} (count : ℕ) (field : ClosedJet dimension)
    (word : CartesianWord order) :
    ‖closedDerivative (positiveKernel count field) order word‖ ≤
      kernelMass count * ‖closedDerivative field order word‖ := by
  induction count with
  | zero => simp only [positiveKernel_zero, kernelMass_zero, one_mul, le_refl]
  | succ count inductionHypothesis =>
    change ‖closedDerivative (powerDilationJet (2 * count + 1)
      (powerDilationJet (2 * count + 3) (positiveKernel count field))) order word‖ ≤ _
    calc
      _ ≤ ‖closedDerivative (powerDilationJet (2 * count + 3) (positiveKernel count field)) order word‖ /
          ((2 * count + 1 : ℕ) + 1 : ℝ) := powerDilationJet_derivative_uniform _ _ word
      _ ≤ (‖closedDerivative (positiveKernel count field) order word‖ / ((2 * count + 3 : ℕ) + 1 : ℝ)) /
          ((2 * count + 1 : ℕ) + 1 : ℝ) :=
        div_le_div_of_nonneg_right (powerDilationJet_derivative_uniform _ _ word) (by positivity)
      _ ≤ (kernelMass count * ‖closedDerivative field order word‖ / ((2 * count + 3 : ℕ) + 1 : ℝ)) /
          ((2 * count + 1 : ℕ) + 1 : ℝ) :=
        div_le_div_of_nonneg_right (div_le_div_of_nonneg_right inductionHypothesis (by positivity)) (by positivity)
      _ = kernelMass (count + 1) * ‖closedDerivative field order word‖ := by
        rw [kernelMass_succ]
        push_cast
        field_simp
        ring

end Grad.ActualCenterVolterra
