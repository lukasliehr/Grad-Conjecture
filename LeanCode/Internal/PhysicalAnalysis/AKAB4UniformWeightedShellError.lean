import AKAB3WeightedAxisShellError

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter MeasureTheory
open scoped Topology ENNReal

namespace Grad.WeightedAxisRemoval

theorem weightedAxisShellError_coefficient_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (epsilon : ℝ) (positive : 0 < epsilon) (constant : ℝ) (constantNonnegative : 0 ≤ constant)
    (weighted : ℝ → F) (error : ℝ → E)
    (squareIntegrable : MemLp weighted 2 (volume.restrict (Ioc epsilon (2 * epsilon))))
    (measurable : AEStronglyMeasurable error (volume.restrict (Ioc epsilon (2 * epsilon))))
    (pointwise : ∀ᵐ radius ∂volume.restrict (Ioc epsilon (2 * epsilon)),
      ‖error radius‖ ≤ constant * ((epsilon⁻¹ * radius) * radius ^ (7 / 4 : ℝ) * ‖weighted radius‖)) :
    ‖∫ radius in Ioc epsilon (2 * epsilon), error radius‖ ≤
      constant * ((2 * (2 : ℝ) ^ (7 / 4 : ℝ)) * epsilon ^ (9 / 4 : ℝ) *
        Real.sqrt (∫ radius in Ioc epsilon (2 * epsilon), ‖weighted radius‖ ^ 2)) := by
  have scaled := weightedAxisShellError_bound epsilon positive (fun radius => constant • weighted radius) error
    (squareIntegrable.const_smul constant) measurable (by
      filter_upwards [pointwise] with radius bound
      simpa only [norm_smul,Real.norm_of_nonneg constantNonnegative] using
        bound.trans_eq (by ring))
  have energy : (∫ radius in Ioc epsilon (2 * epsilon), ‖constant • weighted radius‖ ^ 2) =
      constant ^ 2 * (∫ radius in Ioc epsilon (2 * epsilon), ‖weighted radius‖ ^ 2) := by
    simp only [norm_smul,Real.norm_of_nonneg constantNonnegative,mul_pow]
    exact integral_const_mul _ _
  rw [energy, Real.sqrt_mul (sq_nonneg constant), Real.sqrt_sq constantNonnegative] at scaled
  exact scaled.trans_eq (by ring)

theorem weightedAxisShellError_uniform_bound {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (epsilon : ℝ) (positive : 0 < epsilon) (constant K : ℝ)
    (constantNonnegative : 0 ≤ constant) (Knonnegative : 0 ≤ K)
    (weighted : ℝ → F) (error : ℝ → E)
    (squareIntegrable : MemLp weighted 2 (volume.restrict (Ioc epsilon (2 * epsilon))))
    (energyBound : (∫ radius in Ioc epsilon (2 * epsilon), ‖weighted radius‖ ^ 2) ≤ K ^ 2)
    (measurable : AEStronglyMeasurable error (volume.restrict (Ioc epsilon (2 * epsilon))))
    (pointwise : ∀ᵐ radius ∂volume.restrict (Ioc epsilon (2 * epsilon)),
      ‖error radius‖ ≤ constant * ((epsilon⁻¹ * radius) * radius ^ (7 / 4 : ℝ) * ‖weighted radius‖)) :
    ‖∫ radius in Ioc epsilon (2 * epsilon), error radius‖ ≤
      (constant * (2 * (2 : ℝ) ^ (7 / 4 : ℝ)) * K) * epsilon ^ (9 / 4 : ℝ) := by
  have bound := weightedAxisShellError_coefficient_bound epsilon positive constant constantNonnegative
    weighted error squareIntegrable measurable pointwise
  have energy : Real.sqrt (∫ radius in Ioc epsilon (2 * epsilon), ‖weighted radius‖ ^ 2) ≤ K := by
    exact (Real.sqrt_le_sqrt energyBound).trans_eq (Real.sqrt_sq Knonnegative)
  apply bound.trans
  calc
    _ ≤ constant * ((2 * (2 : ℝ) ^ (7 / 4 : ℝ)) * epsilon ^ (9 / 4 : ℝ) * K) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left energy (by positivity)) constantNonnegative
    _ = _ := by ring

end Grad.WeightedAxisRemoval
