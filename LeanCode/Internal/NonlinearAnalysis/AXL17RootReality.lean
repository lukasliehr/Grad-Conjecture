import AXL16OuterConstraint
import RootUnitTower

noncomputable section

set_option maxHeartbeats 1000000

open Filter
open scoped Topology ComplexConjugate

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange Grad.Q24Realization

variable {parameters : PhaseParameters}

theorem rootAxisCondition_line (base direction : TangentCoefficient parameters)
    (axis : RootAxisCondition base) :
    ∀ᶠ scalar : ℝ in 𝓝 0, RootAxisCondition (base + (scalar : ℂ) • direction) := by
  have continuous : Continuous (fun scalar : ℝ =>
      ‖tangentToGrade parameters 1 base + (scalar : ℂ) • tangentToGrade parameters 1 direction‖) :=
    (continuous_const.add (Complex.continuous_ofReal.smul continuous_const)).norm
  have near : ∀ᶠ scalar : ℝ in 𝓝 0,
      ‖tangentToGrade parameters 1 base + (scalar : ℂ) • tangentToGrade parameters 1 direction‖ <
        (2 * axisConstant)⁻¹ :=
    (isOpen_lt continuous continuous_const).mem_nhds
      (by simpa only [Set.mem_ofPred_eq, Complex.ofReal_zero, zero_smul, add_zero,
        tangentToGrade_norm, RootAxisCondition] using axis)
  filter_upwards [near] with scalar inside
  change tangentNorm 1 (base + (scalar : ℂ) • direction) < _
  rw [← tangentToGrade_norm, map_add, map_smul]
  exact inside

theorem RealTangent.line {base direction : TangentCoefficient parameters}
    (realBase : RealTangent base) (realDirection : RealTangent direction) (scalar : ℝ) :
    RealTangent (base + (scalar : ℂ) • direction) := by
  intro cell coordinate
  change base.val (-cell) coordinate + (scalar : ℂ) * direction.val (-cell) coordinate =
    conj (base.val cell coordinate + (scalar : ℂ) * direction.val cell coordinate)
  rw [realBase, realDirection, map_add, map_mul, Complex.conj_ofReal]

theorem envDerivative_cell_limit {curve : ℝ → TameCoefficient parameters}
    {derivative : TameCoefficient parameters} (genuine : HasEnvDerivAt curve derivative) (cell : ℤ) :
    Tendsto (fun scalar : ℝ => ((scalar : ℂ)⁻¹) * ((curve scalar).val cell - (curve 0).val cell))
      (𝓝[≠] (0 : ℝ)) (𝓝 (derivative.val cell)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ (genuine 0)
  intro scalar
  exact norm_le_tameEnvelope ((((scalar : ℂ)⁻¹) • (curve scalar - curve 0)) - derivative).property 0 cell

theorem envDerivative_real {curve : ℝ → TameCoefficient parameters}
    {derivative : TameCoefficient parameters} (genuine : HasEnvDerivAt curve derivative)
    (atZero : ∀ cell, (curve 0).val (-cell) = conj ((curve 0).val cell))
    (near : ∀ᶠ scalar : ℝ in 𝓝 0, ∀ cell, (curve scalar).val (-cell) = conj ((curve scalar).val cell)) :
    ∀ cell, derivative.val (-cell) = conj (derivative.val cell) := by
  intro cell
  have first := envDerivative_cell_limit genuine (-cell)
  have second := Complex.continuous_conj.tendsto (derivative.val cell) |>.comp (envDerivative_cell_limit genuine cell)
  apply tendsto_nhds_unique first
  apply second.congr'
  filter_upwards [near.filter_mono nhdsWithin_le_nhds] with scalar real
  simp only [Function.comp_apply, map_mul, map_inv₀, Complex.conj_ofReal, map_sub,
    real cell, atZero cell]

/-- The actual root derivative coefficient is real for arbitrary real
directions at every original real Q13 base. -/
theorem rootDerivativeFamily_one_real (base direction : TangentCoefficient parameters)
    (realBase : RealTangent base) (realDirection : RealTangent direction)
    (axis : RootAxisCondition base) :
    ∀ cell, (rootDerivativeFamily 1 base (fun _ => direction)).val (-cell) =
      conj ((rootDerivativeFamily 1 base (fun _ => direction)).val cell) := by
  have genuine := rootDerivativeFamily_genuine 0 base (fun _ => direction) axis
  simp only [rootDerivativeFamily_zero] at genuine
  apply envDerivative_real genuine
  · simpa only [Complex.ofReal_zero, zero_smul, add_zero] using rootChart_real base realBase axis
  · filter_upwards [rootAxisCondition_line base direction axis] with scalar inside
    exact rootChart_real _ (RealTangent.line realBase realDirection scalar) inside

end Grad.ChartAxisLift
