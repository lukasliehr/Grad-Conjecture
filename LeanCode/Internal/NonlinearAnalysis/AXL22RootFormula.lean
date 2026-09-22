import AXL21ReferenceLift
import RootUnitConsumer

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1000000

open Filter
open scoped Topology ComplexConjugate

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearRange

variable {parameters : PhaseParameters}

theorem tangentQuadratic_hasEnvDerivAt (base direction : TangentCoefficient parameters) :
    HasEnvDerivAt (fun scalar : ℝ => tangentQuadratic (base + (scalar : ℂ) • direction))
      (tangentDot base direction) := by
  have component (index : Fin 2) :=
    hasEnvDerivAt_affine (tangentComponent base index) (tangentComponent direction index)
  have result := ((component 0).mul (component 0) |>.add ((component 1).mul (component 1))).const_smul ((2 : ℂ)⁻¹)
  have curve : HasEnvDerivAt
      (fun scalar : ℝ => tangentQuadratic (base + (scalar : ℂ) • direction)) _ :=
    result.congr_curve (by
      intro scalar
      simp only [tangentQuadratic, tangentDot, tangentComponent_add, tangentComponent_smul])
  apply curve.congr_derivative
  simp only [Complex.ofReal_zero, zero_smul, add_zero]
  rw [tangentDot]
  algebra

theorem envDerivative_zero_of_eventually_constant
    {curve : ℝ → TameCoefficient parameters} {derivative : TameCoefficient parameters}
    (genuine : HasEnvDerivAt curve derivative)
    (constant : ∀ᶠ scalar : ℝ in 𝓝 0, curve scalar = curve 0) : derivative = 0 := by
  apply Subtype.ext
  funext cell
  have limit := envDerivative_cell_limit genuine cell
  have zeroLimit : Tendsto (fun scalar : ℝ => (scalar : ℂ)⁻¹ *
      ((curve scalar).val cell - (curve 0).val cell)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [constant.filter_mono nhdsWithin_le_nhds] with scalar equal
    rw [equal, sub_self, mul_zero]
  exact tendsto_nhds_unique limit zeroLimit

/-- Differentiating the proved quadratic normalization gives the exact
coefficient identity, with its nonzero transverse root derivative retained. -/
theorem rootDerivativeFamily_normalization (base direction : TangentCoefficient parameters)
    (realBase : RealTangent base) (realDirection : RealTangent direction)
    (axis : RootAxisCondition base) :
    rootDerivativeFamily 1 base (fun _ => direction) * rootChart base +
      rootChart base * rootDerivativeFamily 1 base (fun _ => direction) + tangentDot base direction = 0 := by
  have root := rootDerivativeFamily_genuine 0 base (fun _ => direction) axis
  simp only [rootDerivativeFamily_zero] at root
  have derivative := (root.mul root).add (tangentQuadratic_hasEnvDerivAt base direction)
  simp only [Complex.ofReal_zero, zero_smul, add_zero] at derivative
  apply envDerivative_zero_of_eventually_constant derivative
  filter_upwards [rootAxisCondition_line base direction axis] with scalar inside
  have moved := rootChart_square (base + (scalar : ℂ) • direction)
    (RealTangent.line realBase realDirection scalar) inside
  have original := rootChart_square base realBase axis
  simpa only [Complex.ofReal_zero, zero_smul, add_zero, pow_two] using moved.trans original.symm

/-- The literal AL2/AL15 coefficient formula, at every axial point. The
denominator is the already proved positive root, never a new assumption. -/
theorem rootDerivativeFamily_value_formula (base direction : TangentCoefficient parameters)
    (realBase : RealTangent base) (realDirection : RealTangent direction)
    (axis : RootAxisCondition base) (angle : ℝ) :
    coefficientValue (rootDerivativeFamily 1 base (fun _ => direction)) angle =
      -(planarValue base angle 0 * planarValue direction angle 0 +
        planarValue base angle 1 * planarValue direction angle 1) /
        (2 * coefficientValue (rootChart base) angle) := by
  have identity := congrArg (coefficientValueHom angle)
    (rootDerivativeFamily_normalization base direction realBase realDirection axis)
  simp only [map_add, map_mul, map_zero, coefficientValueHom_apply,
    coefficientValue_tangentDot] at identity
  have nonzero : coefficientValue (rootChart base) angle ≠ 0 := by
    intro zero
    have positive := (rootChart_pointwise_positive parameters base realBase axis angle).2.2
    rw [zero, Complex.zero_re] at positive
    exact (lt_irrefl 0) positive
  apply (eq_div_iff (mul_ne_zero (by norm_num) nonzero)).2
  linear_combination identity

end Grad.ChartAxisLift
