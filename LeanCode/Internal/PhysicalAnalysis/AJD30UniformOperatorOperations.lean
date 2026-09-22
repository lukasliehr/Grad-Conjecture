import AJD26UniformCoordinateCalculus
import AJD8ActualKnownZeroFunctionalPullback

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.AnnularKernelOrbit Grad.AnnularInverseCalculus

section Uniform
variable {Context : Type*} {E : Context → Type*}
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℝ (E context)]
  {budget : Context → ℕ → ℝ}

/-- Generic specialization keeps deep physical carrier inference outside
of the derivative-restriction rewrite. -/
theorem UniformCoordinateBound.of_ordered
    (family : (context : Context) → OrbitParameter → E context)
    (smooth : ∀ context, ContDiff ℝ ∞ (family context))
    (bound : ∀ axis order, ∃ constant : ℝ, 0 ≤ constant ∧ ∀ context point,
      ‖orderedOrbitDerivative (List.replicate order axis) (family context) point‖ ≤
        constant * coordinateJetWeight (budget context) order) :
    UniformCoordinateBound budget family := by
  intro axis order
  obtain ⟨constant, nonnegative, estimate⟩ := bound axis order
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  have same := Grad.AnnularOrbitGenerators.iteratedDeriv_axis_restriction (family context)
    (smooth context) axis base order time
  rw [same]
  exact estimate context _

theorem UniformCoordinateBound.const (budgetNonnegative : ∀ context n, 0 ≤ budget context n)
    (value : (context : Context) → E context) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ∀ context, ‖value context‖ ≤ constant) :
    UniformCoordinateBound budget (fun context _ => value context) := by
  intro axis order
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  rw [iteratedDeriv_const]
  by_cases zero : order = 0
  · simpa only [if_pos zero, coordinateJetWeight, mul_one] using bound context
  · rw [if_neg zero, norm_zero, coordinateJetWeight, if_neg zero]
    exact mul_nonneg nonnegative (budgetNonnegative context order)

theorem UniformCoordinateBound.neg {family : (context : Context) → OrbitParameter → E context}
    (bound : UniformCoordinateBound budget family) (smooth : ∀ context, ContDiff ℝ ∞ (family context)) :
    UniformCoordinateBound budget (fun context tau => -family context tau) := by
  have mapped := bound.map smooth (fun context => -ContinuousLinearMap.id ℝ (E context)) 1 (by norm_num)
    (fun context => by simpa only [norm_neg] using ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E context))
  exact mapped
end Uniform

section PointwiseMap
variable {Context : Type*} {E F : Context → Type*}
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℝ (E context)]
  [∀ context, NormedAddCommGroup (F context)] [∀ context, NormedSpace ℝ (F context)]
  {budget : Context → ℕ → ℝ} {family : (context : Context) → OrbitParameter → E context}

theorem UniformCoordinateBound.map_bound (bound : UniformCoordinateBound budget family)
    (smooth : ∀ context, ContDiff ℝ ∞ (family context))
    (mapping : (context : Context) → E context →L[ℝ] F context)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (pointwise : ∀ context value, ‖mapping context value‖ ≤ constant * ‖value‖) :
    UniformCoordinateBound budget (fun context tau => mapping context (family context tau)) :=
  bound.map smooth mapping constant nonnegative
    (fun context => ContinuousLinearMap.opNorm_le_bound _ nonnegative (pointwise context))
end PointwiseMap

section Composition
variable {Context : Type*} {X E F : Context → Type*}
  [∀ context, NormedAddCommGroup (X context)] [∀ context, NormedSpace ℂ (X context)]
  [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℂ (E context)]
  [∀ context, NormedAddCommGroup (F context)] [∀ context, NormedSpace ℂ (F context)]
  {budget : Context → ℕ → ℝ}

def complexPrecomposition (context : Context) (input : X context →L[ℂ] E context) :
    (E context →L[ℂ] F context) →L[ℝ] (X context →L[ℂ] F context) :=
  ((ContinuousLinearMap.compL ℂ (X context) (E context) (F context)).flip input).restrictScalars ℝ

def complexPostcomposition (context : Context) (output : E context →L[ℂ] F context) :
    (X context →L[ℂ] E context) →L[ℝ] (X context →L[ℂ] F context) :=
  ((ContinuousLinearMap.compL ℂ (X context) (E context) (F context)) output).restrictScalars ℝ

theorem UniformCoordinateBound.precomposeComplex
    {family : (context : Context) → OrbitParameter → E context →L[ℂ] F context}
    (bound : UniformCoordinateBound budget family) (smooth : ∀ context, ContDiff ℝ ∞ (family context))
    (input : (context : Context) → X context →L[ℂ] E context)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (inputBound : ∀ context, ‖input context‖ ≤ constant) :
    UniformCoordinateBound budget (fun context tau => (family context tau).comp (input context)) := by
  apply bound.map smooth (fun context => complexPrecomposition context (input context)) constant nonnegative
  intro context
  apply ContinuousLinearMap.opNorm_le_bound _ nonnegative
  intro operator
  exact (ContinuousLinearMap.opNorm_comp_le operator (input context)).trans
    ((mul_le_mul_of_nonneg_left (inputBound context) (norm_nonneg operator)).trans_eq (mul_comm _ _))

theorem UniformCoordinateBound.postcomposeComplex
    {family : (context : Context) → OrbitParameter → X context →L[ℂ] E context}
    (bound : UniformCoordinateBound budget family) (smooth : ∀ context, ContDiff ℝ ∞ (family context))
    (output : (context : Context) → E context →L[ℂ] F context)
    (constant : ℝ) (nonnegative : 0 ≤ constant) (outputBound : ∀ context, ‖output context‖ ≤ constant) :
    UniformCoordinateBound budget (fun context tau => (output context).comp (family context tau)) := by
  apply bound.map smooth (fun context => complexPostcomposition context (output context)) constant nonnegative
  intro context
  apply ContinuousLinearMap.opNorm_le_bound _ nonnegative
  intro operator
  exact (ContinuousLinearMap.opNorm_comp_le (output context) operator).trans
    (mul_le_mul_of_nonneg_right (outputBound context) (norm_nonneg operator))
end Composition

section Pairing
variable {X D V : Type*}
  [NormedAddCommGroup X] [NormedSpace ℂ X] [NormedSpace ℝ X] [IsScalarTower ℝ ℂ X]
  [NormedAddCommGroup D] [InnerProductSpace ℂ D]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
attribute [local instance] pairingRealInner
/-- The literal physical real pairing uses no additional operator norm loss. -/
theorem pairedComplexOperator_bound (test : V →L[ℝ] D) (mapping : X →L[ℂ] D) :
    ‖pairedComplexOperator test mapping‖ ≤ ‖test‖ * ‖mapping‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  intro source
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro field
  rw [pairedComplexOperator_apply, Real.norm_eq_abs]
  have paired := (Complex.abs_re_le_norm (inner ℂ (test field) (mapping source))).trans
    (norm_inner_le_norm (test field) (mapping source))
  exact paired.trans ((mul_le_mul (test.le_opNorm field) (mapping.le_opNorm source)
    (norm_nonneg _) (mul_nonneg (norm_nonneg test) (norm_nonneg field))).trans_eq (by ring))

end Pairing
end Grad.AnnularCrossOrbit
