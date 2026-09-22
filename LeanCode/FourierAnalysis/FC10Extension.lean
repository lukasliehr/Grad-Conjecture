import FC9Proof
import Mathlib.Topology.Algebra.LinearMapCompletion

noncomputable section

open Set

namespace Grad.CartesianState

/-- A specified bounded complex-linear core map, bundled with exactly the
bound supplied by the caller. -/
def denseCoreContinuousMap {dimension grade : ℕ} (parameters : PhaseParameters)
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]
    (coreMap : GradeCore parameters dimension grade →ₗ[ℂ] Target)
    (boundConstant : ℝ)
    (coreBound : ∀ field, ‖coreMap field‖ ≤ boundConstant * ‖field‖) :
    GradeCore parameters dimension grade →L[ℂ] Target :=
  coreMap.mkContinuous boundConstant coreBound

theorem denseCoreContinuousMap_apply {dimension grade : ℕ}
    (parameters : PhaseParameters)
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]
    (coreMap : GradeCore parameters dimension grade →ₗ[ℂ] Target)
    (boundConstant : ℝ)
    (coreBound : ∀ field, ‖coreMap field‖ ≤ boundConstant * ‖field‖)
    (field : GradeCore parameters dimension grade) :
    denseCoreContinuousMap parameters coreMap boundConstant coreBound field =
      coreMap field := rfl

/-- The constructed continuous-linear extension from the actual `AGrade`
completion into a specified complete target. -/
def denseCoreExtension {dimension grade : ℕ} (parameters : PhaseParameters)
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]
    [CompleteSpace Target]
    (coreMap : GradeCore parameters dimension grade →ₗ[ℂ] Target)
    (boundConstant : ℝ)
    (coreBound : ∀ field, ‖coreMap field‖ ≤ boundConstant * ‖field‖) :
    AGrade parameters dimension grade →L[ℂ] Target :=
  (denseCoreContinuousMap parameters coreMap boundConstant coreBound).fromCompletion

/-- Exact core law on the literal COR09 embedding `eta_q`. -/
theorem denseCoreExtension_apply_eta {dimension grade : ℕ}
    (parameters : PhaseParameters)
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]
    [CompleteSpace Target]
    (coreMap : GradeCore parameters dimension grade →ₗ[ℂ] Target)
    (boundConstant : ℝ)
    (coreBound : ∀ field, ‖coreMap field‖ ≤ boundConstant * ‖field‖)
    (field : GradeCore parameters dimension grade) :
    denseCoreExtension parameters coreMap boundConstant coreBound
        (aGradeEta parameters field) = coreMap field := by
  change (denseCoreContinuousMap parameters coreMap boundConstant coreBound).fromCompletion
      (field : UniformSpace.Completion
        (GradeCore parameters dimension grade)) = coreMap field
  rw [ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

/-- The supplied core bound extends pointwise to the entire completion with
the same constant. -/
theorem denseCoreExtension_apply_norm_le {dimension grade : ℕ}
    (parameters : PhaseParameters)
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]
    [CompleteSpace Target]
    (coreMap : GradeCore parameters dimension grade →ₗ[ℂ] Target)
    (boundConstant : ℝ)
    (coreBound : ∀ field, ‖coreMap field‖ ≤ boundConstant * ‖field‖)
    (point : AGrade parameters dimension grade) :
    ‖denseCoreExtension parameters coreMap boundConstant coreBound point‖ ≤
      boundConstant * ‖point‖ := by
  refine UniformSpace.Completion.induction_on point
    (isClosed_le (by fun_prop) (by fun_prop)) ?_
  intro field
  change
    ‖denseCoreExtension parameters coreMap boundConstant coreBound
        (aGradeEta parameters field)‖ ≤
      boundConstant * ‖aGradeEta parameters field‖
  rw [denseCoreExtension_apply_eta, aGradeEta_norm]
  exact coreBound field

/-- The constructed extension has operator norm at most the exact supplied
constant. -/
theorem denseCoreExtension_norm_le {dimension grade : ℕ}
    (parameters : PhaseParameters)
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]
    [CompleteSpace Target]
    (coreMap : GradeCore parameters dimension grade →ₗ[ℂ] Target)
    (boundConstant : ℝ) (boundNonnegative : 0 ≤ boundConstant)
    (coreBound : ∀ field, ‖coreMap field‖ ≤ boundConstant * ‖field‖) :
    ‖denseCoreExtension parameters coreMap boundConstant coreBound‖ ≤
      boundConstant := by
  apply ContinuousLinearMap.opNorm_le_bound _ boundNonnegative
  exact denseCoreExtension_apply_norm_le parameters coreMap boundConstant
    coreBound

/-- Two continuous complex-linear maps out of `AGrade` that agree on the
literal dense core embedding agree everywhere. -/
theorem denseCoreContinuousLinearMap_ext {dimension grade : ℕ}
    (parameters : PhaseParameters)
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]
    (first second : AGrade parameters dimension grade →L[ℂ] Target)
    (coreAgreement : ∀ field : GradeCore parameters dimension grade,
      first (aGradeEta parameters field) =
        second (aGradeEta parameters field)) :
    first = second := by
  apply DFunLike.ext first second
  intro point
  have functionEquality := (aGradeEta_denseRange parameters).equalizer
    first.continuous second.continuous (by
      funext field
      change first (aGradeEta parameters field) =
        second (aGradeEta parameters field)
      exact coreAgreement field)
  exact congrFun functionEquality point

/-- Uniqueness among all continuous-linear maps with the same specified core
law; the desired completed identity is not assumed. -/
theorem denseCoreExtension_unique {dimension grade : ℕ}
    (parameters : PhaseParameters)
    {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]
    [CompleteSpace Target]
    (coreMap : GradeCore parameters dimension grade →ₗ[ℂ] Target)
    (boundConstant : ℝ)
    (coreBound : ∀ field, ‖coreMap field‖ ≤ boundConstant * ‖field‖)
    (other : AGrade parameters dimension grade →L[ℂ] Target)
    (otherCoreLaw : ∀ field,
      other (aGradeEta parameters field) = coreMap field) :
    other = denseCoreExtension parameters coreMap boundConstant coreBound := by
  apply denseCoreContinuousLinearMap_ext parameters
  intro field
  rw [otherCoreLaw, denseCoreExtension_apply_eta]

/-- The literal core map obtained by postcomposing with one specified
continuous-linear map. -/
def postcomposedCoreMap {dimension grade : ℕ} (parameters : PhaseParameters)
    {FirstTarget SecondTarget : Type*}
    [NormedAddCommGroup FirstTarget] [NormedSpace ℂ FirstTarget]
    [NormedAddCommGroup SecondTarget] [NormedSpace ℂ SecondTarget]
    (postMap : FirstTarget →L[ℂ] SecondTarget)
    (coreMap : GradeCore parameters dimension grade →ₗ[ℂ] FirstTarget) :
    GradeCore parameters dimension grade →ₗ[ℂ] SecondTarget :=
  postMap.toLinearMap.comp coreMap

theorem postcomposedCoreMap_apply {dimension grade : ℕ}
    (parameters : PhaseParameters)
    {FirstTarget SecondTarget : Type*}
    [NormedAddCommGroup FirstTarget] [NormedSpace ℂ FirstTarget]
    [NormedAddCommGroup SecondTarget] [NormedSpace ℂ SecondTarget]
    (postMap : FirstTarget →L[ℂ] SecondTarget)
    (coreMap : GradeCore parameters dimension grade →ₗ[ℂ] FirstTarget)
    (field : GradeCore parameters dimension grade) :
    postcomposedCoreMap parameters postMap coreMap field =
      postMap (coreMap field) := rfl

theorem postcomposedCoreMap_bound {dimension grade : ℕ}
    (parameters : PhaseParameters)
    {FirstTarget SecondTarget : Type*}
    [NormedAddCommGroup FirstTarget] [NormedSpace ℂ FirstTarget]
    [NormedAddCommGroup SecondTarget] [NormedSpace ℂ SecondTarget]
    (postMap : FirstTarget →L[ℂ] SecondTarget)
    (coreMap : GradeCore parameters dimension grade →ₗ[ℂ] FirstTarget)
    (boundConstant : ℝ)
    (coreBound : ∀ field, ‖coreMap field‖ ≤ boundConstant * ‖field‖)
    (field : GradeCore parameters dimension grade) :
    ‖postcomposedCoreMap parameters postMap coreMap field‖ ≤
      (‖postMap‖ * boundConstant) * ‖field‖ := by
  calc
    ‖postcomposedCoreMap parameters postMap coreMap field‖ =
        ‖postMap (coreMap field)‖ := rfl
    _ ≤ ‖postMap‖ * ‖coreMap field‖ := postMap.le_opNorm (coreMap field)
    _ ≤ ‖postMap‖ * (boundConstant * ‖field‖) :=
      mul_le_mul_of_nonneg_left (coreBound field) (norm_nonneg postMap)
    _ = (‖postMap‖ * boundConstant) * ‖field‖ := by ring

/-- Extend the literally postcomposed core map, with its derived finite
composition bound. -/
def postcomposedDenseCoreExtension {dimension grade : ℕ}
    (parameters : PhaseParameters)
    {FirstTarget SecondTarget : Type*}
    [NormedAddCommGroup FirstTarget] [NormedSpace ℂ FirstTarget]
    [NormedAddCommGroup SecondTarget] [NormedSpace ℂ SecondTarget]
    [CompleteSpace SecondTarget]
    (postMap : FirstTarget →L[ℂ] SecondTarget)
    (coreMap : GradeCore parameters dimension grade →ₗ[ℂ] FirstTarget)
    (boundConstant : ℝ)
    (coreBound : ∀ field, ‖coreMap field‖ ≤ boundConstant * ‖field‖) :
    AGrade parameters dimension grade →L[ℂ] SecondTarget :=
  denseCoreExtension parameters (postcomposedCoreMap parameters postMap coreMap)
    (‖postMap‖ * boundConstant)
    (postcomposedCoreMap_bound parameters postMap coreMap boundConstant coreBound)

/-- A genuinely specified finite composition identity: extending the literal
core postcomposition equals postcomposing the constructed extension. -/
theorem denseCoreExtension_postcomp {dimension grade : ℕ}
    (parameters : PhaseParameters)
    {FirstTarget SecondTarget : Type*}
    [NormedAddCommGroup FirstTarget] [NormedSpace ℂ FirstTarget]
    [CompleteSpace FirstTarget]
    [NormedAddCommGroup SecondTarget] [NormedSpace ℂ SecondTarget]
    [CompleteSpace SecondTarget]
    (postMap : FirstTarget →L[ℂ] SecondTarget)
    (coreMap : GradeCore parameters dimension grade →ₗ[ℂ] FirstTarget)
    (boundConstant : ℝ)
    (coreBound : ∀ field, ‖coreMap field‖ ≤ boundConstant * ‖field‖) :
    postcomposedDenseCoreExtension parameters postMap coreMap boundConstant coreBound =
      postMap.comp
        (denseCoreExtension parameters coreMap boundConstant coreBound) := by
  symm
  apply denseCoreExtension_unique parameters
    (postcomposedCoreMap parameters postMap coreMap)
    (‖postMap‖ * boundConstant)
    (postcomposedCoreMap_bound parameters postMap coreMap boundConstant coreBound)
  intro field
  rw [ContinuousLinearMap.comp_apply, denseCoreExtension_apply_eta]
  rfl

end Grad.CartesianState
