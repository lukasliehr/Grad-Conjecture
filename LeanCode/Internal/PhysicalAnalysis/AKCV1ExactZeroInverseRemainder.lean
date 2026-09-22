import AKCT4OriginalNewtonParameterSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000

namespace Grad.NashMoser.BranchDerivative

variable {State Source : Type*}
    [AddCommGroup State] [Module ℝ State]
    [AddCommGroup Source] [Module ℝ Source]

section CoreAlgebra
variable {Parameter : Type*} [AddCommGroup Parameter] [Module ℝ Parameter]

/-- The literal first-order remainder of the nonlinear equation on its
smooth cores. No norm or fictitious Banach structure is imposed on a core. -/
def coreTaylorRemainder (mapping : Parameter → State → Source)
    (baseParameter pointParameter : Parameter) (baseState pointState : State)
    (parameterDerivative : Parameter →ₗ[ℝ] Source) (stateDerivative : State →ₗ[ℝ] Source) : Source :=
  mapping pointParameter pointState - mapping baseParameter baseState -
    parameterDerivative (pointParameter-baseParameter) - stateDerivative (pointState-baseState)

/-- Written NM11 equation (19), on the SAME smooth cores. Only the left
inverse identity is needed to recover the difference of two actual zeros. -/
theorem inverse_two_zero_difference
    (mapping : Parameter → State → Source)
    (baseParameter pointParameter : Parameter) (baseState pointState : State)
    (parameterDerivative : Parameter →ₗ[ℝ] Source) (stateDerivative : State →ₗ[ℝ] Source)
    (inverse : Source →ₗ[ℝ] State)
    (leftInverse : ∀ state, inverse (stateDerivative state) = state)
    (baseZero : mapping baseParameter baseState = 0)
    (pointZero : mapping pointParameter pointState = 0) :
    pointState-baseState - (-(inverse.comp parameterDerivative)) (pointParameter-baseParameter) =
      -inverse (coreTaylorRemainder mapping baseParameter pointParameter baseState pointState
        parameterDerivative stateDerivative) := by
  simp only [coreTaylorRemainder, pointZero, baseZero, sub_self, zero_sub,
    map_sub, map_neg, leftInverse, LinearMap.neg_apply, LinearMap.comp_apply]
  abel

end CoreAlgebra
section CompletedDerivative
variable {Parameter Output : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    [NormedAddCommGroup Output] [NormedSpace ℝ Output]

/-- The candidate derivative is the actual embedded core map -V DqPhi;
its displayed bound makes this parameter-linear map continuous. -/
def completedInverseParameterDerivative
    (embedding : State →ₗ[ℝ] Output) (inverse : Source →ₗ[ℝ] State)
    (parameterDerivative : Parameter →ₗ[ℝ] Source) (constant : ℝ)
    (bounded : ∀ direction,
      ‖embedding (inverse (parameterDerivative direction))‖ ≤ constant * ‖direction‖) :
    Parameter →L[ℝ] Output :=
  (-((embedding.comp inverse).comp parameterDerivative)).mkContinuous constant (by
    intro direction
    simpa only [LinearMap.neg_apply, LinearMap.comp_apply, norm_neg] using bounded direction)

theorem completedInverseParameterDerivative_apply
    (embedding : State →ₗ[ℝ] Output) (inverse : Source →ₗ[ℝ] State)
    (parameterDerivative : Parameter →ₗ[ℝ] Source) (constant : ℝ)
    (bounded : ∀ direction,
      ‖embedding (inverse (parameterDerivative direction))‖ ≤ constant * ‖direction‖)
    (direction : Parameter) :
    completedInverseParameterDerivative embedding inverse parameterDerivative constant bounded direction =
      -embedding (inverse (parameterDerivative direction)) := rfl

/-- Exact completed-grade remainder for the actual candidate -V DqPhi.
This lets uncomposed nonlinear Taylor estimates feed the NM11 derivative
argument, without assuming any regularity of the zero branch. -/
theorem completed_two_zero_remainder_norm
    (mapping : Parameter → State → Source)
    (baseParameter pointParameter : Parameter) (baseState pointState : State)
    (parameterDerivative : Parameter →ₗ[ℝ] Source) (stateDerivative : State →ₗ[ℝ] Source)
    (inverse : Source →ₗ[ℝ] State) (embedding : State →ₗ[ℝ] Output)
    (leftInverse : ∀ state, inverse (stateDerivative state) = state)
    (baseZero : mapping baseParameter baseState = 0)
    (pointZero : mapping pointParameter pointState = 0)
    (constant : ℝ) (bounded : ∀ direction,
      ‖embedding (inverse (parameterDerivative direction))‖ ≤ constant * ‖direction‖) :
    ‖embedding pointState-embedding baseState-
      completedInverseParameterDerivative embedding inverse parameterDerivative constant bounded
        (pointParameter-baseParameter)‖ =
    ‖embedding (inverse (coreTaylorRemainder mapping baseParameter pointParameter baseState pointState
        parameterDerivative stateDerivative))‖ := by
  have same := congrArg (fun state => ‖embedding state‖) (inverse_two_zero_difference mapping baseParameter pointParameter
    baseState pointState parameterDerivative stateDerivative inverse leftInverse baseZero pointZero)
  simpa only [map_sub, map_neg, LinearMap.neg_apply, LinearMap.comp_apply,
    completedInverseParameterDerivative_apply, norm_neg] using same

end CompletedDerivative
end Grad.NashMoser.BranchDerivative
