import AAG20BoundedComplexInverse

noncomputable section
set_option maxHeartbeats 1000000

namespace Grad.AnnularVariational

open Grad.CartesianState

section Consumer
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

/-- Actual annular AG19: every independently prescribed sharp inner value
and undifferentiated physical forcing has exactly one solution in the
original completed energy space. The test space is the literal inner-trace
kernel, whose finite smooth inner-zero core is proved dense in AAG19. -/
theorem annularProblem_existsUnique (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    ∃! field : annularEnergySpace lower length positive,
      annularEnergyTrace lower length positive bounded lengthPositive 0 field = innerValue ∧
        ∀ test : annularInnerZero lower length positive bounded lengthPositive,
          annularFormValue parameters lower length positive lengthPositive widthHalf widthLength field test.val =
            annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source test.val := by
  refine ⟨annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue, ?_, ?_⟩
  · exact ⟨annularVariationalSolution_inner parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue,
      annularVariationalSolution_weak parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue⟩
  · intro candidate laws
    exact annularVariationalSolution_unique parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue candidate laws.1 laws.2

theorem annularProblem_inverse_norm :
    ‖annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength‖ ≤
      annularInverseConstant lower length := by
  apply ContinuousLinearMap.opNorm_le_bound _
  · unfold annularInverseConstant
    have trace : 0 ≤ annularTraceConstant lower length := Real.sqrt_nonneg _
    have lift : 0 ≤ annularInnerLiftConstant lower length := Real.sqrt_nonneg _
    positivity
  · exact annularVariationalLinear_bound parameters lower length positive bounded lengthPositive widthHalf widthLength

/-- AG20, retaining the physical bulk and sharp boundary norms separately. -/
theorem annularProblem_physical_bound (source : AnnularForcing lower) (innerValue : AnnularBoundary) :
    ‖annularVariationalInverse parameters lower length positive bounded lengthPositive widthHalf widthLength (source, innerValue)‖ ≤
      annularInnerLiftConstant lower length * ‖innerValue‖ +
        (4 / 3 : ℝ) * (3 * ‖source.1‖ + ‖source.2.1‖ + ‖source.2.2.1‖ +
          annularTraceConstant lower length * ‖source.2.2.2‖ +
          4 * annularInnerLiftConstant lower length * ‖innerValue‖) :=
  annularVariationalSolution_bound parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue

end Consumer

end Grad.AnnularVariational
