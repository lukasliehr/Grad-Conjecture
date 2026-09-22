import AEB7LiteralBWeightedCoercivity

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularTiltedReference
open Grad.CartesianState Grad.AnnularVariational

local instance tiltedZero_normedGroup (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length) :
    NormedAddCommGroup (annularInnerZero lower length positive collar lengthPositive) := inferInstance

local instance tiltedZero_seminormedGroup (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length) :
    SeminormedAddCommGroup (annularInnerZero lower length positive collar lengthPositive) :=
  (tiltedZero_normedGroup lower length positive collar lengthPositive).toSeminormedAddCommGroup

local instance tiltedZero_realNormedSpace (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length) :
    NormedSpace ℝ (annularInnerZero lower length positive collar lengthPositive) :=
  (annularInnerZero_realInner lower length positive collar lengthPositive).toNormedSpace

private theorem tilted_realCoercive_solution {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (form : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive form)
    (source : V →L[ℝ] ℝ) (test : V) :
    form (coercive.continuousLinearEquivOfBilin.symm
      ((InnerProductSpace.toDual ℝ V).symm source)) test = source test := by
  have equality := coercive.continuousLinearEquivOfBilin_apply
    (coercive.continuousLinearEquivOfBilin.symm ((InnerProductSpace.toDual ℝ V).symm source)) test
  rw [ContinuousLinearEquiv.apply_symm_apply, InnerProductSpace.toDual_symm_apply] at equality
  exact equality.symm

private theorem tilted_realCoercive_unique {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [CompleteSpace V]
    (form : V →L[ℝ] V →L[ℝ] ℝ) (coercive : IsCoercive form)
    (first second : V) (equality : ∀ test, form first test = form second test) : first = second := by
  apply coercive.continuousLinearEquivOfBilin.injective
  apply ext_inner_right ℝ
  intro test
  rw [coercive.continuousLinearEquivOfBilin_apply, coercive.continuousLinearEquivOfBilin_apply]
  exact equality test

section Inverse
variable (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (collar : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))

def annularTiltZeroForm : annularInnerZero lower length positive collar lengthPositive →L[ℝ]
    annularInnerZero lower length positive collar lengthPositive →L[ℝ] ℝ :=
  (annularTiltForm parameters lower length positive lengthPositive widthHalf widthLength).bilinearComp
    (annularZeroRealInclusion lower length positive collar lengthPositive)
    (annularZeroRealInclusion lower length positive collar lengthPositive)

theorem annularTiltZeroForm_coercive_bound
    (field : annularInnerZero lower length positive collar lengthPositive) :
    (1 / 16 : ℝ) * ‖field‖ ^ 2 ≤
      annularTiltZeroForm parameters lower length positive collar lengthPositive widthHalf widthLength field field :=
  annularTiltForm_coercive_bound parameters lower length positive lengthPositive widthHalf widthLength field.val

theorem annularTiltZeroForm_isCoercive :
    IsCoercive (annularTiltZeroForm parameters lower length positive collar lengthPositive widthHalf widthLength) := by
  refine ⟨1 / 16, by norm_num, fun field => ?_⟩
  simpa only [sq, mul_assoc] using annularTiltZeroForm_coercive_bound parameters lower length positive collar
    lengthPositive widthHalf widthLength field

/-- Constructed inverse of the actual tilted reference form on its original
zero-inner-trace space. The input is a continuous functional, not an inverse assumption. -/
def annularTiltDualInverse
    (source : annularInnerZero lower length positive collar lengthPositive →L[ℝ] ℝ) :
    annularInnerZero lower length positive collar lengthPositive :=
  (annularTiltZeroForm_isCoercive parameters lower length positive collar lengthPositive widthHalf widthLength).continuousLinearEquivOfBilin.symm
    ((InnerProductSpace.toDual ℝ (annularInnerZero lower length positive collar lengthPositive)).symm source)

theorem annularTiltDualInverse_solves
    (source : annularInnerZero lower length positive collar lengthPositive →L[ℝ] ℝ)
    (test : annularInnerZero lower length positive collar lengthPositive) :
    annularTiltZeroForm parameters lower length positive collar lengthPositive widthHalf widthLength
      (annularTiltDualInverse parameters lower length positive collar lengthPositive widthHalf widthLength source) test =
      source test :=
  tilted_realCoercive_solution _
    (annularTiltZeroForm_isCoercive parameters lower length positive collar lengthPositive widthHalf widthLength) _ test

/-- The reference inverse bound is independent of the inner radius and all
Fourier cutoffs, at the unchanged original analytic width. -/
theorem annularTiltDualInverse_bound
    (source : annularInnerZero lower length positive collar lengthPositive →L[ℝ] ℝ) :
    ‖annularTiltDualInverse parameters lower length positive collar lengthPositive widthHalf widthLength source‖ ≤
      16 * ‖source‖ := by
  let solution := annularTiltDualInverse parameters lower length positive collar lengthPositive widthHalf widthLength source
  have coercive := annularTiltZeroForm_coercive_bound parameters lower length positive collar lengthPositive
    widthHalf widthLength solution
  rw [annularTiltDualInverse_solves] at coercive
  have estimate := (le_abs_self (source solution)).trans (source.le_opNorm solution)
  by_cases zero : ‖solution‖ = 0
  · change ‖solution‖ ≤ _
    rw [zero]
    positivity
  · have positiveNorm : 0 < ‖solution‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm zero)
    change ‖solution‖ ≤ _
    nlinarith only [coercive, estimate, positiveNorm]

theorem annularTiltDualInverse_unique
    (source : annularInnerZero lower length positive collar lengthPositive →L[ℝ] ℝ)
    (candidate : annularInnerZero lower length positive collar lengthPositive)
    (equation : ∀ test, annularTiltZeroForm parameters lower length positive collar lengthPositive
      widthHalf widthLength candidate test = source test) :
    candidate = annularTiltDualInverse parameters lower length positive collar lengthPositive widthHalf widthLength source := by
  apply tilted_realCoercive_unique _
    (annularTiltZeroForm_isCoercive parameters lower length positive collar lengthPositive widthHalf widthLength)
  intro test
  exact (equation test).trans
    (annularTiltDualInverse_solves parameters lower length positive collar lengthPositive widthHalf widthLength source test).symm

end Inverse
end Grad.AnnularTiltedReference
