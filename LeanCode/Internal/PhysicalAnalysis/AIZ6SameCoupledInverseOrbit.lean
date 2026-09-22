import AIZ4CompleteCoupledUnitary
import AIZ5ActualZeroTestTranslations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularCoupledOrbit
open Grad.ClosedJets Grad.CartesianState Grad.AnnularReconstruction
open Grad.AnnularCoupledInverse Grad.AnnularKernelOrbit Grad.GaugeCoefficients.Physical.Allocation

private theorem unitaryResidualIdentity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (translation : E ≃ₗᵢ[ℂ] E) (operator : E →L[ℂ] E) (field : E) :
    translation (translation.symm field - operator (translation.symm field)) =
      field - translation (operator (translation.symm field)) := by
  rw [map_sub, translation.apply_symm_apply]

private theorem unitaryConjugateBound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (translation : E ≃ₗᵢ[ℂ] E) (operator : E →L[ℂ] E) (constant : ℝ)
    (bound : ‖operator‖ ≤ constant) :
    ‖translation.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (operator.comp translation.symm.toContinuousLinearEquiv.toContinuousLinearMap)‖ ≤ constant := by
  apply ContinuousLinearMap.opNorm_le_bound _ ((norm_nonneg operator).trans bound)
  intro field
  change ‖translation (operator (translation.symm field))‖ ≤ constant * ‖field‖
  rw [translation.norm_map]
  exact (operator.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right bound (norm_nonneg _)).trans_eq
      (congrArg (fun value : ℝ => constant * value) (translation.symm.norm_map field)))

variable (parameters : PhaseParameters) (lower length compact : ℝ)
  (lengthPositive : 0 < length) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
  (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
  (state : RetainedInverseState parameters length compact)
  (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)

/-- Conjugation of the SAME actual complete off-diagonal operator. -/
def coupledOrbitError (tau : OrbitParameter) :
    CoupledSpace lower length positive lengthPositive →L[ℂ] CoupledSpace lower length positive lengthPositive :=
  (coupledTranslationEquivalence lower length positive lengthPositive tau).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((coupledError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small).comp
      (coupledTranslationEquivalence lower length positive lengthPositive tau).symm.toContinuousLinearEquiv.toContinuousLinearMap)

/-- The accepted actual residual equivalence transported by the original
norm-isometric translations. No new inverse or stronger smallness is assumed. -/
def coupledOrbitResidualEquivalence (tau : OrbitParameter) :
    CoupledSpace lower length positive lengthPositive ≃L[ℂ] CoupledSpace lower length positive lengthPositive :=
  (coupledTranslationEquivalence lower length positive lengthPositive tau).symm.toContinuousLinearEquiv.trans
    ((actualCoupledResidualEquiv parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small).trans
      (coupledTranslationEquivalence lower length positive lengthPositive tau).toContinuousLinearEquiv)

/-- The actual same inverse at every translation. -/
def coupledOrbitInverse (tau : OrbitParameter) :
    CoupledSpace lower length positive lengthPositive →L[ℂ] CoupledSpace lower length positive lengthPositive :=
  (coupledOrbitResidualEquivalence parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small tau).symm.toContinuousLinearMap

theorem coupledOrbitInverse_apply (tau : OrbitParameter) (field : CoupledSpace lower length positive lengthPositive) :
    coupledOrbitInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small tau field =
      coupledTranslationEquivalence lower length positive lengthPositive tau
        (actualCoupledInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small
          ((coupledTranslationEquivalence lower length positive lengthPositive tau).symm field)) := rfl

theorem coupledOrbitResidual_apply (tau : OrbitParameter) (field : CoupledSpace lower length positive lengthPositive) :
    coupledOrbitResidualEquivalence parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small tau field =
      field - coupledOrbitError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small tau field := by
  let translation := coupledTranslationEquivalence lower length positive lengthPositive tau
  change translation (translation.symm field -
    coupledError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small (translation.symm field)) = _
  exact unitaryResidualIdentity translation
    (coupledError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small) field

theorem coupledOrbitInverse_left (tau : OrbitParameter) (field : CoupledSpace lower length positive lengthPositive) :
    coupledOrbitInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small tau
      (field - coupledOrbitError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small tau field) = field := by
  rw [← coupledOrbitResidual_apply]
  exact (coupledOrbitResidualEquivalence parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small tau).symm_apply_apply field

theorem coupledOrbitInverse_right (tau : OrbitParameter) (field : CoupledSpace lower length positive lengthPositive) :
    let response := coupledOrbitInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small tau field
    response - coupledOrbitError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small tau response = field := by
  dsimp only
  rw [← coupledOrbitResidual_apply]
  exact (coupledOrbitResidualEquivalence parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small tau).apply_symm_apply field

theorem coupledOrbitInverse_apply_bound (tau : OrbitParameter) (field : CoupledSpace lower length positive lengthPositive) :
    ‖coupledOrbitInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small tau field‖ ≤ 2 * ‖field‖ := by
  rw [coupledOrbitInverse_apply, LinearIsometryEquiv.norm_map]
  exact (actualCoupledInverse_apply_bound parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small _).trans_eq
    (congrArg (fun value : ℝ => 2 * value) ((coupledTranslationEquivalence lower length positive lengthPositive tau).symm.norm_map field))

theorem coupledOrbitInverse_bound (tau : OrbitParameter) :
    ‖coupledOrbitInverse parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small tau‖ ≤ 2 :=
  ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
    (coupledOrbitInverse_apply_bound parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small tau)

theorem coupledOrbitError_half (tau : OrbitParameter) :
    let operator : CoupledSpace lower length positive lengthPositive →L[ℂ] CoupledSpace lower length positive lengthPositive :=
      coupledOrbitError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small tau
    ‖operator‖ ≤ 1 / 2 := by
  exact unitaryConjugateBound
    (coupledTranslationEquivalence lower length positive lengthPositive tau)
    (coupledError parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small) (1 / 2)
    (coupledError_half parameters lower length compact lengthPositive positive lowerHalf widthHalf widthLength state small)

end Grad.AnnularCoupledOrbit
