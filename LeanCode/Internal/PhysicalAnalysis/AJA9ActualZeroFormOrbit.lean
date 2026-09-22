import AJA8ActualFullFormOrbit
import AEL5ActualHighDualInverse
import AIZ5ActualZeroTestTranslations

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularHighInverseOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit

section Restriction
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def formRestriction (inclusion : V →L[ℝ] E) : (E →L[ℝ] E →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] V →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ V E (V →L[ℝ] ℝ)).flip inclusion |>.comp
    ((ContinuousLinearMap.compL ℝ E (E →L[ℝ] ℝ) (V →L[ℝ] ℝ))
      ((ContinuousLinearMap.compL ℝ V E ℝ).flip inclusion))

theorem formRestriction_apply (inclusion : V →L[ℝ] E) (form : E →L[ℝ] E →L[ℝ] ℝ) (field test : V) :
    formRestriction inclusion form field test = form (inclusion field) (inclusion test) := rfl

theorem formRestriction_norm_le (inclusion : V →L[ℝ] E)
    (isometry : ∀ field, ‖inclusion field‖ = ‖field‖) (form : E →L[ℝ] E →L[ℝ] ℝ) :
    ‖formRestriction inclusion form‖ ≤ ‖form‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (formRestriction inclusion form) (norm_nonneg form)
  intro field
  apply ContinuousLinearMap.opNorm_le_bound (formRestriction inclusion form field) (mul_nonneg (norm_nonneg form) (norm_nonneg field))
  intro test
  change ‖form (inclusion field) (inclusion test)‖ ≤ _
  exact ((form (inclusion field)).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (form.le_opNorm _) (norm_nonneg _)).trans_eq (by rw [isometry, isometry]))
theorem formRestriction_hasFDerivAt {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (inclusion : V →L[ℝ] E) (f : P → E →L[ℝ] E →L[ℝ] ℝ)
    (df : P →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ) (point : P) (derivative : HasFDerivAt f df point) :
    HasFDerivAt (fun tau => formRestriction inclusion (f tau))
      ((formRestriction inclusion).comp df) point :=
  HasFDerivAt.comp (𝕜 := ℝ) (E := P) (F := E →L[ℝ] E →L[ℝ] ℝ) (G := V →L[ℝ] V →L[ℝ] ℝ)
    point (ContinuousLinearMap.hasFDerivAt (E := E →L[ℝ] E →L[ℝ] ℝ) (F := V →L[ℝ] V →L[ℝ] ℝ)
      (formRestriction inclusion)) derivative

end Restriction

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)

def currentHighZeroFormOrbit (tau : OrbitParameter) :=
  formRestriction (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
    (currentHighFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau)

theorem currentHighZeroFormOrbit_hasFDerivAt (tau : OrbitParameter) :
    HasFDerivAt (currentHighZeroFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
      ((formRestriction (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)).comp
        (currentHighFormOrbitDerivative parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau)) tau := by
  exact formRestriction_hasFDerivAt
    (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
    (currentHighFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (currentHighFormOrbitDerivative parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau) tau
    (currentHighFormOrbit_hasFDerivAt parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau)

theorem currentHighZeroFormOrbit_pullback (tau : OrbitParameter)
    (field test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    currentHighZeroFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau field test =
      currentHighZeroForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
        (zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (-tau) field)
        (zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (-tau) test) := by
  change currentHighFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau field.val test.val = _
  exact currentHighFormOrbit_pullback parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau field.val test.val

end Grad.AnnularHighInverseOrbit
