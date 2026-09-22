import AJF13GenuineIncomingLiftCovariance
import AJA17ActualFullJetOneHigh

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularHighInverseOrbit Grad.AnnularCurrentInverse Grad.AnnularCurrentEnergy
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit Grad.AnnularReconstruction Grad.CartesianState

section Restriction
variable {W V : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def formTestRestriction (inclusion : V →L[ℝ] W) :
    (W →L[ℝ] W →L[ℝ] ℝ) →L[ℝ] (W →L[ℝ] V →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ W (W →L[ℝ] ℝ) (V →L[ℝ] ℝ))
    ((ContinuousLinearMap.compL ℝ V W ℝ).flip inclusion)

theorem formTestRestriction_apply (inclusion : V →L[ℝ] W) (form : W →L[ℝ] W →L[ℝ] ℝ)
    (field : W) (test : V) : formTestRestriction inclusion form field test = form field (inclusion test) := rfl

theorem formTestRestriction_norm (inclusion : V →L[ℝ] W) (isometry : ∀ test, ‖inclusion test‖ = ‖test‖)
    (form : W →L[ℝ] W →L[ℝ] ℝ) : ‖formTestRestriction inclusion form‖ ≤ ‖form‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (formTestRestriction inclusion form) (norm_nonneg form)
  intro field
  apply ContinuousLinearMap.opNorm_le_bound (formTestRestriction inclusion form field) (mul_nonneg (norm_nonneg form) (norm_nonneg field))
  intro test
  change ‖form field (inclusion test)‖ ≤ (‖form‖ * ‖field‖) * ‖test‖
  rw [← isometry test]
  exact ((form field).le_opNorm _).trans (mul_le_mul_of_nonneg_right (form.le_opNorm field) (norm_nonneg _))

theorem formTestRestriction_hasFDerivAt {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (inclusion : V →L[ℝ] W) (function : P → W →L[ℝ] W →L[ℝ] ℝ)
    (derivative : P →L[ℝ] W →L[ℝ] W →L[ℝ] ℝ) (point : P)
    (actual : HasFDerivAt function derivative point) :
    HasFDerivAt (fun tau => formTestRestriction inclusion (function tau))
      ((formTestRestriction inclusion).comp derivative) point :=
  HasFDerivAt.comp (𝕜 := ℝ) (E := P) (F := W →L[ℝ] W →L[ℝ] ℝ) (G := W →L[ℝ] V →L[ℝ] ℝ)
    point (ContinuousLinearMap.hasFDerivAt (E := W →L[ℝ] W →L[ℝ] ℝ) (F := W →L[ℝ] V →L[ℝ] ℝ)
      (formTestRestriction inclusion)) actual

end Restriction

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
  (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)

/-- The actual full form, restricted only in its test argument. Its input
may have the genuine nonzero prescribed inner trace. -/
def liftedTestFunctionalOrbitJet (angular cell : ℕ) (tau : OrbitParameter) :=
  formTestRestriction (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
    (currentHighFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau)

theorem liftedTestFunctionalOrbitJet_hasFDerivAt (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell)
      (orbitColumns
        (liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state (angular + 1) cell tau)
        (liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular (cell + 1) tau)) tau := by
  let restriction := formTestRestriction
    (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
  have derivative := formTestRestriction_hasFDerivAt
    (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
    (currentHighFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell)
    _ tau (currentHighFormOrbitJet_hasFDerivAt parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau)
  apply derivative.congr_fderiv
  exact orbitColumns_comp
    (E := annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ)
    (F := annularEnergySpace lower L positive →L[ℝ]
      annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    restriction _ _

theorem liftedTestFunctionalOrbitJet_contDiff (angular cell : ℕ) :
    ContDiff ℝ ∞ (liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell) :=
  orbitTower_contDiff _ (liftedTestFunctionalOrbitJet_hasFDerivAt parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state) angular cell

theorem liftedTestFunctionalOrbitJet_norm (angular cell : ℕ) (tau : OrbitParameter) :
    ‖liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau‖ ≤
      ‖currentHighFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau‖ :=
  formTestRestriction_norm _ (fun _ => rfl) _

theorem liftedTestFunctionalOrbit_pullback (tau : OrbitParameter) (field : annularEnergySpace lower L positive)
    (test : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive) :
    liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau field test =
      currentHighTestFunctional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
        (energyTranslation lower L positive (-tau) field)
        (zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (-tau) test) := by
  change currentHighFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau field test.val = _
  rw [currentHighFormOrbitJet_zero]
  exact currentHighFormOrbit_pullback parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau field test.val

end Grad.AnnularHighGenerators
