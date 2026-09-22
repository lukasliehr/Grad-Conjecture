import AJA9ActualZeroFormOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularHighInverseOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit

section Transport
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem equivalence_forward_of_right (base : (V →L[ℝ] ℝ) ≃L[ℝ] V)
    (form : V →L[ℝ] V →L[ℝ] ℝ)
    (right : form.comp base.toContinuousLinearMap = ContinuousLinearMap.id ℝ _) :
    base.symm.toContinuousLinearMap = form := by
  ext field test
  have equation := congrArg (fun mapping : (V →L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ) => mapping (base.symm field) test) right
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.id_apply] using equation.symm

theorem equivalence_right (base : (V →L[ℝ] ℝ) ≃L[ℝ] V)
    (form : V →L[ℝ] V →L[ℝ] ℝ) (forward : base.symm.toContinuousLinearMap = form) :
    form.comp base.toContinuousLinearMap = ContinuousLinearMap.id ℝ _ := by
  rw [← forward]
  apply ContinuousLinearMap.ext
  intro source
  exact base.symm_apply_apply source

theorem equivalence_left (base : (V →L[ℝ] ℝ) ≃L[ℝ] V)
    (form : V →L[ℝ] V →L[ℝ] ℝ) (forward : base.symm.toContinuousLinearMap = form) :
    base.toContinuousLinearMap.comp form = ContinuousLinearMap.id ℝ _ := by
  rw [← forward]
  ext field
  exact base.apply_symm_apply field

def dualTranslation (translation : V ≃L[ℝ] V) : (V →L[ℝ] ℝ) ≃L[ℝ] (V →L[ℝ] ℝ) :=
  translation.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ)

def sameInverseEquivalence (translation : V ≃L[ℝ] V) (base : (V →L[ℝ] ℝ) ≃L[ℝ] V) :
    (V →L[ℝ] ℝ) ≃L[ℝ] V :=
  (dualTranslation translation).symm.trans (base.trans translation)

theorem sameInverseEquivalence_forward (translation : V ≃L[ℝ] V)
    (base : (V →L[ℝ] ℝ) ≃L[ℝ] V) (form : V →L[ℝ] V →L[ℝ] ℝ)
    (forward : base.symm.toContinuousLinearMap = form) :
    (sameInverseEquivalence translation base).symm.toContinuousLinearMap =
      formRestriction translation.symm.toContinuousLinearMap form := by
  ext field test
  change base.symm (translation.symm field) (translation.symm test) = form (translation.symm field) (translation.symm test)
  exact congrArg (fun mapping : V →L[ℝ] V →L[ℝ] ℝ => mapping (translation.symm field) (translation.symm test)) forward

theorem sameInverseEquivalence_bound (translation : V ≃L[ℝ] V)
    (isometry : ∀ field, ‖translation field‖ = ‖field‖)
    (base : (V →L[ℝ] ℝ) ≃L[ℝ] V) (constant : ℝ) (constantNonnegative : 0 ≤ constant)
    (bound : ∀ source, ‖base source‖ ≤ constant * ‖source‖) (source : V →L[ℝ] ℝ) :
    ‖sameInverseEquivalence translation base source‖ ≤ constant * ‖source‖ := by
  have dualBound : ‖(dualTranslation translation).symm source‖ ≤ ‖source‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro field
    change ‖source (translation field)‖ ≤ ‖source‖ * ‖field‖
    exact (source.le_opNorm _).trans_eq (by rw [isometry])
  change ‖translation (base ((dualTranslation translation).symm source))‖ ≤ _
  rw [isometry]
  exact (bound _).trans (mul_le_mul_of_nonneg_left dualBound constantNonnegative)
end Transport

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

def currentHighInverseOrbitEquivalence (tau : OrbitParameter) :=
  sameInverseEquivalence
    ((zeroTestTranslationEquivalence lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau).toContinuousLinearEquiv.restrictScalars ℝ)
    (currentHighDualEquiv parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)

def currentHighInverseOrbit (tau : OrbitParameter) :=
  (currentHighInverseOrbitEquivalence parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau).toContinuousLinearMap

theorem currentHighInverseOrbit_apply (tau : OrbitParameter)
    (source : annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ) :
    currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau source =
      zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau
        (currentHighDualInverse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          (source.comp ((zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau).restrictScalars ℝ))) := rfl

theorem currentHighInverseOrbit_forward (tau : OrbitParameter) :
    (currentHighInverseOrbitEquivalence parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau).symm.toContinuousLinearMap =
      currentHighZeroFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau := by
  have base := equivalence_forward_of_right
    (currentHighDualEquiv parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (currentHighZeroForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (currentHighDualInverse_right parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
  have transported := sameInverseEquivalence_forward
    ((zeroTestTranslationEquivalence lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau).toContinuousLinearEquiv.restrictScalars ℝ)
    (currentHighDualEquiv parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (currentHighZeroForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state) base
  apply transported.trans
  ext field test
  exact (currentHighZeroFormOrbit_pullback parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau field test).symm

theorem currentHighInverseOrbit_right (tau : OrbitParameter) :
    (currentHighZeroFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau).comp
      (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau) = ContinuousLinearMap.id ℝ _ :=
  equivalence_right
    (currentHighInverseOrbitEquivalence parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)
    (currentHighZeroFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau)
    (currentHighInverseOrbit_forward parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)

theorem currentHighInverseOrbit_left (tau : OrbitParameter) :
    (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau).comp
      (currentHighZeroFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau) = ContinuousLinearMap.id ℝ _ :=
  equivalence_left
    (currentHighInverseOrbitEquivalence parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)
    (currentHighZeroFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau)
    (currentHighInverseOrbit_forward parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau)

theorem currentHighInverseOrbit_norm (tau : OrbitParameter) :
    ‖currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small tau‖ ≤ 32 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro source
  exact sameInverseEquivalence_bound
    ((zeroTestTranslationEquivalence lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau).toContinuousLinearEquiv.restrictScalars ℝ)
    (zeroTestTranslation_norm lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive tau)
    (currentHighDualEquiv parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) 32 (by norm_num)
    (currentHighDualInverse_apply_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small) source

end Grad.AnnularHighInverseOrbit
