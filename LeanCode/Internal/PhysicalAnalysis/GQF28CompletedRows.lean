import GQF27AugmentedIdentity

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

theorem compensatedRows_extension {T : Type*} [NormedAddCommGroup T] [NormedSpace ℂ T] [CompleteSpace T]
    (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (mapping : CompensatedData L sigma gamma ell →ₗ[ℂ] T) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ∀ state, ‖mapping state‖ ≤ constant * compensatedNorm admissible grade state) :
    ∃ completed : compensatedClosure admissible grade core →L[ℂ] T,
      (∀ state : core, completed (compensatedIntoClosure admissible grade core state) = mapping state.val) ∧
      ‖completed‖ ≤ constant :=
  dense_extension_opNorm (C := core) (F := compensatedClosure admissible grade core) (T := T)
    (compensatedIntoClosure admissible grade core) (compensatedIntoClosure_injective admissible grade core)
    (compensatedIntoClosure_denseRange admissible grade core) (mapping.comp core.subtype) constant nonnegative
    (fun state => bound state.val)

theorem completedCircularRows_exists (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    ∃ mapping : compensatedClosure admissible grade core →L[ℂ] CapAugmentedAmbient L sigma gamma ell grade,
      (∀ state : core, mapping (compensatedIntoClosure admissible grade core state) =
        circularAugmentedCore admissible grade state.val) ∧
      ‖mapping‖ ≤ circularForwardConstant L sigma gamma grade :=
  compensatedRows_extension admissible grade core (circularAugmentedCore admissible grade)
    (circularForwardConstant L sigma gamma grade) (circularForwardConstant_nonnegative admissible grade)
    (fun state => circularAugmentedCore_bound admissible state grade)

def completedCircularRows (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] CapAugmentedAmbient L sigma gamma ell grade :=
  (completedCircularRows_exists admissible grade core).choose

theorem completedCircularRows_core (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (state : core) :
    completedCircularRows admissible grade core (compensatedIntoClosure admissible grade core state) =
      circularAugmentedCore admissible grade state.val :=
  (completedCircularRows_exists admissible grade core).choose_spec.1 state

theorem completedCircularRows_bound (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    ‖completedCircularRows admissible grade core‖ ≤ circularForwardConstant L sigma gamma grade :=
  (completedCircularRows_exists admissible grade core).choose_spec.2

def completedCurrentRows (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] CapAugmentedAmbient L sigma gamma ell grade :=
  completedCircularRows admissible grade core +
    (completedError admissible data coherent grade).comp (completedReconstruct admissible grade core)

theorem completedCurrentRows_core (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (state : core) :
    completedCurrentRows admissible data coherent grade core (compensatedIntoClosure admissible grade core state) =
      actualAugmentedCore admissible data coherent grade state.val := by
  have first := completedCircularRows_core admissible grade core state
  have second := (congrArg (completedError admissible data coherent grade)
    (completedReconstruct_core admissible grade core state)).trans
      (completedError_core admissible data coherent grade (compensatedReconstruct admissible state.val))
  exact (congrArg₂ (fun first second : CapAugmentedAmbient L sigma gamma ell grade => first + second)
    first second).trans ((add_comm _ _).trans (eq_add_of_sub_eq
      (actualAugmentedCore_difference admissible data coherent grade state.val)).symm)

theorem completedCircularRows_transfer
    {gauge : Grad.GaugeCoefficients.Physical.Allocation.CoefficientFamily L sigma gamma ell 3 3}
    (smooth : SmoothCompensatedCoreIsomorphism admissible gauge) (grade : ℕ) (large : 3 ≤ grade)
    (field : circularCompensatedClosure admissible grade) :
    completedCircularRows admissible grade (currentCompensatedCore admissible gauge smooth.coherent)
      (completedTransfer smooth grade large field) =
        completedCircularRows admissible grade (circularCompensatedCore admissible) field := by
  apply isClosed_property (compensatedIntoClosure_denseRange admissible grade (circularCompensatedCore admissible))
    (isClosed_eq
      ((completedCircularRows admissible grade (currentCompensatedCore admissible gauge smooth.coherent)).continuous.comp
        (completedTransfer smooth grade large).continuous)
      (completedCircularRows admissible grade (circularCompensatedCore admissible)).continuous) _ field
  intro state
  exact (congrArg (completedCircularRows admissible grade (currentCompensatedCore admissible gauge smooth.coherent))
    (completedTransfer_core smooth grade large state)).trans
      ((completedCircularRows_core admissible grade _ (smooth.equivalence state)).trans
        ((circularAugmentedCore_transfer admissible smooth grade large state).trans
          (completedCircularRows_core admissible grade _ state).symm))

theorem completedRows_difference (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data)
    (smooth : SmoothCompensatedCoreIsomorphism admissible data.gaugeDeviation) (grade : ℕ) (large : 3 ≤ grade)
    (field : circularCompensatedClosure admissible grade) :
    completedCurrentRows admissible data coherent grade
      (currentCompensatedCore admissible data.gaugeDeviation smooth.coherent)
      (completedTransfer smooth grade large field) -
      completedCircularRows admissible grade (circularCompensatedCore admissible) field =
      completedError admissible data coherent grade
        (Grad.GaugeCoefficients.Physical.GaugeTransfer.apCurrentProjection admissible data.gaugeDeviation (grade + 1)
          (completedReconstruct admissible grade (circularCompensatedCore admissible) field)) := by
  have first := completedCircularRows_transfer admissible smooth grade large field
  have second := congrArg (completedError admissible data coherent grade)
    (completedReconstruct_transfer admissible smooth grade large field)
  exact (congrArg₂ (fun first second : CapAugmentedAmbient L sigma gamma ell grade =>
    first + second - completedCircularRows admissible grade (circularCompensatedCore admissible) field)
    first second).trans (add_sub_cancel_left _ _)

end Grad.GaugeCoefficients.Physical.Compensated
