import GQD3BoundedExtensions

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Allocation

variable {L sigma gamma ell : ℝ} {admissible : Admissible L sigma gamma ell}
  {gauge : CoefficientFamily L sigma gamma ell 3 3}

theorem inverse_of_dense_core {C E F : Type*} [TopologicalSpace E] [TopologicalSpace F] [T2Space E]
    (embed : C → E) (dense : DenseRange embed) (forward : E → F) (backward : F → E)
    (forwardContinuous : Continuous forward) (backwardContinuous : Continuous backward)
    (coreLaw : ∀ core, backward (forward (embed core)) = embed core) (field : E) :
    backward (forward field) = field :=
  congrFun (dense.equalizer (backwardContinuous.comp forwardContinuous) continuous_id (funext coreLaw)) field

theorem completedTransfer_left_inverse
    (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (large : 3 ≤ grade) (field : circularCompensatedClosure admissible grade) :
    completedInverse isomorphism grade (completedTransfer isomorphism grade large field) = field := by
  apply inverse_of_dense_core (compensatedIntoClosure admissible grade (circularCompensatedCore admissible))
    (compensatedIntoClosure_denseRange admissible grade (circularCompensatedCore admissible))
    (completedTransfer isomorphism grade large) (completedInverse isomorphism grade)
    (completedTransfer isomorphism grade large).continuous (completedInverse isomorphism grade).continuous
  intro core
  exact (congrArg (completedInverse isomorphism grade) (completedTransfer_core isomorphism grade large core)).trans
    ((completedInverse_core isomorphism grade (isomorphism.equivalence core)).trans
      (congrArg (compensatedIntoClosure admissible grade (circularCompensatedCore admissible))
        (isomorphism.equivalence.symm_apply_apply core)))

theorem completedTransfer_right_inverse
    (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (large : 3 ≤ grade)
    (field : currentCompensatedClosure admissible gauge isomorphism.coherent grade) :
    completedTransfer isomorphism grade large (completedInverse isomorphism grade field) = field := by
  apply inverse_of_dense_core
    (compensatedIntoClosure admissible grade (currentCompensatedCore admissible gauge isomorphism.coherent))
    (compensatedIntoClosure_denseRange admissible grade (currentCompensatedCore admissible gauge isomorphism.coherent))
    (completedInverse isomorphism grade) (completedTransfer isomorphism grade large)
    (completedInverse isomorphism grade).continuous (completedTransfer isomorphism grade large).continuous
  intro core
  exact (congrArg (completedTransfer isomorphism grade large) (completedInverse_core isomorphism grade core)).trans
    ((completedTransfer_core isomorphism grade large (isomorphism.equivalence.symm core)).trans
      (congrArg (compensatedIntoClosure admissible grade (currentCompensatedCore admissible gauge isomorphism.coherent))
        (isomorphism.equivalence.apply_symm_apply core)))

/-- The actual same-grade isomorphism of the two specified AN8 closures. -/
def completedCompensatedEquivalence
    (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (large : 3 ≤ grade) :
    circularCompensatedClosure admissible grade ≃L[ℂ]
      currentCompensatedClosure admissible gauge isomorphism.coherent grade where
  toLinearEquiv :=
    { toLinearMap := (completedTransfer isomorphism grade large).toLinearMap
      invFun := completedInverse isomorphism grade
      left_inv := completedTransfer_left_inverse isomorphism grade large
      right_inv := completedTransfer_right_inverse isomorphism grade large }
  continuous_toFun := (completedTransfer isomorphism grade large).continuous
  continuous_invFun := (completedInverse isomorphism grade).continuous

theorem completedCompensatedEquivalence_core
    (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (large : 3 ≤ grade) (core : circularCompensatedCore admissible) :
    completedCompensatedEquivalence isomorphism grade large (compensatedIntoClosure admissible grade _ core) =
      compensatedIntoClosure admissible grade _ (isomorphism.equivalence core) :=
  completedTransfer_core isomorphism grade large core

theorem completedCompensatedEquivalence_symm_core
    (isomorphism : SmoothCompensatedCoreIsomorphism admissible gauge)
    (grade : ℕ) (large : 3 ≤ grade) (core : currentCompensatedCore admissible gauge isomorphism.coherent) :
    (completedCompensatedEquivalence isomorphism grade large).symm (compensatedIntoClosure admissible grade _ core) =
      compensatedIntoClosure admissible grade _ (isomorphism.equivalence.symm core) :=
  completedInverse_core isomorphism grade core

end Grad.GaugeCoefficients.Physical.Compensated
