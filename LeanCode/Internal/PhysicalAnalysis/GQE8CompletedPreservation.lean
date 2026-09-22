import GQE7CompletedScalars

noncomputable section
set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.GaugeCoefficients.Physical.Allocation

theorem observation_of_dense_core {C E F T : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup T] [NormedSpace ℂ T]
    (embed : C → E) (dense : DenseRange embed) (transfer : E →L[ℂ] F)
    (source : E →L[ℂ] T) (target : F →L[ℂ] T)
    (onCore : ∀ core, target (transfer (embed core)) = source (embed core))
    (field : E) : target (transfer field) = source field :=
  isClosed_property dense (isClosed_eq (target.continuous.comp transfer.continuous) source.continuous) onCore field

variable {L sigma gamma ell : ℝ} {admissible : Admissible L sigma gamma ell}
  {gauge : CoefficientFamily L sigma gamma ell 3 3}
  (smooth : SmoothCompensatedCoreIsomorphism admissible gauge) (grade : ℕ) (large : 3 ≤ grade)

theorem completedPsi_transfer (field : circularCompensatedClosure admissible grade) :
    completedPsi admissible grade (currentCompensatedCore admissible gauge smooth.coherent)
      (completedTransfer smooth grade large field) =
      completedPsi admissible grade (circularCompensatedCore admissible) field := by
  apply observation_of_dense_core (compensatedIntoClosure admissible grade (circularCompensatedCore admissible))
    (compensatedIntoClosure_denseRange admissible grade (circularCompensatedCore admissible))
    (completedTransfer smooth grade large) (completedPsi admissible grade (circularCompensatedCore admissible))
    (completedPsi admissible grade (currentCompensatedCore admissible gauge smooth.coherent)) _ field
  intro data
  exact (congrArg (completedPsi admissible grade (currentCompensatedCore admissible gauge smooth.coherent))
    (completedTransfer_core smooth grade large data)).trans
      ((completedPsi_core admissible grade (currentCompensatedCore admissible gauge smooth.coherent) (smooth.equivalence data)).trans
        ((congrArg (apSmoothGrade L sigma gamma ell 1 (grade + 1)) (transfer_physicalPsi smooth data)).trans
          (completedPsi_core admissible grade (circularCompensatedCore admissible) data).symm))

theorem completedScalar_transfer (field : circularCompensatedClosure admissible grade) :
    completedScalar admissible grade (currentCompensatedCore admissible gauge smooth.coherent)
      (completedTransfer smooth grade large field) =
      completedScalar admissible grade (circularCompensatedCore admissible) field := by
  apply observation_of_dense_core (compensatedIntoClosure admissible grade (circularCompensatedCore admissible))
    (compensatedIntoClosure_denseRange admissible grade (circularCompensatedCore admissible))
    (completedTransfer smooth grade large) (completedScalar admissible grade (circularCompensatedCore admissible))
    (completedScalar admissible grade (currentCompensatedCore admissible gauge smooth.coherent)) _ field
  intro data
  exact (congrArg (completedScalar admissible grade (currentCompensatedCore admissible gauge smooth.coherent))
    (completedTransfer_core smooth grade large data)).trans
      ((completedScalar_core admissible grade (currentCompensatedCore admissible gauge smooth.coherent) (smooth.equivalence data)).trans
        ((congrArg (apSmoothGrade L sigma gamma ell 1 (grade + 1)) (transfer_physicalScalar smooth data)).trans
          (completedScalar_core admissible grade (circularCompensatedCore admissible) data).symm))

theorem completedRadial_transfer (field : circularCompensatedClosure admissible grade) :
    completedRadial admissible grade (currentCompensatedCore admissible gauge smooth.coherent)
      (completedTransfer smooth grade large field) =
      completedRadial admissible grade (circularCompensatedCore admissible) field := by
  apply observation_of_dense_core (compensatedIntoClosure admissible grade (circularCompensatedCore admissible))
    (compensatedIntoClosure_denseRange admissible grade (circularCompensatedCore admissible))
    (completedTransfer smooth grade large) (completedRadial admissible grade (circularCompensatedCore admissible))
    (completedRadial admissible grade (currentCompensatedCore admissible gauge smooth.coherent)) _ field
  intro data
  exact (congrArg (completedRadial admissible grade (currentCompensatedCore admissible gauge smooth.coherent))
    (completedTransfer_core smooth grade large data)).trans
      ((completedRadial_core admissible grade (currentCompensatedCore admissible gauge smooth.coherent) (smooth.equivalence data)).trans
        ((congrArg (apSmoothGrade L sigma gamma ell 1 (grade + 1)) (transfer_physicalRadial smooth data)).trans
          (completedRadial_core admissible grade (circularCompensatedCore admissible) data).symm))

/-- Actual AO23 on both specified original completed graph carriers. -/
theorem completedScalarPreservation (field : circularCompensatedClosure admissible grade) :
    completedPsi admissible grade (currentCompensatedCore admissible gauge smooth.coherent)
        (completedTransfer smooth grade large field) = completedPsi admissible grade (circularCompensatedCore admissible) field ∧
    completedScalar admissible grade (currentCompensatedCore admissible gauge smooth.coherent)
        (completedTransfer smooth grade large field) = completedScalar admissible grade (circularCompensatedCore admissible) field ∧
    completedRadial admissible grade (currentCompensatedCore admissible gauge smooth.coherent)
        (completedTransfer smooth grade large field) = completedRadial admissible grade (circularCompensatedCore admissible) field :=
  ⟨completedPsi_transfer smooth grade large field, completedScalar_transfer smooth grade large field,
    completedRadial_transfer smooth grade large field⟩

end Grad.GaugeCoefficients.Physical.Compensated
