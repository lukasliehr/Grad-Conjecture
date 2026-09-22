import GQE5ScalarPreservation

noncomputable section
set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace

open Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

theorem completedReconstruct_exists (grade : ℕ)
    (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    ∃ mapping : compensatedClosure admissible grade core →L[ℂ] apGrade L sigma gamma ell 3 (grade + 1),
      (∀ data : core, mapping (compensatedIntoClosure admissible grade core data) =
        apSmoothGrade L sigma gamma ell 3 (grade + 1) (compensatedReconstruct admissible data.val)) ∧
      ‖mapping‖ ≤ reconstructionBoundConstant L gamma grade :=
  coreGraph_extension (compensatedCoreGraph admissible grade core)
    (((apSmoothGrade L sigma gamma ell 3 (grade + 1)).comp (compensatedReconstruct admissible)).comp core.subtype)
    (reconstructionBoundConstant L gamma grade) (reconstructionBoundConstant_nonnegative admissible grade)
    (fun data => compensatedReconstruct_bound admissible grade data.val)

/-- Faithful reconstruction of the actual five-slot graph closure. No
independent vector coordinate or maximal PDE domain is introduced. -/
def completedReconstruct (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] apGrade L sigma gamma ell 3 (grade + 1) :=
  (completedReconstruct_exists admissible grade core).choose

theorem completedReconstruct_core (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell))
    (data : core) :
    completedReconstruct admissible grade core (compensatedIntoClosure admissible grade core data) =
      apSmoothGrade L sigma gamma ell 3 (grade + 1) (compensatedReconstruct admissible data.val) :=
  (completedReconstruct_exists admissible grade core).choose_spec.1 data

theorem completedReconstruct_bound (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    ‖completedReconstruct admissible grade core‖ ≤ reconstructionBoundConstant L gamma grade :=
  (completedReconstruct_exists admissible grade core).choose_spec.2

theorem completedReconstruct_transfer {gauge : CoefficientFamily L sigma gamma ell 3 3}
    (smooth : SmoothCompensatedCoreIsomorphism admissible gauge) (grade : ℕ) (large : 3 ≤ grade)
    (field : circularCompensatedClosure admissible grade) :
    completedReconstruct admissible grade (currentCompensatedCore admissible gauge smooth.coherent)
      (completedTransfer smooth grade large field) =
      Grad.GaugeCoefficients.Physical.GaugeTransfer.apCurrentProjection admissible gauge (grade + 1)
        (completedReconstruct admissible grade (circularCompensatedCore admissible) field) := by
  apply isClosed_property (compensatedIntoClosure_denseRange admissible grade (circularCompensatedCore admissible))
    (isClosed_eq
      ((completedReconstruct admissible grade (currentCompensatedCore admissible gauge smooth.coherent)).continuous.comp
        (completedTransfer smooth grade large).continuous)
      ((Grad.GaugeCoefficients.Physical.GaugeTransfer.apCurrentProjection admissible gauge (grade + 1)).continuous.comp
        (completedReconstruct admissible grade (circularCompensatedCore admissible)).continuous)) _ field
  intro data
  simp only [Function.comp_apply]
  exact (congrArg (completedReconstruct admissible grade (currentCompensatedCore admissible gauge smooth.coherent))
    (completedTransfer_core smooth grade large data)).trans
      ((completedReconstruct_core admissible grade (currentCompensatedCore admissible gauge smooth.coherent)
        (smooth.equivalence data)).trans
          ((congrArg (apSmoothGrade L sigma gamma ell 3 (grade + 1)) (smooth.forwardReconstruction data)).trans
            (congrArg (Grad.GaugeCoefficients.Physical.GaugeTransfer.apCurrentProjection admissible gauge (grade + 1))
              (completedReconstruct_core admissible grade (circularCompensatedCore admissible) data).symm)))

end Grad.GaugeCoefficients.Physical.Compensated
