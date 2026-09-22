import GQE6CompletedReconstruction

noncomputable section
set_option maxHeartbeats 1200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace graphNormedSpace coreGroup coreModule
attribute [local instance] closureGroup closureSeminormed closureNormedSpace

open Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

def fixedRowBoundConstant (L sigma gamma : ℝ) (grade : ℕ) (coefficient : SmoothOperatorJet 3 1) : ℝ :=
  apMultiplierConstant L sigma gamma grade * fixedJetConstant coefficient grade

theorem fixedRowBoundConstant_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) (coefficient : SmoothOperatorJet 3 1) :
    0 ≤ fixedRowBoundConstant L sigma gamma grade coefficient :=
  mul_nonneg (apMultiplierConstant_nonnegative admissible grade) (fixedJetConstant_nonnegative coefficient grade)

theorem apFixedRow_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (coefficient : SmoothOperatorJet 3 1) (field : apGrade L sigma gamma ell 3 grade) :
    ‖apMultiplier admissible (fixedJetFamily L sigma gamma ell coefficient grade) field‖ ≤
      fixedRowBoundConstant L sigma gamma grade coefficient * ‖field‖ :=
  (apMultiplier_bound admissible _ field).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (fixedJetFamily_norm_le L sigma gamma ell coefficient grade)
        (apMultiplierConstant_nonnegative admissible grade)) (norm_nonneg field))

def psiBoundConstant (L sigma gamma : ℝ) (grade : ℕ) : ℝ :=
  fixedRowBoundConstant L sigma gamma (grade + 1) tangentRowJet * covariantBoundConstant L gamma (grade + 1)

theorem psiBoundConstant_nonnegative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (grade : ℕ) : 0 ≤ psiBoundConstant L sigma gamma grade :=
  mul_nonneg (fixedRowBoundConstant_nonnegative admissible (grade + 1) tangentRowJet)
    (covariantBoundConstant_nonnegative admissible (grade + 1))

theorem physicalPsi_bound {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (data : CompensatedData L sigma gamma ell) :
    ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) (physicalPsi admissible data)‖ ≤
      psiBoundConstant L sigma gamma grade * compensatedNorm admissible grade data := by
  have identity := congrArg (apSmoothGrade L sigma gamma ell 1 (grade + 1))
    (apSmoothTangent_covariant admissible data.1)
  change ‖apSmoothGrade L sigma gamma ell 1 (grade + 1) (apSmoothRotation admissible 1 data.1)‖ ≤ _
  rw [← identity]
  have inner := (apSmoothCovariant_bound admissible data.1 (grade + 1)).trans
    (mul_le_mul_of_nonneg_left (compensatedGraphEntry_bound admissible grade data 0)
      (covariantBoundConstant_nonnegative admissible (grade + 1)))
  exact (apFixedRow_bound admissible (grade + 1) tangentRowJet
    ((apSmoothCovariant admissible data.1).val (grade + 1))).trans
      ((mul_le_mul_of_nonneg_left inner
        (fixedRowBoundConstant_nonnegative admissible (grade + 1) tangentRowJet)).trans_eq
          (mul_assoc _ _ _).symm)

variable {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)

theorem completedPsi_exists (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    ∃ mapping : compensatedClosure admissible grade core →L[ℂ] apGrade L sigma gamma ell 1 (grade + 1),
      (∀ data : core, mapping (compensatedIntoClosure admissible grade core data) =
        apSmoothGrade L sigma gamma ell 1 (grade + 1) (physicalPsi admissible data.val)) ∧
      ‖mapping‖ ≤ psiBoundConstant L sigma gamma grade :=
  coreGraph_extension (compensatedCoreGraph admissible grade core)
    (((apSmoothGrade L sigma gamma ell 1 (grade + 1)).comp (physicalPsi admissible)).comp core.subtype)
    (psiBoundConstant L sigma gamma grade) (psiBoundConstant_nonnegative admissible grade)
    (fun data => physicalPsi_bound admissible grade data.val)

def completedPsi (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] apGrade L sigma gamma ell 1 (grade + 1) :=
  (completedPsi_exists admissible grade core).choose

theorem completedPsi_core (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (data : core) :
    completedPsi admissible grade core (compensatedIntoClosure admissible grade core data) =
      apSmoothGrade L sigma gamma ell 1 (grade + 1) (physicalPsi admissible data.val) :=
  (completedPsi_exists admissible grade core).choose_spec.1 data

theorem completedPsi_bound (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    ‖completedPsi admissible grade core‖ ≤ psiBoundConstant L sigma gamma grade :=
  (completedPsi_exists admissible grade core).choose_spec.2

def completedScalar (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] apGrade L sigma gamma ell 1 (grade + 1) :=
  completedPsi admissible grade core + ((apMeanFree L sigma gamma ell 1 (grade + 1)).comp
    (apTangentContraction admissible (grade + 1))).comp (completedReconstruct admissible grade core)

def completedRadial (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) :
    compensatedClosure admissible grade core →L[ℂ] apGrade L sigma gamma ell 1 (grade + 1) :=
  (apRadialContraction admissible (grade + 1)).comp (completedReconstruct admissible grade core)

theorem completedScalar_core (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (data : core) :
    completedScalar admissible grade core (compensatedIntoClosure admissible grade core data) =
      apSmoothGrade L sigma gamma ell 1 (grade + 1) (physicalScalar admissible data.val) := by
  have identity := congrArg₂ (fun psi : apGrade L sigma gamma ell 1 (grade + 1) =>
    fun field : apGrade L sigma gamma ell 3 (grade + 1) =>
      psi + apMeanFree L sigma gamma ell 1 (grade + 1) (apTangentContraction admissible (grade + 1) field))
    (completedPsi_core admissible grade core data) (completedReconstruct_core admissible grade core data)
  exact identity

theorem completedRadial_core (grade : ℕ) (core : Submodule ℂ (CompensatedData L sigma gamma ell)) (data : core) :
    completedRadial admissible grade core (compensatedIntoClosure admissible grade core data) =
      apSmoothGrade L sigma gamma ell 1 (grade + 1) (physicalRadial admissible data.val) :=
  congrArg (apRadialContraction admissible (grade + 1)) (completedReconstruct_core admissible grade core data)

end Grad.GaugeCoefficients.Physical.Compensated
