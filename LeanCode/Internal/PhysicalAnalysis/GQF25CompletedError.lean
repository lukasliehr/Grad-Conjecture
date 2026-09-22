import GQF24ErrorBounds

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated
attribute [local instance] apNormedSpace
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

variable {L sigma gamma ell : ℝ}

theorem dense_extension_opNorm {C F T : Type*} [AddCommGroup C] [Module ℂ C]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup T] [NormedSpace ℂ T] [CompleteSpace T]
    (embed : C →ₗ[ℂ] F) (injective : Function.Injective embed) (dense : DenseRange embed)
    (mapping : C →ₗ[ℂ] T) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ∀ core, ‖mapping core‖ ≤ constant * ‖embed core‖) :
    ∃ completed : F →L[ℂ] T, (∀ core, completed (embed core) = mapping core) ∧ ‖completed‖ ≤ constant := by
  obtain ⟨completed, core, bounded⟩ := apDense_extension embed injective dense mapping constant nonnegative bound
  exact ⟨completed, core, completed.opNorm_le_bound nonnegative bounded⟩

theorem completedError_exists (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) (grade : ℕ) :
    ∃ mapping : apGrade L sigma gamma ell 3 (grade + 1) →L[ℂ] CapAugmentedAmbient L sigma gamma ell grade,
      (∀ field, mapping (apSmoothGrade L sigma gamma ell 3 (grade + 1) field) =
        errorAugmentedCore admissible data coherent grade field) ∧
      ‖mapping‖ ≤ errorForwardConstant L sigma gamma grade * errorCoefficientSize data (grade + 1) := by
  exact dense_extension_opNorm
    (C := APSmooth L sigma gamma ell 3)
    (F := apGrade L sigma gamma ell 3 (grade + 1))
    (T := CapAugmentedAmbient L sigma gamma ell grade)
    (apSmoothGrade L sigma gamma ell 3 (grade + 1)) (apSmoothGrade_injective admissible 3 (grade + 1))
    (apSmoothGrade_denseRange L sigma gamma ell 3 (grade + 1))
    (errorAugmentedCore admissible data coherent grade)
    (errorForwardConstant L sigma gamma grade * errorCoefficientSize data (grade + 1))
    (mul_nonneg (errorForwardConstant_nonnegative admissible grade) (errorCoefficientSize_nonnegative data (grade + 1)))
    (fun field => errorAugmentedCore_bound admissible data coherent field grade)

def completedError (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) (grade : ℕ) :
    apGrade L sigma gamma ell 3 (grade + 1) →L[ℂ] CapAugmentedAmbient L sigma gamma ell grade :=
  (completedError_exists admissible data coherent grade).choose

theorem completedError_core (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) (grade : ℕ)
    (field : APSmooth L sigma gamma ell 3) :
    completedError admissible data coherent grade (apSmoothGrade L sigma gamma ell 3 (grade + 1) field) =
      errorAugmentedCore admissible data coherent grade field :=
  (completedError_exists admissible data coherent grade).choose_spec.1 field

theorem completedError_bound (admissible : Admissible L sigma gamma ell)
    (data : LedgerData L sigma gamma ell) (coherent : LedgerCoherent data) (grade : ℕ) :
    ‖completedError admissible data coherent grade‖ ≤
      errorForwardConstant L sigma gamma grade * errorCoefficientSize data (grade + 1) :=
  (completedError_exists admissible data coherent grade).choose_spec.2

end Grad.GaugeCoefficients.Physical.Compensated
