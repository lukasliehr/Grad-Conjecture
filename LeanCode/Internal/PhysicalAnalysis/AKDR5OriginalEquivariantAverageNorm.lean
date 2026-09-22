import AKDR4SameOriginalFieldAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup Grad.Constraints Grad.Constraints.Gauges
open Grad.NonlinearProduct Grad.NonlinearQuotientBounds Grad.GaugeCoefficients.Physical.RadialLedger

def originalCharacterCore {dimension : ℕ} (parameters : PhaseParameters) (mode : ℤ)
    (field : ACore parameters dimension) : ACore parameters dimension :=
  originalAngularKernelCore parameters (angularCharacter mode) (angularCharacter_smooth mode)
    1 zero_le_one (fun angle _ => (angularCharacter_norm mode angle).le) field

theorem originalCharacterCore_bound {dimension : ℕ} (parameters : PhaseParameters) (mode : ℤ)
    (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (originalCharacterCore parameters mode field) ≤
      orthogonalGradeConstant grade * originalGradeNorm grade field := by
  simpa only [originalCharacterCore,one_mul] using originalAngularKernelCore_bound parameters
    (angularCharacter mode) (angularCharacter_smooth mode) 1 zero_le_one
    (fun angle _ => (angularCharacter_norm mode angle).le) field grade

theorem originalCharacterCore_sameField {dimension : ℕ} (parameters : PhaseParameters) (mode : ℤ)
    (field : ACore parameters dimension) :
    originalSourceFieldLinear parameters (originalCharacterCore parameters mode field) =
      startupCharacterKernel dimension mode (originalSourceFieldLinear parameters field) :=
  originalAngularKernelCore_sameField parameters (angularCharacter mode) (angularCharacter_smooth mode)
    1 zero_le_one (fun angle _ => (angularCharacter_norm mode angle).le) field

def originalEquivariantAverageCore (parameters : PhaseParameters) (field : ACore parameters 2) :
    ACore parameters 2 :=
  valueMapCore parameters positiveHelicity (originalCharacterCore parameters 1 field) +
    valueMapCore parameters negativeHelicity (originalCharacterCore parameters (-1) field)

def originalAverageConstant (grade : ℕ) : ℝ :=
  (‖positiveHelicity‖+‖negativeHelicity‖)*orthogonalGradeConstant grade

theorem originalAverageConstant_nonnegative (grade : ℕ) : 0 ≤ originalAverageConstant grade :=
  mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (orthogonalGradeConstant_nonnegative _)

theorem originalEquivariantAverageCore_bound (parameters : PhaseParameters)
    (field : ACore parameters 2) (grade : ℕ) :
    originalGradeNorm grade (originalEquivariantAverageCore parameters field) ≤
      originalAverageConstant grade * originalGradeNorm grade field := by
  have positive := (valueMapCore_bound positiveHelicity _ grade).trans
    (mul_le_mul_of_nonneg_left (originalCharacterCore_bound parameters 1 field grade) (norm_nonneg _))
  have negative := (valueMapCore_bound negativeHelicity _ grade).trans
    (mul_le_mul_of_nonneg_left (originalCharacterCore_bound parameters (-1) field grade) (norm_nonneg _))
  exact (originalGradeNorm_add_le grade _ _).trans
    ((add_le_add positive negative).trans_eq (by unfold originalAverageConstant; ring))

theorem originalEquivariantAverageCore_sameField (parameters : PhaseParameters)
    (field : ACore parameters 2) :
    originalSourceFieldLinear parameters (originalEquivariantAverageCore parameters field) =
      originalAverageKernel (originalSourceFieldLinear parameters field) := by
  rw [originalEquivariantAverageCore,map_add,originalSourceFieldLinear_valueMap,
    originalSourceFieldLinear_valueMap,originalCharacterCore_sameField,originalCharacterCore_sameField]
  rfl

end Grad.OriginalCoreRealization
