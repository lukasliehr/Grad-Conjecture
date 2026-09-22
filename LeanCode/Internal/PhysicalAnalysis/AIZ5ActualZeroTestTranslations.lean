import AIZ1ActualEnergyTranslations
import AAT4TraceLiftCommutation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularCoupledOrbit
open Grad.AnnularVariational Grad.AnnularGrades Grad.AnnularKernelOrbit

variable (lower length : ℝ) (positive : 0 < lower) (collar : lower < 1) (lengthPositive : 0 < length)

/-- Actual translation on the genuine inner-zero test subspace V. Its
membership follows from the accepted physical trace commutation laws. -/
def zeroTestTranslation (tau : OrbitParameter) :
    annularInnerZero lower length positive collar lengthPositive →L[ℂ]
      annularInnerZero lower length positive collar lengthPositive :=
  annularZeroDiagonal lower length positive collar lengthPositive (fun mode => (orbitCharacter tau mode.val).re)
    1 (by norm_num) (fun mode => orbitCharacter_re_bound tau mode.val) +
  Complex.I • annularZeroDiagonal lower length positive collar lengthPositive (fun mode => (orbitCharacter tau mode.val).im)
    1 (by norm_num) (fun mode => orbitCharacter_im_bound tau mode.val)

theorem zeroTestTranslation_value (tau : OrbitParameter)
    (field : annularInnerZero lower length positive collar lengthPositive) :
    (zeroTestTranslation lower length positive collar lengthPositive tau field).val =
      energyTranslation lower length positive tau field.val := rfl

theorem zeroTestTranslation_norm (tau : OrbitParameter)
    (field : annularInnerZero lower length positive collar lengthPositive) :
    ‖zeroTestTranslation lower length positive collar lengthPositive tau field‖ = ‖field‖ := by
  change ‖(zeroTestTranslation lower length positive collar lengthPositive tau field).val‖ = ‖field.val‖
  rw [zeroTestTranslation_value]
  exact energyTranslation_norm lower length positive tau field.val

theorem zeroTestTranslation_inverse (tau : OrbitParameter)
    (field : annularInnerZero lower length positive collar lengthPositive) :
    zeroTestTranslation lower length positive collar lengthPositive tau
      (zeroTestTranslation lower length positive collar lengthPositive (-tau) field) = field := by
  apply Subtype.ext
  change energyTranslation lower length positive tau (energyTranslation lower length positive (-tau) field.val) = field.val
  exact energyTranslation_inverse lower length positive tau field.val

def zeroTestTranslationEquivalence (tau : OrbitParameter) :
    annularInnerZero lower length positive collar lengthPositive ≃ₗᵢ[ℂ]
      annularInnerZero lower length positive collar lengthPositive where
  toLinearEquiv :=
    { (zeroTestTranslation lower length positive collar lengthPositive tau).toLinearMap with
      invFun := zeroTestTranslation lower length positive collar lengthPositive (-tau)
      left_inv := by
        intro field
        change zeroTestTranslation lower length positive collar lengthPositive (-tau)
          (zeroTestTranslation lower length positive collar lengthPositive tau field) = field
        simpa only [neg_neg] using zeroTestTranslation_inverse lower length positive collar lengthPositive (-tau) field
      right_inv := zeroTestTranslation_inverse lower length positive collar lengthPositive tau }
  norm_map' := zeroTestTranslation_norm lower length positive collar lengthPositive tau

end Grad.AnnularCoupledOrbit
