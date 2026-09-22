import AIX3ExactFourierUnitary
import AIT99OriginalCoupledInverseConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularCoupledOrbit
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularGrades Grad.AnnularKernelOrbit

section Scalars
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem complexParts_smul (scalar : ℂ) (value : E) :
    (scalar.re : ℂ) • value + Complex.I • ((scalar.im : ℂ) • value) = scalar • value := by
  rw [smul_smul, ← add_smul]
  congr 1
  apply Complex.ext <;> simp

theorem orbitCharacter_re_bound (tau : OrbitParameter) (mode : ℤ × ℤ) :
    |(orbitCharacter tau mode).re| ≤ 1 :=
  (Complex.abs_re_le_norm _).trans_eq (orbitCharacter_norm tau mode)

theorem orbitCharacter_im_bound (tau : OrbitParameter) (mode : ℤ × ℤ) :
    |(orbitCharacter tau mode).im| ≤ 1 :=
  (Complex.abs_im_le_norm _).trans_eq (orbitCharacter_norm tau mode)

end Scalars

variable (lower length : ℝ) (positive : 0 < lower)

/-- Genuine complex angular/cell translation on the same completed energy
space, using its accepted real Fourier diagonals and complex linear structure. -/
def energyTranslation (tau : OrbitParameter) :
    annularEnergySpace lower length positive →L[ℂ] annularEnergySpace lower length positive :=
  annularEnergyDiagonal lower length positive (fun mode => (orbitCharacter tau mode.val).re)
    1 (by norm_num) (fun mode => orbitCharacter_re_bound tau mode.val) +
  Complex.I • annularEnergyDiagonal lower length positive (fun mode => (orbitCharacter tau mode.val).im)
    1 (by norm_num) (fun mode => orbitCharacter_im_bound tau mode.val)

theorem energyTranslation_apply (tau : OrbitParameter) (field : annularEnergySpace lower length positive)
    (mode : HighAnnularMode) :
    (energyTranslation lower length positive tau field).val mode = orbitCharacter tau mode.val • field.val mode := by
  change (annularEnergyDiagonal lower length positive (fun mode => (orbitCharacter tau mode.val).re)
      1 (by norm_num) (fun mode => orbitCharacter_re_bound tau mode.val) field).val mode +
    Complex.I • (annularEnergyDiagonal lower length positive (fun mode => (orbitCharacter tau mode.val).im)
      1 (by norm_num) (fun mode => orbitCharacter_im_bound tau mode.val) field).val mode = _
  rw [annularEnergyDiagonal_apply, annularEnergyDiagonal_apply]
  exact complexParts_smul _ _

theorem energyTranslation_norm (tau : OrbitParameter) (field : annularEnergySpace lower length positive) :
    ‖energyTranslation lower length positive tau field‖ = ‖field‖ := by
  change ‖(energyTranslation lower length positive tau field).val‖ = ‖field.val‖
  have point (mode : HighAnnularMode) :
      ‖(energyTranslation lower length positive tau field).val mode‖ = ‖field.val mode‖ := by
    rw [energyTranslation_apply, norm_smul, orbitCharacter_norm, one_mul]
  exact le_antisymm (lp.norm_mono (by norm_num) (fun mode => (point mode).le))
    (lp.norm_mono (by norm_num) (fun mode => (point mode).ge))

theorem energyTranslation_add (tau sigma : OrbitParameter) (field : annularEnergySpace lower length positive) :
    energyTranslation lower length positive (tau + sigma) field =
      energyTranslation lower length positive tau (energyTranslation lower length positive sigma field) := by
  apply Subtype.ext
  apply lp.ext
  funext mode
  rw [energyTranslation_apply, energyTranslation_apply, energyTranslation_apply, smul_smul, orbitCharacter_add]

theorem energyTranslation_inverse (tau : OrbitParameter) (field : annularEnergySpace lower length positive) :
    energyTranslation lower length positive tau (energyTranslation lower length positive (-tau) field) = field := by
  apply Subtype.ext
  apply lp.ext
  funext mode
  rw [energyTranslation_apply, energyTranslation_apply, smul_smul, orbitCharacter_inverse, one_smul]

def energyTranslationEquivalence (tau : OrbitParameter) :
    annularEnergySpace lower length positive ≃ₗᵢ[ℂ] annularEnergySpace lower length positive where
  toLinearEquiv :=
    { (energyTranslation lower length positive tau).toLinearMap with
      invFun := energyTranslation lower length positive (-tau)
      left_inv := by
        intro field
        change energyTranslation lower length positive (-tau) (energyTranslation lower length positive tau field) = field
        simpa only [neg_neg] using energyTranslation_inverse lower length positive (-tau) field
      right_inv := energyTranslation_inverse lower length positive tau }
  norm_map' := energyTranslation_norm lower length positive tau

end Grad.AnnularCoupledOrbit
