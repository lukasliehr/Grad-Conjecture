import AIZ1ActualEnergyTranslations
import ADX1ExactOmegaDiagonals

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open scoped BigOperators
namespace Grad.AnnularCoupledOrbit
open Grad.ClosedJets Grad.AnnularVariational Grad.AnnularGrades Grad.AnnularKernelOrbit Grad.AnnularOmegaGraph

variable (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)

/-- Translation preserves the original closed Domega graph through its
accepted bounded diagonals. Both derivative and value stay on the same mode. -/
def fluxTranslation (tau : OrbitParameter) :
    annularOmegaGraph lower length positive lengthPositive →L[ℂ] annularOmegaGraph lower length positive lengthPositive :=
  annularOmegaGraphDiagonal lower length positive lengthPositive (fun mode => (orbitCharacter tau mode.val).re)
    1 (by norm_num) (fun mode => orbitCharacter_re_bound tau mode.val) +
  Complex.I • annularOmegaGraphDiagonal lower length positive lengthPositive (fun mode => (orbitCharacter tau mode.val).im)
    1 (by norm_num) (fun mode => orbitCharacter_im_bound tau mode.val)

theorem fluxTranslation_apply (tau : OrbitParameter) (field : annularOmegaGraph lower length positive lengthPositive)
    (coordinate : Fin 2) (mode : HighAnnularMode) :
    (fluxTranslation lower length positive lengthPositive tau field).val coordinate mode =
      orbitCharacter tau mode.val • field.val coordinate mode := by
  let first := annularOmegaGraphDiagonal lower length positive lengthPositive (fun mode => (orbitCharacter tau mode.val).re)
    1 (by norm_num) (fun mode => orbitCharacter_re_bound tau mode.val)
  let second := annularOmegaGraphDiagonal lower length positive lengthPositive (fun mode => (orbitCharacter tau mode.val).im)
    1 (by norm_num) (fun mode => orbitCharacter_im_bound tau mode.val)
  have firstRow : (first field).val coordinate =
      realLpDiagonal (Index := HighAnnularMode) (E := Grad.SourceCollarDivision.RadialL2 1 lower) (fun mode => (orbitCharacter tau mode.val).re) 1 (by norm_num)
        (fun mode => orbitCharacter_re_bound tau mode.val) (field.val coordinate) := by
    fin_cases coordinate
    · exact annularOmegaGraphDiagonal_value lower length positive lengthPositive _ _ _ _ field
    · exact annularOmegaGraphDiagonal_slope lower length positive lengthPositive _ _ _ _ field
  have secondRow : (second field).val coordinate =
      realLpDiagonal (Index := HighAnnularMode) (E := Grad.SourceCollarDivision.RadialL2 1 lower) (fun mode => (orbitCharacter tau mode.val).im) 1 (by norm_num)
        (fun mode => orbitCharacter_im_bound tau mode.val) (field.val coordinate) := by
    fin_cases coordinate
    · exact annularOmegaGraphDiagonal_value lower length positive lengthPositive _ _ _ _ field
    · exact annularOmegaGraphDiagonal_slope lower length positive lengthPositive _ _ _ _ field
  have firstPoint : (first field).val coordinate mode = ((orbitCharacter tau mode.val).re : ℂ) • field.val coordinate mode :=
    congrArg (fun row : AnnularBulk lower => row mode) firstRow
  have secondPoint : (second field).val coordinate mode = ((orbitCharacter tau mode.val).im : ℂ) • field.val coordinate mode :=
    congrArg (fun row : AnnularBulk lower => row mode) secondRow
  change (first field).val coordinate mode + Complex.I • (second field).val coordinate mode = _
  exact (congrArg₂ (fun a b => a + Complex.I • b) firstPoint secondPoint).trans (complexParts_smul _ _)

theorem fluxTranslation_norm (tau : OrbitParameter) (field : annularOmegaGraph lower length positive lengthPositive) :
    ‖fluxTranslation lower length positive lengthPositive tau field‖ = ‖field‖ := by
  have rowNorm (coordinate : Fin 2) :
      ‖(fluxTranslation lower length positive lengthPositive tau field).val coordinate‖ = ‖field.val coordinate‖ := by
    have point (mode : HighAnnularMode) :
        ‖(fluxTranslation lower length positive lengthPositive tau field).val coordinate mode‖ = ‖field.val coordinate mode‖ := by
      rw [fluxTranslation_apply, norm_smul, orbitCharacter_norm, one_mul]
    exact le_antisymm (lp.norm_mono (by norm_num) (fun mode => (point mode).le))
      (lp.norm_mono (by norm_num) (fun mode => (point mode).ge))
  have first := annularOmegaGraph_norm_sq lower length positive lengthPositive (fluxTranslation lower length positive lengthPositive tau field)
  have second := annularOmegaGraph_norm_sq lower length positive lengthPositive field
  rw [rowNorm 0, rowNorm 1] at first
  nlinarith [norm_nonneg field, norm_nonneg (fluxTranslation lower length positive lengthPositive tau field)]

theorem fluxTranslation_add (tau sigma : OrbitParameter) (field : annularOmegaGraph lower length positive lengthPositive) :
    fluxTranslation lower length positive lengthPositive (tau + sigma) field =
      fluxTranslation lower length positive lengthPositive tau (fluxTranslation lower length positive lengthPositive sigma field) := by
  apply Subtype.ext
  apply PiLp.ext
  intro coordinate
  apply lp.ext
  funext mode
  rw [fluxTranslation_apply, fluxTranslation_apply, fluxTranslation_apply, smul_smul, orbitCharacter_add]

theorem fluxTranslation_inverse (tau : OrbitParameter) (field : annularOmegaGraph lower length positive lengthPositive) :
    fluxTranslation lower length positive lengthPositive tau (fluxTranslation lower length positive lengthPositive (-tau) field) = field := by
  apply Subtype.ext
  apply PiLp.ext
  intro coordinate
  apply lp.ext
  funext mode
  rw [fluxTranslation_apply, fluxTranslation_apply, smul_smul, orbitCharacter_inverse, one_smul]

def fluxTranslationEquivalence (tau : OrbitParameter) :
    annularOmegaGraph lower length positive lengthPositive ≃ₗᵢ[ℂ] annularOmegaGraph lower length positive lengthPositive where
  toLinearEquiv :=
    { (fluxTranslation lower length positive lengthPositive tau).toLinearMap with
      invFun := fluxTranslation lower length positive lengthPositive (-tau)
      left_inv := by
        intro field
        change fluxTranslation lower length positive lengthPositive (-tau) (fluxTranslation lower length positive lengthPositive tau field) = field
        simpa only [neg_neg] using fluxTranslation_inverse lower length positive lengthPositive (-tau) field
      right_inv := fluxTranslation_inverse lower length positive lengthPositive tau }
  norm_map' := fluxTranslation_norm lower length positive lengthPositive tau

end Grad.AnnularCoupledOrbit
