import AAT9LiteralWeightedCarrier

noncomputable section
set_option maxHeartbeats 1000000

namespace Grad.AnnularGrades

open Grad.AnnularVariational

section Lp
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def HasAnnularLpGrade (angular cell inserted : ℕ) (field : lp (fun _ : HighAnnularMode => E) 2) : Prop :=
  Memℓp (fun mode => (annularGradeWeight angular cell inserted mode : ℂ) • field mode) 2

def annularLpWeighted (angular cell inserted : ℕ) (field : lp (fun _ : HighAnnularMode => E) 2)
    (grade : HasAnnularLpGrade angular cell inserted field) : lp (fun _ : HighAnnularMode => E) 2 :=
  ⟨fun mode => (annularGradeWeight angular cell inserted mode : ℂ) • field mode, grade⟩

def annularLpDecode (angular cell inserted : ℕ) :
    lp (fun _ : HighAnnularMode => E) 2 →L[ℂ] lp (fun _ : HighAnnularMode => E) 2 :=
  realLpDiagonal (fun mode => (annularGradeWeight angular cell inserted mode)⁻¹) 1
    (by norm_num) (annularGradeWeight_inv_bound angular cell inserted)

theorem annularLpDecode_normalization (angular cell inserted : ℕ)
    (field : lp (fun _ : HighAnnularMode => E) 2) (mode : HighAnnularMode) :
    (annularGradeWeight angular cell inserted mode : ℂ) • annularLpDecode angular cell inserted field mode = field mode := by
  rw [annularLpDecode, realLpDiagonal_apply, smul_smul, ← Complex.ofReal_mul,
    mul_inv_cancel₀ (annularGradeWeight_pos angular cell inserted mode).ne', Complex.ofReal_one, one_smul]

theorem annularLpDecode_weighted (angular cell inserted : ℕ)
    (field : lp (fun _ : HighAnnularMode => E) 2) (grade : HasAnnularLpGrade angular cell inserted field) :
    annularLpDecode angular cell inserted (annularLpWeighted angular cell inserted field grade) = field := by
  apply lp.ext
  funext mode
  change (((annularGradeWeight angular cell inserted mode)⁻¹ : ℝ) : ℂ) •
    ((annularGradeWeight angular cell inserted mode : ℂ) • field mode) = field mode
  rw [smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ (annularGradeWeight_pos angular cell inserted mode).ne',
    Complex.ofReal_one, one_smul]

theorem annularLpDecode_injective (angular cell inserted : ℕ) :
    Function.Injective (annularLpDecode (E := E) angular cell inserted) :=
  realLpDiagonal_injective _ _ _ _ (fun mode => inv_ne_zero (annularGradeWeight_pos angular cell inserted mode).ne')

theorem annularLpDecode_norm_sq (angular cell inserted : ℕ) (field : lp (fun _ : HighAnnularMode => E) 2) :
    ‖field‖ ^ 2 = ∑' mode : HighAnnularMode, annularGradeWeight angular cell inserted mode ^ 2 *
      ‖annularLpDecode angular cell inserted field mode‖ ^ 2 := by
  have formula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at formula
  rw [formula]
  apply tsum_congr
  intro mode
  have normalized := congrArg (fun value : E => ‖value‖ ^ 2)
    (annularLpDecode_normalization angular cell inserted field mode)
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (annularGradeWeight_pos angular cell inserted mode), mul_pow] at normalized
  exact normalized.symm

end Lp

section Energy
variable (lower length : ℝ) (positive : 0 < lower) (angular cell inserted : ℕ)

theorem annularEnergyDecode_injective :
    Function.Injective (annularEnergyDecode lower length positive angular cell inserted) := by
  intro first second equality
  apply Subtype.ext
  exact annularLpDecode_injective angular cell inserted
    (congrArg (fun field : annularEnergySpace lower length positive => field.val) equality)

theorem annularWeightedEnergy_decode (field : annularEnergySpace lower length positive)
    (grade : HasAnnularEnergyGrade lower length positive angular cell inserted
      (annularEnergyDecode lower length positive angular cell inserted field)) :
    annularWeightedEnergy lower length positive angular cell inserted
      (annularEnergyDecode lower length positive angular cell inserted field) grade = field := by
  apply Subtype.ext
  apply lp.ext
  funext mode
  exact annularEnergyDecode_normalization lower length positive angular cell inserted field mode

/-- The complete normalized carrier norm is precisely the weighted norm
of its actual decoded energy coordinates. -/
theorem annularEnergyDecode_norm_sq (field : annularEnergySpace lower length positive) :
    ‖field‖ ^ 2 = ∑' mode : HighAnnularMode, annularGradeWeight angular cell inserted mode ^ 2 *
      ‖(annularEnergyDecode lower length positive angular cell inserted field).val mode‖ ^ 2 :=
  annularLpDecode_norm_sq angular cell inserted field.val

end Energy

end Grad.AnnularGrades
