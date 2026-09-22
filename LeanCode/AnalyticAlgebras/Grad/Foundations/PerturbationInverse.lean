import Grad.Foundations.NeumannInverse

/-! Perturb a reference isomorphism between genuinely different spaces.
Only the normalized error is an endomorphism; its Neumann inverse is then
composed with the reference inverse in the indicated order. -/
noncomputable section
namespace Grad.Foundations
variable {𝕜 X Y : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]
  [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]

def normalizedError (F : X ≃L[𝕜] Y) (A : X →L[𝕜] Y) : X →L[𝕜] X :=
  F.symm.toContinuousLinearMap.comp (A - F.toContinuousLinearMap)

omit [CompleteSpace X] in
theorem normalizedError_identity (F : X ≃L[𝕜] Y) (A : X →L[𝕜] Y) :
    1 + normalizedError F A = F.symm.toContinuousLinearMap.comp A := by
  ext x
  simp [normalizedError]

omit [CompleteSpace X] in
theorem perturbation_factor (F : X ≃L[𝕜] Y) (A : X →L[𝕜] Y) :
    F.toContinuousLinearMap.comp (1 + normalizedError F A) = A := by
  rw [normalizedError_identity]
  ext x
  simp

def perturbationInverse (F : X ≃L[𝕜] Y) (A : X →L[𝕜] Y) : Y →L[𝕜] X :=
  (neumannInverse (-normalizedError F A)).comp F.symm.toContinuousLinearMap

theorem perturbationInverse_left (F : X ≃L[𝕜] Y) (A : X →L[𝕜] Y)
    (h : ‖normalizedError F A‖ < 1) :
    (perturbationInverse F A).comp A = ContinuousLinearMap.id 𝕜 X := by
  have hi := neumannInverse_left (-normalizedError F A) (by simpa using h)
  simp only [sub_neg_eq_add] at hi
  rw [perturbationInverse, ContinuousLinearMap.comp_assoc, ← normalizedError_identity]
  exact hi

theorem perturbationInverse_right (F : X ≃L[𝕜] Y) (A : X →L[𝕜] Y)
    (h : ‖normalizedError F A‖ < 1) :
    A.comp (perturbationInverse F A) = ContinuousLinearMap.id 𝕜 Y := by
  have hi := neumannInverse_right (-normalizedError F A) (by simpa using h)
  simp only [sub_neg_eq_add] at hi
  have hf := perturbation_factor F A
  conv_lhs => lhs; rw [← hf]
  rw [perturbationInverse, ContinuousLinearMap.comp_assoc,
    ← ContinuousLinearMap.comp_assoc (1 + normalizedError F A), hi]
  ext y
  exact F.apply_symm_apply y

omit [CompleteSpace X] in
theorem perturbationInverse_norm (F : X ≃L[𝕜] Y) (A : X →L[𝕜] Y)
    (h : ‖normalizedError F A‖ < 1) :
    ‖perturbationInverse F A‖ ≤
      (1 - ‖normalizedError F A‖)⁻¹ * ‖F.symm.toContinuousLinearMap‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  simpa using neumannInverse_norm (-normalizedError F A) (by simpa using h)

omit [CompleteSpace X] in
theorem perturbationInverse_norm_of_le (F : X ≃L[𝕜] Y) (A : X →L[𝕜] Y)
    {q : ℝ} (h : ‖normalizedError F A‖ ≤ q) (hq : q < 1) :
    ‖perturbationInverse F A‖ ≤ (1 - q)⁻¹ * ‖F.symm.toContinuousLinearMap‖ := by
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact neumannInverse_norm_of_le _ (by simpa using h) hq

omit [CompleteSpace X] in
theorem normalizedError_norm (F : X ≃L[𝕜] Y) (A : X →L[𝕜] Y) :
    ‖normalizedError F A‖ ≤ ‖F.symm.toContinuousLinearMap‖ *
      ‖A - F.toContinuousLinearMap‖ := ContinuousLinearMap.opNorm_comp_le _ _

omit [CompleteSpace X] in
theorem normalizedError_small_of_product (F : X ≃L[𝕜] Y) (A : X →L[𝕜] Y)
    {q : ℝ} (h : ‖F.symm.toContinuousLinearMap‖ * ‖A - F.toContinuousLinearMap‖ ≤ q) :
    ‖normalizedError F A‖ ≤ q := (normalizedError_norm F A).trans h

omit [CompleteSpace X] in
theorem perturbationInverse_norm_half (F : X ≃L[𝕜] Y) (A : X →L[𝕜] Y)
    (h : ‖normalizedError F A‖ ≤ (1 / 2 : ℝ)) :
    ‖perturbationInverse F A‖ ≤ 2 * ‖F.symm.toContinuousLinearMap‖ := by
  have ht := perturbationInverse_norm_of_le F A h (by norm_num : (1 / 2 : ℝ) < 1)
  norm_num at ht
  exact ht

@[simp] theorem perturbationInverse_reference (F : X ≃L[𝕜] Y) :
    perturbationInverse F F.toContinuousLinearMap = F.symm.toContinuousLinearMap := by
  simp [perturbationInverse, normalizedError]
  ext y
  rfl

def perturbationEquiv (F : X ≃L[𝕜] Y) (A : X →L[𝕜] Y)
    (h : ‖normalizedError F A‖ < 1) : X ≃L[𝕜] Y :=
  ContinuousLinearEquiv.equivOfInverse' A (perturbationInverse F A)
    (perturbationInverse_right F A h) (perturbationInverse_left F A h)

@[simp] theorem perturbationEquiv_forward (F : X ≃L[𝕜] Y) (A : X →L[𝕜] Y)
    (h : ‖normalizedError F A‖ < 1) : (perturbationEquiv F A h).toContinuousLinearMap = A := rfl

@[simp] theorem perturbationEquiv_inverse (F : X ≃L[𝕜] Y) (A : X →L[𝕜] Y)
    (h : ‖normalizedError F A‖ < 1) :
    (perturbationEquiv F A h).symm.toContinuousLinearMap = perturbationInverse F A := rfl

end Grad.Foundations
