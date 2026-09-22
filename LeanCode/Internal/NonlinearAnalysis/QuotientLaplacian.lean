import QuotientDerivativeCompletion

noncomputable section

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct

def laplacianCore {dimension : ℕ} (parameters : PhaseParameters) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension :=
  (partialCore parameters 0).comp (partialCore parameters 0) +
    (partialCore parameters 1).comp (partialCore parameters 1)

theorem partialJet_twice {dimension : ℕ} (direction : Fin 2) (field : ClosedJet dimension) :
    (partialJet direction (partialJet direction field)).value =
      closedDerivative field 2 (fun _ => direction) := by
  change closedDerivative (partialJet direction field) 1 (fun _ => direction) = _
  rw [partialJet_closedDerivative]
  congr 1
  funext position
  fin_cases position <;> rfl

theorem laplacianCore_actual {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) :
    IsActualLaplacian field (laplacianCore parameters field) := by
  intro cell
  change (partialJet 0 (partialJet 0 (field.val cell)) +
    partialJet 1 (partialJet 1 (field.val cell))).value = _
  rw [closedJet_value_add, partialJet_twice, partialJet_twice]
  rfl

def laplacianGradeConstant (grade : ℕ) : ℝ :=
  2 * partialGradeConstant grade * partialGradeConstant (grade + 1)

theorem laplacianGradeConstant_nonnegative (grade : ℕ) : 0 ≤ laplacianGradeConstant grade :=
  mul_nonneg (mul_nonneg (by norm_num) (partialGradeConstant_nonnegative _))
    (partialGradeConstant_nonnegative _)

theorem originalGradeNorm_add_le {dimension : ℕ} {parameters : PhaseParameters}
    (grade : ℕ) (first second : ACore parameters dimension) :
    originalGradeNorm grade (first + second) ≤
      originalGradeNorm grade first + originalGradeNorm grade second := by
  unfold originalGradeNorm
  rw [map_add]
  exact norm_add_le _ _

theorem laplacianCore_bound {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (laplacianCore parameters field) ≤
      laplacianGradeConstant grade * originalGradeNorm (grade + 2) field := by
  have twice (direction : Fin 2) :
      originalGradeNorm grade (partialCore parameters direction (partialCore parameters direction field)) ≤
        partialGradeConstant grade * (partialGradeConstant (grade + 1) * originalGradeNorm (grade + 2) field) := by
    exact (partialCore_bound parameters direction _ grade).trans
      (mul_le_mul_of_nonneg_left (partialCore_bound parameters direction field (grade + 1))
        (partialGradeConstant_nonnegative _))
  exact (originalGradeNorm_add_le grade _ _).trans ((add_le_add (twice 0) (twice 1)).trans_eq (by
    unfold laplacianGradeConstant
    ring))

theorem actual_laplacian : LaplacianGoal := by
  refine ⟨laplacianGradeConstant, laplacianGradeConstant_nonnegative, ?_⟩
  intro parameters dimension
  exact ⟨laplacianCore parameters, laplacianCore_actual parameters,
    fun grade field => laplacianCore_bound parameters field grade⟩

def laplacianGradeCore {dimension grade : ℕ} (parameters : PhaseParameters) :
    GradeCore parameters dimension (grade + 2) →ₗ[ℂ] GradeCore parameters dimension grade :=
  GradeCore.ofCoreLinear.comp ((laplacianCore parameters).comp GradeCore.toCoreLinear)

def laplacianCompleted {dimension grade : ℕ} (parameters : PhaseParameters) :
    AGrade parameters dimension (grade + 2) →L[ℂ] AGrade parameters dimension grade :=
  denseCoreExtension parameters
    ((aGradeEta parameters).toLinearMap.comp (laplacianGradeCore parameters))
    (laplacianGradeConstant grade) (fun field => by
      change ‖aGradeEta parameters (laplacianGradeCore parameters field)‖ ≤ _
      rw [aGradeEta_norm]
      exact laplacianCore_bound parameters field.toCore grade)

theorem laplacianCompleted_eta {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) :
    laplacianCompleted (grade := grade) parameters (aGradeEta parameters (GradeCore.ofCoreLinear field)) =
      aGradeEta parameters (GradeCore.ofCoreLinear (laplacianCore parameters field)) :=
  denseCoreExtension_apply_eta parameters _ _ _ _

theorem laplacianCompleted_bound {dimension grade : ℕ} (parameters : PhaseParameters)
    (field : AGrade parameters dimension (grade + 2)) :
    ‖laplacianCompleted parameters field‖ ≤ laplacianGradeConstant grade * ‖field‖ :=
  denseCoreExtension_apply_norm_le parameters _ _ _ field

end Grad.NonlinearQuotientBounds
