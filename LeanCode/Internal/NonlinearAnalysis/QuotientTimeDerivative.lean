import QuotientDerivativeCore
import FC6Monotone

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct

theorem cellGradeRow_frequency_bound {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (cell : ℤ) (field : ClosedJet dimension) :
    cellFrequency cell * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ≤
      ‖cellGradeRowLinear (grade := grade + 1) parameters cell field‖ := by
  apply (sq_le_sq₀ (mul_nonneg (cellFrequency_pos cell).le (norm_nonneg _)) (norm_nonneg _)).mp
  rw [mul_pow, cellGradeRow_norm_sq, cellGradeRow_norm_sq, Finset.mul_sum]
  let embedding := gradeMultiIndexEmbedding (show grade ≤ grade + 1 by omega)
  calc
    _ = ∑ index : GradeMultiIndex grade,
        m2IndexEnergy parameters (fun _ => field) cell (embedding index) := by
      apply Finset.sum_congr rfl
      intro index _
      change _ = cellFrequency cell ^ (2 * (grade + 1 - cartesianOrder index.toCartesian)) * _
      have power : 2 * (grade + 1 - cartesianOrder index.toCartesian) =
          2 + 2 * (grade - cartesianOrder index.toCartesian) := by
        have rankBound : cartesianOrder index.toCartesian ≤ grade := index.property
        omega
      rw [power, pow_add]
      change _ = cellFrequency cell ^ 2 * cellFrequency cell ^ (2 * (grade - cartesianOrder index.toCartesian)) *
        ‖closedContinuousToDiskL2 (closedMultiDerivative (phaseWeightedJet parameters cell field) index.toCartesian)‖ ^ 2
      ring
    _ = ∑ index ∈ Finset.univ.image embedding,
        m2IndexEnergy parameters (fun _ => field) cell index :=
      (Finset.sum_image embedding.injective.injOn).symm
    _ ≤ ∑ index : GradeMultiIndex (grade + 1),
        m2IndexEnergy parameters (fun _ => field) cell index := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro index _ _
      exact m2IndexEnergy_nonneg parameters _ cell index

theorem timeScalar_norm_bound (cell : ℤ) : ‖(cell : ℂ) * Complex.I‖ ≤ cellFrequency cell := by
  rw [norm_mul, Complex.norm_I, mul_one]
  have realCast : (cell : ℂ) = ((cell : ℝ) : ℂ) := by simp
  rw [realCast, Complex.norm_real, Real.norm_eq_abs]
  change |(cell : ℝ)| ≤ Real.sqrt (1 + (cell : ℝ) ^ 2)
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by linarith)

theorem timeDerivative_row_bound {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (cell : ℤ) (field : ClosedJet dimension) :
    ‖cellGradeRowLinear (grade := grade) parameters cell (((cell : ℂ) * Complex.I) • field)‖ ≤
      ‖cellGradeRowLinear (grade := grade + 1) parameters cell field‖ := by
  rw [map_smul, norm_smul]
  exact (mul_le_mul_of_nonneg_right (timeScalar_norm_bound cell) (norm_nonneg _)).trans
    (cellGradeRow_frequency_bound parameters grade cell field)

theorem timeDerivative_mem_core {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) :
    (fun cell : ℤ => ((cell : ℂ) * Complex.I) • field.val cell) ∈ originalCoreSubmodule parameters dimension := by
  intro grade
  apply (field.property (grade + 1)).mono'
  intro cell
  exact timeDerivative_row_bound parameters grade cell (field.val cell)

def timeDerivativeCore {dimension : ℕ} (parameters : PhaseParameters) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension where
  toFun field := ⟨fun cell => ((cell : ℂ) * Complex.I) • field.val cell,
    timeDerivative_mem_core parameters field⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    exact smul_add _ _ _
  map_smul' scalar field := by
    apply Subtype.ext
    funext cell
    change ((cell : ℂ) * Complex.I) • (scalar • field.val cell) =
      scalar • (((cell : ℂ) * Complex.I) • field.val cell)
    exact smul_comm _ _ _

theorem timeDerivativeCore_bound {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (field : ACore parameters dimension) :
    originalGradeNorm grade (timeDerivativeCore parameters field) ≤ originalGradeNorm (grade + 1) field := by
  unfold originalGradeNorm
  rw [gradeCore_norm_eq_cartesianGradeSeminorm, gradeCore_norm_eq_cartesianGradeSeminorm,
    cartesianGradeSeminorm_apply, cartesianGradeSeminorm_apply, gradeCoreCoordinates_apply, gradeCoreCoordinates_apply]
  apply lp.norm_mono (by norm_num)
  intro cell
  exact timeDerivative_row_bound parameters grade cell (field.val cell)

theorem actual_time_derivative : TimeDerivativeGoal := by
  intro parameters dimension
  exact ⟨timeDerivativeCore parameters, fun _ _ => rfl, timeDerivativeCore_bound parameters⟩

end Grad.NonlinearQuotientBounds
