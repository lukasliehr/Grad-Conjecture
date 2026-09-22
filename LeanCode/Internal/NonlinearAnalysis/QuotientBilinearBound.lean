import QuotientBilinearInterface

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct Grad.NonlinearRadial

def radialMeanLaplacianConstant (grade : ℕ) : ℝ :=
  dilationGradeConstant grade * laplacianGradeConstant grade * orthogonalGradeConstant (grade + 2)

theorem radialMeanLaplacianConstant_nonnegative (grade : ℕ) : 0 ≤ radialMeanLaplacianConstant grade :=
  mul_nonneg (mul_nonneg (dilationGradeConstant_nonnegative _) (laplacianGradeConstant_nonnegative _))
    (orthogonalGradeConstant_nonnegative _)

theorem radial_mean_laplacian_bound {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (radialCore parameters (laplacianCore parameters (angularCore parameters 0 field))) ≤
      radialMeanLaplacianConstant grade * originalGradeNorm (grade + 2) field := by
  have angularBound : originalGradeNorm (grade + 2) (angularCore parameters 0 field) ≤
      orthogonalGradeConstant (grade + 2) * originalGradeNorm (grade + 2) field :=
    angularGradeCore_norm_le parameters 0 (GradeCore.ofCoreLinear field)
  calc
    _ ≤ dilationGradeConstant grade * originalGradeNorm grade
        (laplacianCore parameters (angularCore parameters 0 field)) := radialCore_bound parameters grade _
    _ ≤ dilationGradeConstant grade * (laplacianGradeConstant grade *
        (orthogonalGradeConstant (grade + 2) * originalGradeNorm (grade + 2) field)) := by
      apply mul_le_mul_of_nonneg_left _ (dilationGradeConstant_nonnegative _)
      exact (laplacianCore_bound parameters _ grade).trans
        (mul_le_mul_of_nonneg_left angularBound (laplacianGradeConstant_nonnegative _))
    _ = _ := by unfold radialMeanLaplacianConstant; ring

theorem oneHighExpression_pair {dimension : ℕ} {parameters : PhaseParameters}
    (first second : ACore parameters dimension) (grade : ℕ) :
    oneHighExpression grade ![first, second] =
      originalGradeNorm (grade + 3) first * originalGradeNorm 3 second +
        originalGradeNorm (grade + 3) second * originalGradeNorm 3 first := by
  have eraseZero : (Finset.univ : Finset (Fin 2)).erase 0 = {1} := by decide
  have eraseOne : (Finset.univ : Finset (Fin 2)).erase 1 = {0} := by decide
  unfold oneHighExpression
  rw [Fin.sum_univ_two, eraseZero, eraseOne]
  simp

def radialQuotientConstant (grade : ℕ) : ℝ :=
  radialMeanLaplacianConstant grade * productGradeConstant 1 (grade + 2) *
    vectorDerivativeGradeConstant (grade + 5) * vectorDerivativeGradeConstant 3

theorem radialQuotientConstant_nonnegative (grade : ℕ) : 0 ≤ radialQuotientConstant grade :=
  mul_nonneg (mul_nonneg (mul_nonneg (radialMeanLaplacianConstant_nonnegative _)
    (productGradeConstant_nonnegative _ _)) (vectorDerivativeGradeConstant_nonnegative _))
    (vectorDerivativeGradeConstant_nonnegative _)

theorem bilinearRadialCore_bound {dimension outputDimension : ℕ} (parameters : PhaseParameters)
    (multiplication : ContinuousMultilinearMap ℂ
      (fun _ : Fin 2 => ComplexEuclidean dimension) (ComplexEuclidean outputDimension))
    (first second : ACore parameters dimension) (grade : ℕ) :
    originalGradeNorm grade (bilinearRadialCore parameters multiplication first second) ≤
      radialQuotientConstant grade * ‖multiplication‖ *
        (originalGradeNorm (grade + 6) first * originalGradeNorm 4 second +
          originalGradeNorm 4 first * originalGradeNorm (grade + 6) second) := by
  have derivativeBound : oneHighExpression (grade + 2)
      ![eulerCore parameters first, rotationCore parameters second] ≤
      vectorDerivativeGradeConstant (grade + 5) * vectorDerivativeGradeConstant 3 *
        (originalGradeNorm (grade + 6) first * originalGradeNorm 4 second +
          originalGradeNorm 4 first * originalGradeNorm (grade + 6) second) := by
    rw [oneHighExpression_pair]
    have firstBound := mul_le_mul (eulerCore_bound parameters first (grade + 5))
      (rotationCore_bound parameters second 3) (originalGradeNorm_nonnegative _ _)
      (mul_nonneg (vectorDerivativeGradeConstant_nonnegative _) (originalGradeNorm_nonnegative _ _))
    have secondBound := mul_le_mul (rotationCore_bound parameters second (grade + 5))
      (eulerCore_bound parameters first 3) (originalGradeNorm_nonnegative _ _)
      (mul_nonneg (vectorDerivativeGradeConstant_nonnegative _) (originalGradeNorm_nonnegative _ _))
    exact (add_le_add firstBound secondBound).trans_eq (by ring)
  have productBound := actualMultilinearProduct_bound parameters multiplication
    ![eulerCore parameters first, rotationCore parameters second] (grade + 2)
  unfold bilinearRadialCore
  apply (radial_mean_laplacian_bound parameters _ grade).trans
  apply le_trans (mul_le_mul_of_nonneg_left productBound (radialMeanLaplacianConstant_nonnegative _))
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left derivativeBound
      (mul_nonneg (productGradeConstant_nonnegative _ _) (norm_nonneg _)))
    (radialMeanLaplacianConstant_nonnegative _)).trans_eq
  unfold radialQuotientConstant
  ring

theorem actual_radial_quotient_bound : RadialQuotientBoundGoal :=
  ⟨radialQuotientConstant, radialQuotientConstant_nonnegative,
    fun _ _ parameters multiplication first second grade =>
      bilinearRadialCore_bound parameters multiplication first second grade⟩

end Grad.NonlinearQuotientBounds
