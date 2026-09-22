import GC14FrameConstruction

noncomputable section

set_option maxHeartbeats 800000

open Set
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope

theorem coefficientScalarNorm_le {L sigma gamma ell : ℝ} {grade inputDimension outputDimension : ℕ}
    (scalar : ℂ) (coefficient : Coefficient L sigma gamma ell grade inputDimension outputDimension) :
    ‖scalar • coefficient‖ ≤ ‖scalar‖ * ‖coefficient‖ := by
  change ‖scalar • coefficient.val‖ ≤ ‖scalar‖ * ‖coefficient.val‖
  exact norm_smul_le scalar coefficient.val

def frameStateConstant (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) : ℝ :=
  shiftedStateConstant parameters grade 1 * (‖columnEmbedding 3 3 0‖ + ‖columnEmbedding 3 3 1‖) +
    L⁻¹ * shiftedStateConstant parameters grade 0 *
      (‖columnEmbedding 3 3 2‖ + ‖referenceCurvatureMapping‖)

def frameConstant (parameters : PhaseParameters) (L : ℝ) (grade : ℕ) : ℝ :=
  frameStateConstant parameters L grade + L⁻¹ * referenceCurvatureConstant parameters grade

theorem frameStateConstant_nonnegative (parameters : PhaseParameters) {L : ℝ} (positive : 0 < L)
    (grade : ℕ) : 0 ≤ frameStateConstant parameters L grade := by
  have first := shiftedStateConstant_nonnegative parameters grade 1
  have zeroth := shiftedStateConstant_nonnegative parameters grade 0
  unfold frameStateConstant
  positivity

theorem frameConstant_nonnegative (parameters : PhaseParameters) {L : ℝ} (positive : 0 < L)
    (grade : ℕ) : 0 ≤ frameConstant parameters L grade :=
  add_nonneg (frameStateConstant_nonnegative parameters positive grade)
    (mul_nonneg (inv_nonneg.mpr positive.le) (referenceCurvatureConstant_nonnegative parameters grade))

/-- Actual Cartesian frame coefficient estimate with one state derivative and
the exact AP21 `q+4` state grade. -/
theorem actualFrameDeviationCoefficient_norm_bound {L ell : ℝ} {grade : ℕ}
    (parameters : PhaseParameters) (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (epsilon : ℝ) (epsilonLe : |epsilon| ≤ 1) (field : GradeCore parameters 3 (grade + 4)) :
    ‖actualFrameDeviationCoefficient parameters L ell epsilon field‖ ≤
      frameConstant parameters L grade * (‖field‖ + |epsilon|) := by
  let first : Coefficient L parameters.sigma0 parameters.gamma ell grade 3 3 :=
    shiftedStateCoefficient parameters L ell grade (columnEmbedding 3 3 0)
    field.toCore (fun _ : Fin 1 => 0) 0
  let second : Coefficient L parameters.sigma0 parameters.gamma ell grade 3 3 :=
    shiftedStateCoefficient parameters L ell grade (columnEmbedding 3 3 1)
    field.toCore (fun _ : Fin 1 => 1) 0
  let third : Coefficient L parameters.sigma0 parameters.gamma ell grade 3 3 :=
    shiftedStateCoefficient parameters L ell grade (columnEmbedding 3 3 2)
    field.toCore emptyCartesianWord 1
  let rotated : Coefficient L parameters.sigma0 parameters.gamma ell grade 3 3 :=
    shiftedStateCoefficient parameters L ell grade referenceCurvatureMapping
    field.toCore emptyCartesianWord 0
  let reference : Coefficient L parameters.sigma0 parameters.gamma ell grade 3 3 :=
    referenceCurvatureCoefficient parameters L ell grade
  have firstBound : ‖first‖ ≤ shiftedStateConstant parameters grade 1 *
      ‖columnEmbedding 3 3 0‖ * ‖field‖ :=
    shiftedStateCoefficient_norm_bound (j := grade + 1) parameters admissible _ field _ _ (by omega)
  have secondBound : ‖second‖ ≤ shiftedStateConstant parameters grade 1 *
      ‖columnEmbedding 3 3 1‖ * ‖field‖ :=
    shiftedStateCoefficient_norm_bound (j := grade + 1) parameters admissible _ field _ _ (by omega)
  have thirdBound : ‖third‖ ≤ shiftedStateConstant parameters grade 0 *
      ‖columnEmbedding 3 3 2‖ * ‖field‖ :=
    shiftedStateCoefficient_norm_bound (j := grade + 1) parameters admissible _ field _ _ (by omega)
  have rotatedBound : ‖rotated‖ ≤ shiftedStateConstant parameters grade 0 *
      ‖referenceCurvatureMapping‖ * ‖field‖ :=
    shiftedStateCoefficient_norm_bound (j := grade + 1) parameters admissible _ field _ _ (by omega)
  have referenceBound : ‖reference‖ ≤ referenceCurvatureConstant parameters grade :=
    referenceCurvatureCoefficient_norm_bound parameters admissible grade
  have invPositive : 0 ≤ L⁻¹ := inv_nonneg.mpr admissible.1.le
  have inverseNorm : ‖(L : ℂ)⁻¹‖ = L⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg admissible.1.le]
  have epsilonNorm : ‖(epsilon : ℂ) * (L : ℂ)⁻¹‖ = |epsilon| * L⁻¹ := by
    rw [norm_mul, inverseNorm, Complex.norm_real, Real.norm_eq_abs]
  have zeroConstant := shiftedStateConstant_nonnegative parameters grade 0
  have referenceConstant := referenceCurvatureConstant_nonnegative parameters grade
  have curvatureSmall : |epsilon| *
      (L⁻¹ * shiftedStateConstant parameters grade 0 * ‖referenceCurvatureMapping‖ * ‖field‖) ≤
      L⁻¹ * shiftedStateConstant parameters grade 0 * ‖referenceCurvatureMapping‖ * ‖field‖ :=
    mul_le_of_le_one_left (by positivity) epsilonLe
  have thirdScalar : ‖(L : ℂ)⁻¹ • third‖ ≤ L⁻¹ * ‖third‖ := by
    have scalar := coefficientScalarNorm_le (L : ℂ)⁻¹ third
    rwa [inverseNorm] at scalar
  have curvatureScalar : ‖((epsilon : ℂ) * (L : ℂ)⁻¹) • (rotated + reference)‖ ≤
      (|epsilon| * L⁻¹) * (‖rotated‖ + ‖reference‖) := by
    have scalar := coefficientScalarNorm_le ((epsilon : ℂ) * (L : ℂ)⁻¹) (rotated + reference)
    rw [epsilonNorm] at scalar
    exact scalar.trans (mul_le_mul_of_nonneg_left (norm_add_le rotated reference)
      (mul_nonneg (abs_nonneg epsilon) invPositive))
  change ‖first + second + (L : ℂ)⁻¹ • third +
    ((epsilon : ℂ) * (L : ℂ)⁻¹) • (rotated + reference)‖ ≤ _
  calc
    _ ≤ ‖first‖ + ‖second‖ + ‖(L : ℂ)⁻¹ • third‖ +
        ‖((epsilon : ℂ) * (L : ℂ)⁻¹) • (rotated + reference)‖ :=
      (norm_add_le _ _).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le first second) le_rfl)) le_rfl)
    _ ≤ ‖first‖ + ‖second‖ + L⁻¹ * ‖third‖ +
        (|epsilon| * L⁻¹) * (‖rotated‖ + ‖reference‖) :=
      add_le_add (add_le_add le_rfl thirdScalar) curvatureScalar
    _ ≤ shiftedStateConstant parameters grade 1 * ‖columnEmbedding 3 3 0‖ * ‖field‖ +
        shiftedStateConstant parameters grade 1 * ‖columnEmbedding 3 3 1‖ * ‖field‖ +
        L⁻¹ * (shiftedStateConstant parameters grade 0 * ‖columnEmbedding 3 3 2‖ * ‖field‖) +
        (|epsilon| * L⁻¹) *
          (shiftedStateConstant parameters grade 0 * ‖referenceCurvatureMapping‖ * ‖field‖ +
            referenceCurvatureConstant parameters grade) := by
      exact add_le_add (add_le_add (add_le_add firstBound secondBound)
        (mul_le_mul_of_nonneg_left thirdBound invPositive))
        (mul_le_mul_of_nonneg_left (add_le_add rotatedBound referenceBound)
          (mul_nonneg (abs_nonneg epsilon) invPositive))
    _ ≤ frameStateConstant parameters L grade * ‖field‖ +
        (L⁻¹ * referenceCurvatureConstant parameters grade) * |epsilon| := by
      unfold frameStateConstant
      nlinarith [curvatureSmall]
    _ ≤ _ := by
      have statePositive := frameStateConstant_nonnegative parameters admissible.1 grade
      have referencePositive : 0 ≤ L⁻¹ * referenceCurvatureConstant parameters grade :=
        mul_nonneg invPositive referenceConstant
      unfold frameConstant
      nlinarith [mul_nonneg statePositive (abs_nonneg epsilon),
        mul_nonneg referencePositive (norm_nonneg field)]

end Grad.GaugeCoefficients.Physical.Frame
