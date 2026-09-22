import AIC12ActualInteriorEquation

noncomputable section
open scoped ContDiff

namespace Grad.InteriorLocalization
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.CircularHighWeak Grad.CircularHighRegularity

local instance localizationDiskNormed : NormedAddCommGroup diskGrade := by infer_instance
local instance localizationDiskComplex : InnerProductSpace ℂ diskGrade :=
  @Submodule.innerProductSpace ℂ DiskAmbient _ _ (by infer_instance) diskGrade
local instance localizationDiskSpace : NormedSpace ℂ diskGrade := localizationDiskComplex.toNormedSpace

private theorem diskCoordinate_bounds (field : diskGrade) :
    ‖diskBulk field‖ ≤ ‖field‖ ∧ ‖diskGradX field‖ ≤ ‖field‖ ∧ ‖diskGradY field‖ ≤ ‖field‖ := by
  have identity := diskGrade_norm_sq field
  have bulkNonnegative := norm_nonneg (diskBulk field)
  have xNonnegative := norm_nonneg (diskGradX field)
  have yNonnegative := norm_nonneg (diskGradY field)
  have fieldNonnegative := norm_nonneg field
  constructor
  · nlinarith [sq_nonneg ‖diskGradX field‖, sq_nonneg ‖diskGradY field‖]
  constructor
  · nlinarith [sq_nonneg ‖diskBulk field‖, sq_nonneg ‖diskGradY field‖]
  · nlinarith [sq_nonneg ‖diskBulk field‖, sq_nonneg ‖diskGradX field‖]

/-- The fixed first-order commutator with the interior cutoff, acting on
actual completed disk H1 coordinates. -/
def cutoffStateLaplacian : diskGrade →L[ℂ] DiskL2 1 :=
  (2 : ℂ) • (diskScalar (firstTestDerivative 0 interiorCutoff.toFun)
    (firstTestDerivative_smooth 0 _ interiorCutoff.smooth)).comp diskGradX +
  (2 : ℂ) • (diskScalar (firstTestDerivative 1 interiorCutoff.toFun)
    (firstTestDerivative_smooth 1 _ interiorCutoff.smooth)).comp diskGradY +
  (diskScalar (secondTestDerivative 0 interiorCutoff.toFun)
    (secondTestDerivative_smooth 0 _ interiorCutoff.smooth)).comp diskBulk +
  (diskScalar (secondTestDerivative 1 interiorCutoff.toFun)
    (secondTestDerivative_smooth 1 _ interiorCutoff.smooth)).comp diskBulk

def cutoffLaplacianSourceConstant : ℝ := ‖diskScalar interiorCutoff.toFun interiorCutoff.smooth‖
def cutoffLaplacianStateConstant : ℝ := ‖cutoffStateLaplacian‖

theorem cutoffLaplacianSourceConstant_nonnegative : 0 ≤ cutoffLaplacianSourceConstant :=
  norm_nonneg (diskScalar interiorCutoff.toFun interiorCutoff.smooth)
theorem cutoffLaplacianStateConstant_nonnegative : 0 ≤ cutoffLaplacianStateConstant :=
  norm_nonneg cutoffStateLaplacian

theorem localizedDiskLaplacian_split (field : diskGrade) (laplacian : DiskL2 1) :
    localizedDiskLaplacian field laplacian =
      diskScalar interiorCutoff.toFun interiorCutoff.smooth laplacian + cutoffStateLaplacian field := by
  change _ = diskScalar interiorCutoff.toFun interiorCutoff.smooth laplacian +
    (((2 : ℂ) • diskScalar (firstTestDerivative 0 interiorCutoff.toFun)
      (firstTestDerivative_smooth 0 _ interiorCutoff.smooth) (diskGradX field) +
    (2 : ℂ) • diskScalar (firstTestDerivative 1 interiorCutoff.toFun)
      (firstTestDerivative_smooth 1 _ interiorCutoff.smooth) (diskGradY field)) +
    diskScalar (secondTestDerivative 0 interiorCutoff.toFun)
      (secondTestDerivative_smooth 0 _ interiorCutoff.smooth) (diskBulk field) +
    diskScalar (secondTestDerivative 1 interiorCutoff.toFun)
      (secondTestDerivative_smooth 1 _ interiorCutoff.smooth) (diskBulk field))
  simp only [localizedDiskLaplacian, add_assoc]

theorem localizedDiskLaplacian_bound (field : diskGrade) (laplacian : DiskL2 1) :
    ‖localizedDiskLaplacian field laplacian‖ ≤
      cutoffLaplacianSourceConstant * ‖laplacian‖ + cutoffLaplacianStateConstant * ‖field‖ := by
  have stateBound : ‖cutoffStateLaplacian field‖ ≤ cutoffLaplacianStateConstant * ‖field‖ :=
    @ContinuousLinearMap.le_opNorm ℂ ℂ diskGrade (DiskL2 1)
      localizationDiskNormed.toSeminormedAddCommGroup _ _ _ localizationDiskSpace _ (RingHom.id ℂ) _
      cutoffStateLaplacian field
  have sourceBound : ‖diskScalar interiorCutoff.toFun interiorCutoff.smooth laplacian‖ ≤
      cutoffLaplacianSourceConstant * ‖laplacian‖ :=
    (diskScalar interiorCutoff.toFun interiorCutoff.smooth).le_opNorm laplacian
  exact (congrArg norm (localizedDiskLaplacian_split field laplacian)).le.trans
    ((norm_add_le _ _).trans (add_le_add sourceBound stateBound))

private theorem diskMassDifference_bound (parameter : ℝ) (field source : DiskL2 1) :
    ‖((parameter ^ 2 : ℝ) : ℂ) • diskB field - source‖ ≤ parameter ^ 2 * ‖field‖ + ‖source‖ := by
  have triangle := norm_sub_le (((parameter ^ 2 : ℝ) : ℂ) • diskB field) source
  rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg parameter)] at triangle
  exact triangle.trans (add_le_add (mul_le_mul_of_nonneg_left (diskB_bound field) (sq_nonneg parameter)) le_rfl)

theorem actualWeakLaplacian_bound (parameter : ℝ) (source : highDiskL2) :
    ‖weakLaplacianValue parameter source‖ ≤ (2 * parameter ^ 2 + 1) * ‖source‖ := by
  have bound : ‖highDiskBulk (highRobinWeakInverse parameter source)‖ ≤ 2 * ‖source‖ :=
    (diskCoordinate_bounds (highRobinWeakInverse parameter source).val).1.trans (weakSolution_bound parameter source)
  exact (diskMassDifference_bound parameter (highDiskBulk (highRobinWeakInverse parameter source)) source.val).trans
    ((add_le_add (mul_le_mul_of_nonneg_left bound (sq_nonneg parameter)) le_rfl).trans_eq (by
      change parameter ^ 2 * (2 * ‖source‖) + ‖source‖ = _
      ring))

/-- Fixed constant, independent of k and of the high source. -/
def interiorLaplacianConstant : ℝ :=
  ‖Grad.GaugeCoefficients.Physical.RadialLedger.apDiskInjection 1‖ *
    (2 * cutoffLaplacianSourceConstant + 2 * cutoffLaplacianStateConstant)

theorem interiorLaplacianConstant_nonnegative : 0 ≤ interiorLaplacianConstant :=
  mul_nonneg (norm_nonneg _) (add_nonneg (mul_nonneg (by norm_num) cutoffLaplacianSourceConstant_nonnegative)
    (mul_nonneg (by norm_num) cutoffLaplacianStateConstant_nonnegative))

theorem actualInteriorLaplacian_bound (parameter : ℝ) (source : highDiskL2) :
    ‖actualInteriorLaplacian parameter source‖ ≤ interiorLaplacianConstant * (1 + parameter ^ 2) * ‖source‖ := by
  have localized := localizedDiskLaplacian_bound (highRobinWeakInverse parameter source).val
    (weakLaplacianValue parameter source)
  have sourceBound := mul_le_mul_of_nonneg_left (actualWeakLaplacian_bound parameter source)
    cutoffLaplacianSourceConstant_nonnegative
  have stateNorm : ‖(highRobinWeakInverse parameter source).val‖ ≤ 2 * ‖source‖ :=
    weakSolution_bound parameter source
  have stateBound := mul_le_mul_of_nonneg_left stateNorm cutoffLaplacianStateConstant_nonnegative
  have combined : ‖localizedDiskLaplacian (highRobinWeakInverse parameter source).val
      (weakLaplacianValue parameter source)‖ ≤
      (2 * cutoffLaplacianSourceConstant + 2 * cutoffLaplacianStateConstant) *
        (1 + parameter ^ 2) * ‖source‖ := by
    nlinarith [mul_nonneg cutoffLaplacianSourceConstant_nonnegative (norm_nonneg source),
      mul_nonneg cutoffLaplacianStateConstant_nonnegative (mul_nonneg (sq_nonneg parameter) (norm_nonneg source))]
  exact (diskZeroExtension_bound _).trans ((mul_le_mul_of_nonneg_left combined (norm_nonneg _)).trans_eq (by
    unfold interiorLaplacianConstant
    ring))

end Grad.InteriorLocalization
