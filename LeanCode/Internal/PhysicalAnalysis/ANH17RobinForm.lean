import ANH16HighL2
import ANH5PhysicalBoundary
import Mathlib.Analysis.InnerProductSpace.LaxMilgram

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.CircularHighWeak
open Grad.CartesianState

instance highDisk_normedAddCommGroup : NormedAddCommGroup highDiskGrade := by infer_instance

instance highDisk_complexInner : InnerProductSpace ℂ highDiskGrade :=
  @Submodule.innerProductSpace ℂ diskGrade _ _ (by infer_instance) highDiskGrade

instance highDisk_realInner : InnerProductSpace ℝ highDiskGrade :=
  InnerProductSpace.rclikeToReal ℂ highDiskGrade
instance highDisk_realPairing : Inner ℝ highDiskGrade := highDisk_realInner.toInner

instance highDisk_realModule : Module ℝ highDiskGrade := highDisk_realInner.toNormedSpace.toModule

instance diskL2_realInner : InnerProductSpace ℝ (DiskL2 1) :=
  InnerProductSpace.rclikeToReal ℂ (DiskL2 1)
instance diskL2_realPairing : Inner ℝ (DiskL2 1) := diskL2_realInner.toInner

instance diskL2_realModule : Module ℝ (DiskL2 1) := diskL2_realInner.toNormedSpace.toModule

instance boundaryL2_realInner : InnerProductSpace ℝ BoundaryL2 :=
  InnerProductSpace.rclikeToReal ℂ BoundaryL2

instance boundaryL2_realPairing : Inner ℝ BoundaryL2 := boundaryL2_realInner.toInner

instance boundaryL2_realModule : Module ℝ BoundaryL2 := boundaryL2_realInner.toNormedSpace.toModule

def highGradX : highDiskGrade →L[ℂ] DiskL2 1 := diskGradX.comp highDiskGrade.subtypeL
def highGradY : highDiskGrade →L[ℂ] DiskL2 1 := diskGradY.comp highDiskGrade.subtypeL
def robinTrace : highDiskGrade →L[ℂ] BoundaryL2 := diskBoundary.comp highDiskGrade.subtypeL

/-- The literal complex Robin form, linear in the solution and conjugate
linear in the test. The boundary space carries ordinary unweighted dθ. -/
def robinValue (parameter : ℝ) (field test : highDiskGrade) : ℂ :=
  inner ℂ (highGradX test) (highGradX field) +
  inner ℂ (highGradY test) (highGradY field) +
  (parameter ^ 2 : ℝ) * inner ℂ (highDiskBulk test) (diskB (highDiskBulk field)) +
  2 * inner ℂ (robinTrace test) (robinTrace field)

/-- Its bounded real bilinear form on the faithful full-disk H1 space. -/
def robinForm (parameter : ℝ) : highDiskGrade →L[ℝ] highDiskGrade →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (highGradX.restrictScalars ℝ) (highGradX.restrictScalars ℝ) +
  (innerSL ℝ).bilinearComp (highGradY.restrictScalars ℝ) (highGradY.restrictScalars ℝ) +
  parameter ^ 2 • (innerSL ℝ).bilinearComp
    ((diskB.comp highDiskBulk).restrictScalars ℝ) (highDiskBulk.restrictScalars ℝ) +
  (2 : ℝ) • (innerSL ℝ).bilinearComp (robinTrace.restrictScalars ℝ) (robinTrace.restrictScalars ℝ)

theorem robinForm_apply (parameter : ℝ) (field test : highDiskGrade) :
    robinForm parameter field test =
      inner ℝ (highGradX field) (highGradX test) +
      inner ℝ (highGradY field) (highGradY test) +
      parameter ^ 2 * inner ℝ (diskB (highDiskBulk field)) (highDiskBulk test) +
      2 * inner ℝ (robinTrace field) (robinTrace test) := by
  simp [robinForm, innerSL_apply_apply]

theorem robinForm_literal (parameter : ℝ) (field test : highDiskGrade) :
    robinForm parameter field test = (robinValue parameter field test).re := by
  rw [robinForm_apply]
  change (inner ℂ (highGradX field) (highGradX test)).re +
    (inner ℂ (highGradY field) (highGradY test)).re +
    parameter ^ 2 * (inner ℂ (diskB (highDiskBulk field)) (highDiskBulk test)).re +
    2 * (inner ℂ (robinTrace field) (robinTrace test)).re = _
  simp only [robinValue, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  norm_num
  have first : (inner ℂ (highGradX field) (highGradX test)).re =
      (inner ℂ (highGradX test) (highGradX field)).re := inner_re_symm (𝕜 := ℂ) _ _
  have second : (inner ℂ (highGradY field) (highGradY test)).re =
      (inner ℂ (highGradY test) (highGradY field)).re := inner_re_symm (𝕜 := ℂ) _ _
  have mass : (inner ℂ (diskB (highDiskBulk field)) (highDiskBulk test)).re =
      (inner ℂ (highDiskBulk test) (diskB (highDiskBulk field))).re := inner_re_symm (𝕜 := ℂ) _ _
  have boundary : (inner ℂ (robinTrace field) (robinTrace test)).re =
      (inner ℂ (robinTrace test) (robinTrace field)).re := inner_re_symm (𝕜 := ℂ) _ _
  exact congrArg₂ (fun first second : ℝ => first + second)
    (congrArg₂ (fun first second : ℝ => first + second)
      (congrArg₂ (fun first second : ℝ => first + second) first second)
      (congrArg (fun value : ℝ => parameter ^ 2 * value) mass))
    (congrArg (fun value : ℝ => 2 * value) boundary)

theorem robinForm_diagonal (parameter : ℝ) (field : highDiskGrade) :
    robinForm parameter field field = ‖highGradX field‖ ^ 2 + ‖highGradY field‖ ^ 2 +
      parameter ^ 2 * (inner ℂ (highDiskBulk field) (diskB (highDiskBulk field))).re +
      2 * ‖robinTrace field‖ ^ 2 := by
  have first : inner ℝ (highGradX field) (highGradX field) = ‖highGradX field‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have second : inner ℝ (highGradY field) (highGradY field) = ‖highGradY field‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have boundary : inner ℝ (robinTrace field) (robinTrace field) = ‖robinTrace field‖ ^ 2 :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).symm
  have mass : inner ℝ (diskB (highDiskBulk field)) (highDiskBulk field) =
      (inner ℂ (highDiskBulk field) (diskB (highDiskBulk field))).re := inner_re_symm (𝕜 := ℂ) _ _
  exact (robinForm_apply parameter field field).trans
    (congrArg₂ (fun first second : ℝ => first + second)
      (congrArg₂ (fun first second : ℝ => first + second)
        (congrArg₂ (fun first second : ℝ => first + second) first second)
        (congrArg (fun value : ℝ => parameter ^ 2 * value) mass))
      (congrArg (fun value : ℝ => 2 * value) boundary))

theorem highBulk_norm_le (field : highDiskGrade) : ‖highDiskBulk field‖ ≤ ‖field‖ := by
  have norm := highDiskGrade_norm_sq field
  nlinarith [norm_nonneg field, norm_nonneg (highDiskBulk field),
    sq_nonneg ‖diskGradX field.val‖, sq_nonneg ‖diskGradY field.val‖]

theorem robinForm_coercivity (parameter : ℝ) (field : highDiskGrade) :
    (1 / 2 : ℝ) * ‖field‖ ^ 2 ≤ robinForm parameter field field := by
  rw [robinForm_diagonal]
  have nonnegative := mul_nonneg (sq_nonneg parameter) (diskB_nonnegative (highDiskBulk field))
  have poincare := highDisk_poincare field
  have norm := highDiskGrade_norm_sq field
  change _ ≤ ‖diskGradX field.val‖ ^ 2 + ‖diskGradY field.val‖ ^ 2 + _ + _
  nlinarith [sq_nonneg ‖robinTrace field‖, sq_nonneg ‖highDiskBulk field‖]

theorem robinForm_isCoercive (parameter : ℝ) : IsCoercive (robinForm parameter) := by
  refine ⟨1 / 2, by norm_num, fun field => ?_⟩
  simpa only [sq, mul_assoc] using robinForm_coercivity parameter field

end Grad.CircularHighWeak
