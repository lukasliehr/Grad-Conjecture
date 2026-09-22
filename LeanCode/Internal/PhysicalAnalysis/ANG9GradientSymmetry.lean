import ANG8TraceSymmetry

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.CircularHighWeak
open Grad.CartesianState

theorem highInner_decomposition (first second : highDiskGrade) :
    (inner ℂ first second).re =
      (inner ℂ (highDiskBulk first) (highDiskBulk second)).re +
      (inner ℂ (highGradX first) (highGradX second)).re +
      (inner ℂ (highGradY first) (highGradY second)).re := by
  have combined := highDiskGrade_norm_sq (first + second)
  have firstNorm := highDiskGrade_norm_sq first
  have secondNorm := highDiskGrade_norm_sq second
  change ‖first + second‖ ^ 2 = ‖highDiskBulk (first + second)‖ ^ 2 +
    ‖highGradX (first + second)‖ ^ 2 + ‖highGradY (first + second)‖ ^ 2 at combined
  change ‖first‖ ^ 2 = ‖highDiskBulk first‖ ^ 2 + ‖highGradX first‖ ^ 2 + ‖highGradY first‖ ^ 2 at firstNorm
  change ‖second‖ ^ 2 = ‖highDiskBulk second‖ ^ 2 + ‖highGradX second‖ ^ 2 + ‖highGradY second‖ ^ 2 at secondNorm
  have bulkAdd := congrArg (fun value : DiskL2 1 => ‖value‖ ^ 2) (highDiskBulk.map_add first second)
  have xAdd := congrArg (fun value : DiskL2 1 => ‖value‖ ^ 2) (highGradX.map_add first second)
  have yAdd := congrArg (fun value : DiskL2 1 => ‖value‖ ^ 2) (highGradY.map_add first second)
  have sumNorm := norm_add_sq (𝕜 := ℂ) first second
  have bulkNorm := norm_add_sq (𝕜 := ℂ) (highDiskBulk first) (highDiskBulk second)
  have xNorm := norm_add_sq (𝕜 := ℂ) (highGradX first) (highGradX second)
  have yNorm := norm_add_sq (𝕜 := ℂ) (highGradY first) (highGradY second)
  change ‖first + second‖ ^ 2 = ‖first‖ ^ 2 + 2 * (inner ℂ first second).re + ‖second‖ ^ 2 at sumNorm
  change ‖highDiskBulk first + highDiskBulk second‖ ^ 2 = ‖highDiskBulk first‖ ^ 2 +
    2 * (inner ℂ (highDiskBulk first) (highDiskBulk second)).re + ‖highDiskBulk second‖ ^ 2 at bulkNorm
  change ‖highGradX first + highGradX second‖ ^ 2 = ‖highGradX first‖ ^ 2 +
    2 * (inner ℂ (highGradX first) (highGradX second)).re + ‖highGradX second‖ ^ 2 at xNorm
  change ‖highGradY first + highGradY second‖ ^ 2 = ‖highGradY first‖ ^ 2 +
    2 * (inner ℂ (highGradY first) (highGradY second)).re + ‖highGradY second‖ ^ 2 at yNorm
  linarith

theorem highBulk_angular_symmetric (mode : ℤ) (first second : highDiskGrade) :
    inner ℂ (highDiskBulk (highDiskMode mode first)) (highDiskBulk second) =
      inner ℂ (highDiskBulk first) (highDiskBulk (highDiskMode mode second)) := by
  exact (congrArg (fun value : DiskL2 1 => inner ℂ value (highDiskBulk second)) (highDiskMode_bulk mode first)).trans
    ((diskMode_symmetric mode (highDiskBulk first) (highDiskBulk second)).trans
      (congrArg (fun value : DiskL2 1 => inner ℂ (highDiskBulk first) value) (highDiskMode_bulk mode second).symm))

theorem highGradient_angular_symmetric (mode : ℤ) (first second : highDiskGrade) :
    (inner ℂ (highGradX (highDiskMode mode first)) (highGradX second)).re +
      (inner ℂ (highGradY (highDiskMode mode first)) (highGradY second)).re =
    (inner ℂ (highGradX first) (highGradX (highDiskMode mode second))).re +
      (inner ℂ (highGradY first) (highGradY (highDiskMode mode second))).re := by
  have left := highInner_decomposition (highDiskMode mode first) second
  have right := highInner_decomposition first (highDiskMode mode second)
  have full := congrArg Complex.re (highDiskMode_symmetric mode first second)
  have bulk := congrArg Complex.re (highBulk_angular_symmetric mode first second)
  linarith

theorem diskB_mode (mode : ℤ) (field : DiskL2 1) :
    diskB (diskMode mode field) = (highMultiplier mode : ℂ) • diskMode mode field := by
  apply diskFourierIsometry.injective
  apply lp.ext
  funext other
  change diskMode other (diskB (diskMode mode field)) = diskMode other ((highMultiplier mode : ℂ) • diskMode mode field)
  rw [diskB_coefficient, map_smul, diskMode_projection]
  by_cases same : other = mode
  · subst other
    rfl
  · rw [if_neg same, smul_zero, smul_zero]

theorem diskB_angular_commute (mode : ℤ) (field : DiskL2 1) :
    diskB (diskMode mode field) = diskMode mode (diskB field) :=
  (diskB_mode mode field).trans (diskB_coefficient mode field).symm

end Grad.CircularHighWeak
