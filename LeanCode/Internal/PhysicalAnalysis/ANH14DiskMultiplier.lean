import ANH13LiteralMultiplier
import Mathlib.Analysis.InnerProductSpace.Adjoint

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.CircularHighWeak

open Grad.ClosedJets Grad.CartesianState Grad.Constraints

theorem diskMode_symmetric (mode : ℤ) (first second : DiskL2 1) :
    inner ℂ (diskMode mode first) second = inner ℂ first (diskMode mode second) := by
  have left := diskFourierIsometry.inner_map_map (diskMode mode first) second
  have right := diskFourierIsometry.inner_map_map first (diskMode mode second)
  change inner ℂ (diskFourier (diskMode mode first)) (diskFourier second) = _ at left
  change inner ℂ (diskFourier first) (diskFourier (diskMode mode second)) = _ at right
  rw [diskFourier_mode, lp.inner_single_left] at left
  rw [diskFourier_mode, lp.inner_single_right] at right
  exact left.symm.trans right

/-- The actual full-disk angular multiplier, constructed using the proved
Fourier isometry and its Hilbert adjoint. Its high coefficients are U1. -/
def diskB : DiskL2 1 →L[ℂ] DiskL2 1 :=
  diskFourier.adjoint.comp (highDiagonal.comp diskFourier)

theorem diskFourier_opNorm_le : ‖diskFourier‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun field => by
    rw [one_mul, diskFourier_norm])

theorem diskB_bound (field : DiskL2 1) : ‖diskB field‖ ≤ ‖field‖ := by
  have adjointNorm : ‖diskFourier.adjoint‖ ≤ 1 :=
    (ContinuousLinearMap.adjoint.norm_map diskFourier).le.trans diskFourier_opNorm_le
  have first := diskFourier.adjoint.le_opNorm (highDiagonal (diskFourier field))
  have second := mul_le_mul_of_nonneg_right adjointNorm (norm_nonneg (highDiagonal (diskFourier field)))
  exact first.trans (second.trans ((one_mul _).le.trans
    ((highDiagonal_bound _).trans_eq (diskFourier_norm field))))

theorem diskB_symmetric (first second : DiskL2 1) :
    inner ℂ (diskB first) second = inner ℂ first (diskB second) := by
  change inner ℂ (diskFourier.adjoint (highDiagonal (diskFourier first))) second =
    inner ℂ first (diskFourier.adjoint (highDiagonal (diskFourier second)))
  exact (ContinuousLinearMap.adjoint_inner_left diskFourier second
    (highDiagonal (diskFourier first))).trans
      ((highDiagonal_symmetric (diskFourier first) (diskFourier second)).trans
        (ContinuousLinearMap.adjoint_inner_right diskFourier first
          (highDiagonal (diskFourier second))).symm)

theorem diskB_coefficient (mode : ℤ) (field : DiskL2 1) :
    diskMode mode (diskB field) = (highMultiplier mode : ℂ) • diskMode mode field := by
  apply ext_inner_right ℂ
  intro test
  rw [diskMode_symmetric]
  change inner ℂ (diskFourier.adjoint (highDiagonal (diskFourier field))) (diskMode mode test) = _
  rw [ContinuousLinearMap.adjoint_inner_left, diskFourier_mode, lp.inner_single_right,
    highDiagonal_apply]
  change inner ℂ ((highMultiplier mode : ℂ) • diskMode mode field) (diskMode mode test) = _
  rw [inner_smul_left, inner_smul_left, ← diskMode_symmetric, diskMode_projection, if_pos rfl]

theorem diskB_literal_high (mode : ℤ) (high : mode ∉ lowAngularModes) (field : DiskL2 1) :
    diskMode mode (diskB field) =
      ((1 - 4 / (mode : ℝ) ^ 2 : ℝ) : ℂ) • diskMode mode field := by
  rw [diskB_coefficient, highMultiplier_high mode high]

theorem diskB_nonnegative (field : DiskL2 1) : 0 ≤ (inner ℂ field (diskB field)).re := by
  change 0 ≤ (inner ℂ field (diskFourier.adjoint (highDiagonal (diskFourier field)))).re
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact highDiagonal_nonnegative _

theorem diskB_coercive (field : DiskL2 1)
    (high : ∀ mode ∈ lowAngularModes, diskMode mode field = 0) :
    (5 / 9 : ℝ) * ‖field‖ ^ 2 ≤ (inner ℂ field (diskB field)).re := by
  change (5 / 9 : ℝ) * ‖field‖ ^ 2 ≤
    (inner ℂ field (diskFourier.adjoint (highDiagonal (diskFourier field)))).re
  rw [ContinuousLinearMap.adjoint_inner_right]
  have bound := highDiagonal_coercive (diskFourier field) high
  rwa [diskFourier_norm] at bound

theorem highDiskBulk_spectral (field : highDiskGrade) (mode : ℤ) (low : mode ∈ lowAngularModes) :
    diskMode mode (highDiskBulk field) = 0 := by
  apply isClosed_property highDiskCoreInto_denseRange
    (isClosed_eq ((diskMode mode).continuous.comp highDiskBulk.continuous) continuous_const) _ field
  intro core
  have bulk : highDiskBulk (highDiskCoreInto core) =
      closedL2Core (excludedAngularJet lowAngularModes core) := by
    change diskCoordinate ⟨(0, 0), by decide⟩
      (diskCoreInto (excludedAngularJet lowAngularModes core)) = _
    rw [diskCoordinate_core]
    change closedContinuousToDiskL2 (closedMultiDerivative _ (0, 0)) = _
    rw [closedMultiDerivative_zero]
    rfl
  change diskMode mode (highDiskBulk (highDiskCoreInto core)) = 0
  rw [bulk, diskMode_core, excludedAngularJet_low_zero core mode low, map_zero]

theorem highDiskBulk_B_bound (field : highDiskGrade) :
    (5 / 9 : ℝ) * ‖highDiskBulk field‖ ^ 2 ≤
      (inner ℂ (highDiskBulk field) (diskB (highDiskBulk field))).re :=
  diskB_coercive _ (highDiskBulk_spectral field)

end Grad.CircularHighWeak
