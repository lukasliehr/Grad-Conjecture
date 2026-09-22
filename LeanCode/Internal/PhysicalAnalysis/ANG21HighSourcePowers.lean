import ANG20CompletedSourcePowers

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open scoped BigOperators
namespace Grad.CircularHighWeak
open Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem highL2Projection_coefficient (mode : ℤ) (field : DiskL2 1) :
    diskMode mode (highL2Projection field) = if mode ∈ lowAngularModes then 0 else diskMode mode field := by
  rw [highL2Projection_apply, map_sub, map_sum]
  simp_rw [diskMode_projection]
  simp
  split_ifs <;> simp_all

theorem highL2Projection_contract (field : DiskL2 1) : ‖highL2Projection field‖ ≤ ‖field‖ := by
  have bound : ‖diskFourier (highL2Projection field)‖ ≤ ‖diskFourier field‖ := by
    apply lp.norm_mono (by norm_num)
    intro mode
    change ‖diskMode mode (highL2Projection field)‖ ≤ ‖diskMode mode field‖
    rw [highL2Projection_coefficient]
    split_ifs
    · exact (norm_zero.le).trans (norm_nonneg (diskMode mode field))
    · exact le_refl _
  exact (diskFourier_norm (highL2Projection field)).symm.le.trans (bound.trans_eq (diskFourier_norm field))

def sourceHighBulk (grade : ℕ) : apGrade 1 0 0 1 1 grade →L[ℂ] highDiskL2 :=
  highL2ProjectionInto.comp (sourceBulk grade)

def sourceHighPower (order : ℕ) : apGrade 1 0 0 1 1 order →L[ℂ] highDiskL2 :=
  highL2ProjectionInto.comp (sourceRotationPower order)

theorem sourceHighPower_bound (order : ℕ) (field : apGrade 1 0 0 1 1 order) :
    ‖sourceHighPower order field‖ ≤ unitRotationPowerConstant order * ‖field‖ :=
  (highL2Projection_contract (sourceRotationPower order field)).trans (sourceRotationPower_bound order field)

theorem sourceHighPower_coefficient (order : ℕ) (mode : ℤ) (field : apGrade 1 0 0 1 1 order) :
    diskMode mode (sourceHighPower order field).val =
      (Complex.I * (mode : ℂ)) ^ order • diskMode mode (sourceHighBulk order field).val := by
  have left := highL2Projection_coefficient mode (sourceRotationPower order field)
  have right := highL2Projection_coefficient mode (sourceBulk order field)
  change diskMode mode (sourceHighPower order field).val = _ at left
  change diskMode mode (sourceHighBulk order field).val = _ at right
  refine left.trans ?_
  by_cases low : mode ∈ lowAngularModes
  · exact (if_pos low).trans ((smul_zero ((Complex.I * (mode : ℂ)) ^ order)).symm.trans
      (congrArg (fun value : DiskL2 1 => (Complex.I * (mode : ℂ)) ^ order • value) (right.trans (if_pos low)).symm))
  · exact (if_neg low).trans ((sourceRotationPower_coefficient order mode field).trans
      (congrArg (fun value : DiskL2 1 => (Complex.I * (mode : ℂ)) ^ order • value) (right.trans (if_neg low)).symm))

end Grad.CircularHighWeak
