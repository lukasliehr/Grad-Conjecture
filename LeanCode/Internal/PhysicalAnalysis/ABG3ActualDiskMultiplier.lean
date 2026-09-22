import ABG2MultiplierSeries

noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators
namespace Grad.OrdinaryDiskMultiplier
open Grad.CartesianState Grad.CircularHighWeak Grad.Constraints

theorem diskMode_opNorm (mode : ℤ) : ‖diskMode mode‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun field => by
    rw [one_mul]
    exact (lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) (diskFourier field) mode).trans_eq
      (diskFourier_norm field))

theorem correctedDisk_coefficient (mode : ℤ) (field : DiskL2 1) :
    diskMode mode (correctedOperator diskMode field) =
      (highMultiplier mode : ℂ) • diskMode mode field := by
  rw [correctedOperator_apply diskMode 1 diskMode_opNorm, map_sub,
    (diskMode mode).map_tsum (correctionValue_summable diskMode 1 diskMode_opNorm field)]
  have series : (∑' other : ℤ, diskMode mode ((correctionCoefficient other : ℂ) • diskMode other field)) =
      (correctionCoefficient mode : ℂ) • diskMode mode field := by
    have term (other : ℤ) : diskMode mode ((correctionCoefficient other : ℂ) • diskMode other field) =
        if other = mode then (correctionCoefficient other : ℂ) • diskMode mode field else 0 := by
      rw [map_smul, diskMode_projection]
      by_cases same : other = mode
      · subst other
        simp
      · simp [same, Ne.symm same]
    simp_rw [term]
    exact tsum_ite_eq mode _
  rw [series]
  have coefficient : (1 : ℂ) - (correctionCoefficient mode : ℂ) = (highMultiplier mode : ℂ) := by
    exact_mod_cast correctionCoefficient_literal mode
  calc
    _ = ((1 : ℂ) - (correctionCoefficient mode : ℂ)) • diskMode mode field := by rw [sub_smul, one_smul]
    _ = _ := by rw [coefficient]

theorem correctedDisk_actual (field : DiskL2 1) : correctedOperator diskMode field = diskB field := by
  apply diskFourierIsometry.injective
  apply lp.ext
  funext mode
  exact (correctedDisk_coefficient mode field).trans (diskB_coefficient mode field).symm

end Grad.OrdinaryDiskMultiplier
