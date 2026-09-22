import GC18CartesianContinuity

noncomputable section

set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Radial

def cMapAngularLinear (dimension : ℕ) (mode : ℤ) :
    C(ClosedDisk, ComplexEuclidean dimension) →ₗ[ℂ] C(ClosedDisk, ComplexEuclidean dimension) where
  toFun field := ⟨closedCharacterProjection mode field, closedCharacterProjection_continuous mode field field.continuous⟩
  map_add' first second := by
    apply ContinuousMap.ext
    intro point
    change closedCharacterProjection mode (fun other => first other + second other) point =
      closedCharacterProjection mode first point + closedCharacterProjection mode second point
    simp_rw [closedCharacterProjection_integral, smul_add]
    rw [intervalIntegral.integral_add
      ((closedCharacterIntegrand_continuous mode first first.continuous point).intervalIntegrable _ _)
      ((closedCharacterIntegrand_continuous mode second second.continuous point).intervalIntegrable _ _), smul_add]
  map_smul' scalar field := by
    apply ContinuousMap.ext
    intro point
    change closedCharacterProjection mode (fun other => scalar • field other) point =
      scalar • closedCharacterProjection mode field point
    simp_rw [closedCharacterProjection_integral, smul_comm (angularCharacter mode _) scalar]
    rw [intervalIntegral.integral_smul]
    exact smul_comm _ _ _

theorem cMapAngular_bound (dimension : ℕ) (mode : ℤ) (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    ‖cMapAngularLinear dimension mode field‖ ≤ ‖field‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro point
  change ‖closedCharacterProjection mode field point‖ ≤ _
  rw [closedCharacterProjection_integral, norm_smul, Real.norm_of_nonneg (by positivity)]
  have bound : ‖∫ angle in (0 : ℝ)..2 * Real.pi,
      angularCharacter mode angle • field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)‖ ≤
      ‖field‖ * (2 * Real.pi) := by
    have estimate := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 2 * Real.pi)
      (f := fun angle => angularCharacter mode angle • field (Grad.GaugeCoefficients.Radial.rotatedPoint angle point))
      (fun angle _ => by rw [norm_smul, angularCharacter_norm, one_mul]; exact ContinuousMap.norm_coe_le_norm field _)
    simpa only [sub_zero, abs_of_pos (by positivity : 0 < 2 * Real.pi)] using estimate
  calc
    _ ≤ (2 * Real.pi)⁻¹ * (‖field‖ * (2 * Real.pi)) := mul_le_mul_of_nonneg_left bound (by positivity)
    _ = ‖field‖ := by field_simp

def cMapAngular (dimension : ℕ) (mode : ℤ) :
    C(ClosedDisk, ComplexEuclidean dimension) →L[ℂ] C(ClosedDisk, ComplexEuclidean dimension) :=
  (cMapAngularLinear dimension mode).mkContinuous 1 (fun field => by simpa only [one_mul] using cMapAngular_bound dimension mode field)

theorem cMapAngular_apply {dimension : ℕ} (mode : ℤ) (field : C(ClosedDisk, ComplexEuclidean dimension)) (point : ClosedDisk) :
    cMapAngular dimension mode field point = closedCharacterProjection mode field point := rfl

end Grad.GaugeCoefficients.Physical.RadialLedger
