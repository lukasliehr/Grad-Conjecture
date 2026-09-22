import ANH9DiskPoincare

noncomputable section

set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators

namespace Grad.CircularHighWeak

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.PhysicalFamily Grad.NonlinearRange

def diskModeEnergy {dimension : ℕ} (field : ClosedJet dimension) (mode : ℤ) (point : SpatialPlane) : ℝ :=
  ‖smoothClosedExtension (angularClosedJet mode field) point‖ ^ 2

theorem diskModeEnergy_integrable {dimension : ℕ} (field : ClosedJet dimension) (mode : ℤ) :
    IntegrableOn (diskModeEnergy field mode) closedUnitDisk :=
  ((smoothClosedExtension_smooth _).continuous.norm.pow 2).continuousOn.integrableOn_compact diskCompact

theorem diskModeEnergy_integral {dimension : ℕ} (field : ClosedJet dimension) (mode : ℤ) :
    (∫ point in closedUnitDisk, diskModeEnergy field mode point) =
      ‖closedContinuousToDiskL2 (angularClosedJet mode field).value‖ ^ 2 :=
  (closedValue_norm_sq_integral _ _ (smoothClosedExtension_value _)).symm

theorem diskModeEnergy_closed {dimension : ℕ} (field : ClosedJet dimension) (mode : ℤ) (point : ClosedDisk) :
    diskModeEnergy field mode point.val =
      ‖angularCoefficient (fun angle => field.value (rotatedPoint angle point)) mode‖ ^ 2 := by
  rw [diskModeEnergy, smoothClosedExtension_value, orbitCoefficient_projection]

theorem diskMode_finite_bound {dimension : ℕ} (field : ClosedJet dimension) (modes : Finset ℤ) :
    (∑ mode ∈ modes, ‖closedContinuousToDiskL2 (angularClosedJet mode field).value‖ ^ 2) ≤
      ‖closedContinuousToDiskL2 field.value‖ ^ 2 := by
  have pointwise (point : SpatialPlane) (inside : point ∈ closedUnitDisk) :
      (∑ mode ∈ modes, diskModeEnergy field mode point) ≤
        (2 * Real.pi)⁻¹ * ∫ angle in -Real.pi..Real.pi, globalOrbitEnergy field (point, angle) := by
    have coefficients (mode : ℤ) := diskModeEnergy_closed field mode ⟨point, inside⟩
    have energy (angle : ℝ) := globalOrbitEnergy_closed field ⟨point, inside⟩ angle
    simp_rw [coefficients, energy]
    exact angular_bessel_finite _ (orbitValue_continuous field ⟨point, inside⟩) modes
  have bound := integral_mono_ae
    (integrable_finsetSum modes (fun mode _ => diskModeEnergy_integrable field mode))
    ((globalOrbitEnergy_angle_integrable field).const_mul ((2 * Real.pi)⁻¹)) (by
      filter_upwards [ae_restrict_mem diskCompact.measurableSet] with point inside
      exact pointwise point inside)
  rw [integral_finsetSum, integral_const_mul, globalOrbitEnergy_disk_average] at bound
  · simp_rw [diskModeEnergy_integral] at bound
    rw [← mul_assoc, inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_mul] at bound
    exact bound
  · intro mode _
    exact diskModeEnergy_integrable field mode

theorem diskMode_summable_sq {dimension : ℕ} (field : ClosedJet dimension) :
    Summable (fun mode : ℤ => ‖closedContinuousToDiskL2 (angularClosedJet mode field).value‖ ^ 2) :=
  summable_of_sum_le (fun _ => sq_nonneg _) (diskMode_finite_bound field)

theorem diskMode_parseval {dimension : ℕ} (field : ClosedJet dimension) :
    (∑' mode : ℤ, ‖closedContinuousToDiskL2 (angularClosedJet mode field).value‖ ^ 2) =
      ‖closedContinuousToDiskL2 field.value‖ ^ 2 := by
  have norms : Summable (fun mode : ℤ => ∫ point in closedUnitDisk, ‖diskModeEnergy field mode point‖) := by
    have equal (mode : ℤ) : (∫ point in closedUnitDisk, ‖diskModeEnergy field mode point‖) =
        ‖closedContinuousToDiskL2 (angularClosedJet mode field).value‖ ^ 2 := by
      rw [← diskModeEnergy_integral]
      apply integral_congr_ae
      filter_upwards [] with point
      exact Real.norm_of_nonneg (sq_nonneg _)
    simp_rw [equal]
    exact diskMode_summable_sq field
  have exchange := integral_tsum_of_summable_integral_norm (diskModeEnergy_integrable field) norms
  have pointwise (point : SpatialPlane) (inside : point ∈ closedUnitDisk) :
      (∑' mode : ℤ, diskModeEnergy field mode point) =
        (2 * Real.pi)⁻¹ * ∫ angle in -Real.pi..Real.pi, globalOrbitEnergy field (point, angle) := by
    have coefficients (mode : ℤ) := diskModeEnergy_closed field mode ⟨point, inside⟩
    have energy (angle : ℝ) := globalOrbitEnergy_closed field ⟨point, inside⟩ angle
    simp_rw [coefficients, energy]
    exact (angular_hasSum_sq _ (orbitValue_continuous field ⟨point, inside⟩)).tsum_eq
  have integrated : (∫ point in closedUnitDisk, ∑' mode : ℤ, diskModeEnergy field mode point) =
      ∫ point in closedUnitDisk,
        (2 * Real.pi)⁻¹ * ∫ angle in -Real.pi..Real.pi, globalOrbitEnergy field (point, angle) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem diskCompact.measurableSet] with point inside
    exact pointwise point inside
  rw [integral_const_mul, globalOrbitEnergy_disk_average,
    ← mul_assoc, inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_mul] at integrated
  simp_rw [diskModeEnergy_integral] at exchange
  exact exchange.trans integrated

end Grad.CircularHighWeak
