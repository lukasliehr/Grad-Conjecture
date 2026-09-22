import ANH7HighOrbits

noncomputable section

set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators

namespace Grad.CircularHighWeak

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.PhysicalFamily Grad.NonlinearRange

theorem diskCompact : IsCompact (closedUnitDisk : Set SpatialPlane) := by
  rw [closedUnitDisk_eq_closedBall]
  exact isCompact_closedBall _ _

theorem closedValue_norm_sq_integral {dimension : ℕ}
    (field : C(ClosedDisk, ComplexEuclidean dimension))
    (extension : SpatialPlane → ComplexEuclidean dimension)
    (agrees : ∀ point : ClosedDisk, extension point.val = field point) :
    ‖closedContinuousToDiskL2 field‖ ^ 2 =
      ∫ point in closedUnitDisk, ‖extension point‖ ^ 2 := by
  rw [closedContinuousToDiskL2_norm_sq,
    ← Measure.restrict_congr_set closedUnitDisk_ae_openUnitDisk]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem diskCompact.measurableSet] with point inside
  rw [closedDiskLift, dif_pos inside, agrees ⟨point, inside⟩]

def globalOrbitEnergy {dimension : ℕ} (field : ClosedJet dimension) (argument : SpatialPlane × ℝ) : ℝ :=
  ‖smoothClosedExtension field (planeRotationAction argument.2 argument.1)‖ ^ 2

theorem globalOrbitEnergy_continuous {dimension : ℕ} (field : ClosedJet dimension) :
    Continuous (globalOrbitEnergy field) :=
  (((smoothClosedExtension_smooth field).continuous.comp
    (physicalRotation_contDiff.continuous.comp continuous_swap)).norm.pow 2)

theorem globalOrbitEnergy_closed {dimension : ℕ} (field : ClosedJet dimension)
    (point : ClosedDisk) (angle : ℝ) :
    globalOrbitEnergy field (point.val, angle) = ‖field.value (rotatedPoint angle point)‖ ^ 2 := by
  unfold globalOrbitEnergy
  have equality := smoothClosedExtension_value field (rotatedPoint angle point)
  have rotation : (rotatedPoint angle point).val = planeRotationAction angle point.val := by
    rw [physicalRotation_eq_orthogonal]
    rfl
  rw [← rotation, equality]

theorem globalOrbitEnergy_disk_integral {dimension : ℕ} (field : ClosedJet dimension) (angle : ℝ) :
    (∫ point in closedUnitDisk, globalOrbitEnergy field (point, angle)) =
      ‖closedContinuousToDiskL2 field.value‖ ^ 2 := by
  have normLaw := closedValue_norm_sq_integral
    (field.value.comp (orthogonalClosedMap (planeRotationEquiv angle)))
    (fun point => smoothClosedExtension field (planeRotationAction angle point)) (by
      intro point
      have equality := smoothClosedExtension_value field (rotatedPoint angle point)
      have rotation : (rotatedPoint angle point).val = planeRotationAction angle point.val := by
        rw [physicalRotation_eq_orthogonal]
        rfl
      rw [← rotation]
      exact equality)
  rw [closedValueL2_orthogonal_norm] at normLaw
  exact normLaw.symm

theorem globalOrbitEnergy_disk_average {dimension : ℕ} (field : ClosedJet dimension) :
    (∫ point in closedUnitDisk,
      ∫ angle in -Real.pi..Real.pi, globalOrbitEnergy field (point, angle)) =
        (2 * Real.pi) * ‖closedContinuousToDiskL2 field.value‖ ^ 2 := by
  have joint : Integrable (globalOrbitEnergy field)
      ((volume.restrict closedUnitDisk).prod (volume.restrict (Icc (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict]
    exact (globalOrbitEnergy_continuous field).continuousOn.integrableOn_compact
      (diskCompact.prod isCompact_Icc)
  have swap := integral_integral_swap (f := fun point angle => globalOrbitEnergy field (point, angle)) joint
  have inner (point : SpatialPlane) :
      (∫ angle in -Real.pi..Real.pi, globalOrbitEnergy field (point, angle)) =
        ∫ angle in Icc (-Real.pi) Real.pi, globalOrbitEnergy field (point, angle) := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Icc_eq_integral_Ioc]
  simp_rw [inner]
  rw [swap]
  simp_rw [globalOrbitEnergy_disk_integral]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos]),
    intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  congr 1
  ring

theorem globalOrbitEnergy_angle_integrable {dimension : ℕ} (field : ClosedJet dimension) :
    IntegrableOn (fun point => ∫ angle in -Real.pi..Real.pi, globalOrbitEnergy field (point, angle))
      closedUnitDisk := by
  have continuous : Continuous (fun point : SpatialPlane =>
      ∫ angle in Icc (-Real.pi) Real.pi, globalOrbitEnergy field (point, angle)) :=
    continuous_parametric_integral_of_continuous
      (f := fun point angle => globalOrbitEnergy field (point, angle))
      (globalOrbitEnergy_continuous field) isCompact_Icc
  have equality : (fun point : SpatialPlane => ∫ angle in -Real.pi..Real.pi,
      globalOrbitEnergy field (point, angle)) =
      fun point => ∫ angle in Icc (-Real.pi) Real.pi, globalOrbitEnergy field (point, angle) := by
    funext point
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Icc_eq_integral_Ioc]
  rw [equality]
  exact continuous.continuousOn.integrableOn_compact diskCompact

theorem highCore_rotation_poincare {dimension : ℕ} (field : ClosedJet dimension) :
    9 * ‖closedContinuousToDiskL2 (excludedAngularJet lowAngularModes field).value‖ ^ 2 ≤
      ‖closedContinuousToDiskL2 (rotationJet (excludedAngularJet lowAngularModes field)).value‖ ^ 2 := by
  let high := excludedAngularJet lowAngularModes field
  have pointwise (point : SpatialPlane) (inside : point ∈ closedUnitDisk) :
      9 * (∫ angle in -Real.pi..Real.pi, globalOrbitEnergy high (point, angle)) ≤
        ∫ angle in -Real.pi..Real.pi, globalOrbitEnergy (rotationJet high) (point, angle) := by
    have bound := highCore_orbit_poincare field ⟨point, inside⟩
    have first (angle : ℝ) := globalOrbitEnergy_closed high ⟨point, inside⟩ angle
    have second (angle : ℝ) := globalOrbitEnergy_closed (rotationJet high) ⟨point, inside⟩ angle
    simp_rw [first, second]
    exact bound
  have integrated := integral_mono_ae
    ((globalOrbitEnergy_angle_integrable high).const_mul 9)
    (globalOrbitEnergy_angle_integrable (rotationJet high)) (by
      filter_upwards [ae_restrict_mem diskCompact.measurableSet] with point inside
      exact pointwise point inside)
  rw [integral_const_mul, globalOrbitEnergy_disk_average, globalOrbitEnergy_disk_average] at integrated
  apply le_of_mul_le_mul_left (a := 2 * Real.pi) _ (by positivity : 0 < 2 * Real.pi)
  nlinarith [integrated]

end Grad.CircularHighWeak
