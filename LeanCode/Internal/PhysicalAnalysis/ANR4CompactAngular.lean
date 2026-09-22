import ANR2AngularLaplacian

noncomputable section
set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped ContDiff BigOperators

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.PhysicalFamily

private def angularSupportSet {dimension : ℕ} (field : SpatialPlane → ComplexEuclidean dimension) :
    Set SpatialPlane :=
  (fun argument : ℝ × SpatialPlane => planeRotationAction argument.1 argument.2) ''
    (Icc (-2 * Real.pi) (0 : ℝ) ×ˢ tsupport field)

private theorem angularSupportSet_compact {dimension : ℕ}
    (field : SpatialPlane → ComplexEuclidean dimension) (compact : HasCompactSupport field) :
    IsCompact (angularSupportSet field) := by
  exact (isCompact_Icc.prod compact).image physicalRotation_contDiff.continuous

private theorem angularSupportSet_inside {dimension : ℕ}
    (field : SpatialPlane → ComplexEuclidean dimension) (supported : tsupport field ⊆ openUnitDisk) :
    angularSupportSet field ⊆ openUnitDisk := by
  rintro point ⟨⟨angle, source⟩, member, rfl⟩
  change ‖planeRotationAction angle source‖ < 1
  rw [physicalRotation_norm]
  exact supported member.2

private theorem angularProjection_support {dimension : ℕ} (mode : ℤ)
    (field : SpatialPlane → ComplexEuclidean dimension) (compact : HasCompactSupport field) :
    tsupport (angularProjectionValue mode field) ⊆ angularSupportSet field := by
  apply closure_minimal _ (angularSupportSet_compact field compact).isClosed
  intro point nonzero
  by_contra outside
  have zero (angle : ℝ) (member : angle ∈ Icc (0 : ℝ) (2 * Real.pi)) :
      field (planeRotationAction angle point) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
    intro sourceMember
    apply outside
    refine ⟨(-angle, planeRotationAction angle point), ⟨⟨by linarith [member.2], by linarith [member.1]⟩, sourceMember⟩, ?_⟩
    dsimp only
    rw [physicalRotation_add, neg_add_cancel, physicalRotation_eq_orthogonal]
    ext coordinate
    fin_cases coordinate <;> simp [Grad.GaugeCoefficients.Radial.planeRotationEquiv_apply,
      Grad.GaugeCoefficients.Radial.planeRotation]
  apply nonzero
  rw [angularProjectionValue_eq_compactIntegral]
  have integralZero : (∫ angle in Icc (0 : ℝ) (2 * Real.pi),
      angularCharacter mode angle • field (planeRotationAction angle point)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro angle member
    rw [zero angle member, smul_zero]
  rw [integralZero, smul_zero]

theorem angularProjection_compact_inside {dimension : ℕ} (mode : ℤ)
    (field : SpatialPlane → ComplexEuclidean dimension) (compact : HasCompactSupport field)
    (supported : tsupport field ⊆ openUnitDisk) :
    HasCompactSupport (angularProjectionValue mode field) ∧
      tsupport (angularProjectionValue mode field) ⊆ openUnitDisk :=
  ⟨(angularSupportSet_compact field compact).of_isClosed_subset (isClosed_tsupport _)
      (angularProjection_support mode field compact),
    (angularProjection_support mode field compact).trans (angularSupportSet_inside field supported)⟩

theorem globalClosedJet_angular {dimension : ℕ} (mode : ℤ)
    (field : SpatialPlane → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field) :
    globalClosedJet (angularProjectionValue mode field) (angularProjectionValue_smooth mode smooth) =
      angularClosedJet mode (globalClosedJet field smooth) := by
  apply globalClosedJet_eq_of_restriction
  intro point
  rw [angularClosedJet_value, angularProjectionValue]
  congr 1
  apply intervalIntegral.integral_congr
  intro angle _
  dsimp only
  rw [globalClosedJet_value]
  congr 1
  exact congrArg field (physicalRotation_eq_orthogonal angle point.val)

end Grad.CircularHighRegularity
