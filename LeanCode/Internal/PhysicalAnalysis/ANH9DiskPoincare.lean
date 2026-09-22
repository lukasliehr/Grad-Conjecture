import ANH8DiskOrbitIntegral

noncomputable section

set_option maxHeartbeats 1000000

open Set MeasureTheory
open scoped BigOperators

namespace Grad.CircularHighWeak

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.PhysicalFamily Grad.NonlinearRange Grad.NonlinearQuotientBounds

theorem rotationJet_pointwise_bound {dimension : ℕ} (field : ClosedJet dimension) (point : ClosedDisk) :
    ‖(rotationJet field).value point‖ ^ 2 ≤
      ‖(partialJet 0 field).value point‖ ^ 2 + ‖(partialJet 1 field).value point‖ ^ 2 := by
  have literal : (rotationJet field).value point =
      point.val 0 • (partialJet 1 field).value point -
        point.val 1 • (partialJet 0 field).value point := by
    change (coordinateJet 0 (partialJet 1 field) - coordinateJet 1 (partialJet 0 field)).value point = _
    rw [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
      ContinuousMap.add_apply, ContinuousMap.neg_apply, coordinateJet_value, coordinateJet_value]
    rfl
  have triangle := norm_sub_le (point.val 0 • (partialJet 1 field).value point)
    (point.val 1 • (partialJet 0 field).value point)
  rw [← literal, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs] at triangle
  have radius : (point.val 0) ^ 2 + (point.val 1) ^ 2 ≤ 1 := by
    have sq := pow_le_pow_left₀ (norm_nonneg point.val) point.property 2
    rw [PiLp.norm_sq_eq_of_L2] at sq
    simpa only [Fin.sum_univ_two, Real.norm_eq_abs, sq_abs, one_pow] using sq
  have cauchy := sq_nonneg (|point.val 0| * ‖(partialJet 0 field).value point‖ -
    |point.val 1| * ‖(partialJet 1 field).value point‖)
  have bounded := mul_le_mul_of_nonneg_right radius
    (show 0 ≤ ‖(partialJet 0 field).value point‖ ^ 2 +
      ‖(partialJet 1 field).value point‖ ^ 2 by positivity)
  have squareTriangle := pow_le_pow_left₀ (norm_nonneg _) triangle 2
  nlinarith [sq_abs (point.val 0), sq_abs (point.val 1)]

theorem rotationJet_L2_bound {dimension : ℕ} (field : ClosedJet dimension) :
    ‖closedContinuousToDiskL2 (rotationJet field).value‖ ^ 2 ≤
      ‖closedContinuousToDiskL2 (partialJet 0 field).value‖ ^ 2 +
        ‖closedContinuousToDiskL2 (partialJet 1 field).value‖ ^ 2 := by
  have valueNorm (source : ClosedJet dimension) := closedValue_norm_sq_integral source.value
    (smoothClosedExtension source) (smoothClosedExtension_value source)
  rw [valueNorm, valueNorm, valueNorm, ← integral_add]
  · apply integral_mono_ae
    · exact ((smoothClosedExtension_smooth _).continuous.norm.pow 2).continuousOn.integrableOn_compact diskCompact
    · exact (((smoothClosedExtension_smooth _).continuous.norm.pow 2).add
        ((smoothClosedExtension_smooth _).continuous.norm.pow 2)).continuousOn.integrableOn_compact diskCompact
    · filter_upwards [ae_restrict_mem diskCompact.measurableSet] with point inside
      rw [smoothClosedExtension_value _ ⟨point, inside⟩,
        smoothClosedExtension_value _ ⟨point, inside⟩,
        smoothClosedExtension_value _ ⟨point, inside⟩]
      exact rotationJet_pointwise_bound field ⟨point, inside⟩
  · exact ((smoothClosedExtension_smooth _).continuous.norm.pow 2).continuousOn.integrableOn_compact diskCompact
  · exact ((smoothClosedExtension_smooth _).continuous.norm.pow 2).continuousOn.integrableOn_compact diskCompact

theorem partialJet_zero_value {dimension : ℕ} (field : ClosedJet dimension) :
    (partialJet 0 field).value = closedMultiDerivative field (1, 0) := by
  change closedDerivative field 1 (fun _ => 0) = _
  unfold closedMultiDerivative
  congr 1
  funext position
  fin_cases position
  rfl

theorem partialJet_one_value {dimension : ℕ} (field : ClosedJet dimension) :
    (partialJet 1 field).value = closedMultiDerivative field (0, 1) := by
  change closedDerivative field 1 (fun _ => 1) = _
  unfold closedMultiDerivative
  congr 1

theorem highCore_disk_poincare (field : ClosedJet 1) :
    9 * ‖closedContinuousToDiskL2 (excludedAngularJet lowAngularModes field).value‖ ^ 2 ≤
      ‖closedDerivativeL2 (1, 0) (excludedAngularJet lowAngularModes field)‖ ^ 2 +
        ‖closedDerivativeL2 (0, 1) (excludedAngularJet lowAngularModes field)‖ ^ 2 := by
  have bounded := (highCore_rotation_poincare field).trans
    (rotationJet_L2_bound (excludedAngularJet lowAngularModes field))
  rw [partialJet_zero_value, partialJet_one_value] at bounded
  exact bounded

/-- The exact full-disk high Poincaré estimate in the faithful H1 completion. -/
theorem highDisk_poincare (field : highDiskGrade) :
    9 * ‖highDiskBulk field‖ ^ 2 ≤
      ‖diskGradX field.val‖ ^ 2 + ‖diskGradY field.val‖ ^ 2 := by
  apply isClosed_property highDiskCoreInto_denseRange
    (isClosed_le (continuous_const.mul (highDiskBulk.continuous.norm.pow 2))
      (((diskGradX.continuous.comp highDiskGrade.subtypeL.continuous).norm.pow 2).add
        ((diskGradY.continuous.comp highDiskGrade.subtypeL.continuous).norm.pow 2))) _ field
  intro core
  have bulk : highDiskBulk (highDiskCoreInto core) =
      closedContinuousToDiskL2 (excludedAngularJet lowAngularModes core).value := by
    change diskCoordinate (zeroGradeIndex 1)
      (diskCoreInto (excludedAngularJet lowAngularModes core)) = _
    rw [diskCoordinate_core]
    change closedContinuousToDiskL2 (closedMultiDerivative _ (0, 0)) = _
    rw [closedMultiDerivative_zero]
  have x := diskGradX_core (excludedAngularJet lowAngularModes core)
  have y := diskGradY_core (excludedAngularJet lowAngularModes core)
  change 9 * ‖highDiskBulk (highDiskCoreInto core)‖ ^ 2 ≤
    ‖diskGradX (diskCoreInto (excludedAngularJet lowAngularModes core))‖ ^ 2 +
    ‖diskGradY (diskCoreInto (excludedAngularJet lowAngularModes core))‖ ^ 2
  exact (congrArg (fun value : DiskL2 1 => 9 * ‖value‖ ^ 2) bulk).le.trans
    ((highCore_disk_poincare core).trans_eq
      (congrArg₂ (fun first second : ℝ => first + second)
        (congrArg (fun value : DiskL2 1 => ‖value‖ ^ 2) x.symm)
        (congrArg (fun value : DiskL2 1 => ‖value‖ ^ 2) y.symm)))

end Grad.CircularHighWeak
