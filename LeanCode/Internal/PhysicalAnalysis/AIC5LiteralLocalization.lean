import AIC4WeakInverseLocalization

noncomputable section
open MeasureTheory Classical
open scoped BigOperators ContDiff

namespace Grad.InteriorLocalization
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.WeightedJets Grad.WeightedJets.ZeroExtension Grad.CircularHighWeak

/-- The global weak H1 field really is chi times the actual solution on
the original disk, zero outside, and has only the auxiliary cell zero. -/
private theorem cutoff_extension_literal (field : DiskL2 1) :
    ∀ᵐ point ∂volume, ∀ cell : ℤ,
      fieldExtension (CellValues 1) openUnitDisk openUnitDisk_isOpen.measurableSet
        (SpatialMultiplier.fieldMultiplier 1 openUnitDisk openUnitDisk_isOpen
          (SpatialMultiplier.derivativeScalar
            (SpatialMultiplier.compactSymbol 1 openUnitDisk interiorCutoff.toFun
              interiorCutoff.smooth interiorCutoff.compact) (zeroIndex 1))
          (apDiskInjection 1 field)) point cell =
        if point ∈ openUnitDisk ∧ cell = 0 then
          (interiorCutoff.toFun point : ℂ) • field point
        else 0 := by
  classical
  let symbol := SpatialMultiplier.compactSymbol 1 openUnitDisk interiorCutoff.toFun
    interiorCutoff.smooth interiorCutoff.compact
  let multiplied := SpatialMultiplier.fieldMultiplier 1 openUnitDisk openUnitDisk_isOpen
    (SpatialMultiplier.derivativeScalar symbol (zeroIndex 1)) (apDiskInjection 1 field)
  have localRepresentation : ∀ᵐ point ∂volume, point ∈ openUnitDisk →
      ∀ cell : ℤ, multiplied point cell =
        (interiorCutoff.toFun point : ℂ) • (cellSingle (PhysicalValue 1) 0 (field point)) cell := by
    apply (ae_restrict_iff' openUnitDisk_isOpen.measurableSet).mp
    filter_upwards [SpatialMultiplier.fieldMultiplier_ae 1 openUnitDisk openUnitDisk_isOpen
      (SpatialMultiplier.derivativeScalar symbol (zeroIndex 1)) (apDiskInjection 1 field),
      apDiskInjection_ae field] with point multiplication injection
    intro cell
    exact (multiplication cell).trans (congrArg (fun value : CellValues 1 =>
      (interiorCutoff.toFun point : ℂ) • value cell) injection)
  have extension := fieldExtension_ae (CellValues 1) openUnitDisk openUnitDisk_isOpen.measurableSet multiplied
  filter_upwards [extension, localRepresentation] with point extensionAt localAt
  intro cell
  change fieldExtension (CellValues 1) openUnitDisk openUnitDisk_isOpen.measurableSet multiplied point cell = _
  rw [extensionAt]
  by_cases inside : point ∈ openUnitDisk
  · rw [Set.indicator_of_mem inside, localAt inside cell]
    by_cases zero : cell = 0
    · subst cell
      simp only [cellSingle_apply, inside, and_self, if_true]
    · simp only [cellSingle_apply, smul_zero, zero, and_false, if_false]
  · simp [inside]

theorem localizedWeakInverse_literal (parameter : ℝ) (source : highDiskL2) :
    ∀ᵐ point ∂volume, ∀ cell : ℤ,
      base 1 1 Set.univ (fun _ => 0) (localizedWeakInverse parameter source) point cell =
        if point ∈ openUnitDisk ∧ cell = 0 then
          (interiorCutoff.toFun point : ℂ) • highDiskBulk (highRobinWeakInverse parameter source) point
        else 0 := by
  filter_upwards [cutoff_extension_literal (highDiskBulk (highRobinWeakInverse parameter source))]
    with point represented
  intro cell
  exact (congrArg (fun global : FieldL2 1 Set.univ => global point cell)
    (localizedWeakInverse_base parameter source)).trans (represented cell)

theorem localizedWeakInverse_inner_disk (parameter : ℝ) (source : highDiskL2) :
    ∀ᵐ point ∂volume.restrict (Metric.ball (0 : Grad.PDEBootstrap.Spatial) (1 / 2)),
      base 1 1 Set.univ (fun _ => 0) (localizedWeakInverse parameter source) point 0 =
        highDiskBulk (highRobinWeakInverse parameter source) point := by
  filter_upwards [ae_restrict_of_ae (localizedWeakInverse_literal parameter source),
    ae_restrict_mem Metric.isOpen_ball.measurableSet] with point literal member
  have bound : ‖point‖ < (1 / 2 : ℝ) := by simpa only [Metric.mem_ball, dist_zero_right] using member
  have inside : point ∈ openUnitDisk := by change ‖point‖ < 1; linarith
  have one : interiorCutoff.toFun point = 1 :=
    interiorCutoff_one (show point ∈ Metric.closedBall (0 : Grad.PDEBootstrap.Spatial) (7 / 12) by
      simp only [Metric.mem_closedBall, dist_zero_right]; linarith)
  simpa only [inside, and_self, if_true, one, Complex.ofReal_one, one_smul] using literal 0

end Grad.InteriorLocalization
