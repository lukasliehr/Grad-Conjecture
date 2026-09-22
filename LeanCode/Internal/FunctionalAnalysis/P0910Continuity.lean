import P0910Geometry

noncomputable section

open Filter Set
open scoped BigOperators ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets
open Grad.DiskExtension.Seeley

local instance continuityClosedDiskCompactSpace : CompactSpace ClosedDisk := by
  rw [← isCompact_iff_compactSpace, closedUnitDisk_eq_closedBall]
  exact isCompact_closedBall (0 : SpatialPlane) 1

def radialRetraction (point : SpatialPlane) : ClosedDisk :=
  ⟨(max 1 ‖point‖)⁻¹ • point, by
    change ‖(max 1 ‖point‖)⁻¹ • point‖ ≤ 1
    by_cases inside : ‖point‖ ≤ 1
    · rw [max_eq_left inside, inv_one, one_smul]
      exact inside
    · have outside : 1 < ‖point‖ := lt_of_not_ge inside
      rw [max_eq_right outside.le, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr (lt_trans zero_lt_one outside)),
        inv_mul_cancel₀ (ne_of_gt (lt_trans zero_lt_one outside))]⟩

theorem radialRetraction_val_of_mem (point : SpatialPlane)
    (membership : point ∈ closedUnitDisk) :
    (radialRetraction point).val = point := by
  change (max 1 ‖point‖)⁻¹ • point = point
  have bound : ‖point‖ ≤ 1 := membership
  rw [max_eq_left bound, inv_one, one_smul]

theorem continuous_radialRetraction : Continuous radialRetraction := by
  refine Continuous.subtype_mk ?_ _
  have denominatorContinuous : Continuous
      (fun point : SpatialPlane => max 1 ‖point‖) :=
    continuous_const.max continuous_norm
  have denominatorPositive : ∀ point : SpatialPlane, 0 < max 1 ‖point‖ :=
    fun point => lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  exact (denominatorContinuous.inv₀ fun point => ne_of_gt (denominatorPositive point)).smul
    continuous_id

def retractedReflectedDiskCell (index : ℕ) (point : SpatialCell) : DiskCellDomain :=
  (radialRetraction (reflectedPoint index (planarPart point)), (point 2 : CellCircle))

theorem retractedReflectedDiskCell_continuousAt (index : ℕ) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    ContinuousAt (retractedReflectedDiskCell index) point := by
  have reflectedSmooth := reflectedSpatialCell_contDiffAt index point nonzero
  have reflectedContinuous : ContinuousAt
      (fun candidate : SpatialCell => reflectedPoint index (planarPart candidate)) point := by
    have := continuous_planarPart.continuousAt.comp reflectedSmooth.continuousAt
    apply this.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun candidate =>
      (reflectedSpatialCell_planarPart index candidate).symm
  have cellContinuous : ContinuousAt
      (fun candidate : SpatialCell => (candidate 2 : CellCircle)) point :=
    continuous_quotient_mk'.continuousAt.comp cellCoordinateCLM.continuous.continuousAt
  exact (continuous_radialRetraction.continuousAt.comp reflectedContinuous).prodMk
    cellContinuous

theorem exteriorSummandCellLift_eq_retracted {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : ℕ) (point : SpatialCell)
    (outside : 1 ≤ ‖planarPart point‖)
    (active : node index * (‖planarPart point‖ - 1) < 1) :
    exteriorSummandCellLift field index point =
      (((coefficient index *
        plateauCutoff (node index * (‖planarPart point‖ - 1)) : ℝ) : ℂ) •
        field.value (retractedReflectedDiskCell index point)) := by
  have reflectedClosed : reflectedPoint index (planarPart point) ∈ closedUnitDisk := by
    have scaleNonnegative : 0 ≤ node index * (‖planarPart point‖ - 1) :=
      mul_nonneg (node_positive index).le (sub_nonneg.mpr outside)
    have pointNormPositive : 0 < ‖planarPart point‖ :=
      lt_of_lt_of_le zero_lt_one outside
    change ‖reflectedPoint index (planarPart point)‖ ≤ 1
    rw [reflectedPoint, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr active.le),
      abs_of_pos (inv_pos.mpr pointNormPositive)]
    field_simp
    linarith
  rw [exteriorSummandCellLift_formula]
  congr 2
  change diskCellLift field.value (reflectedSpatialCell index point) =
    field.value (radialRetraction (reflectedPoint index (planarPart point)),
      (point 2 : CellCircle))
  have retractEquality : radialRetraction (reflectedPoint index (planarPart point)) =
      ⟨reflectedPoint index (planarPart point), reflectedClosed⟩ := by
    apply Subtype.ext
    exact radialRetraction_val_of_mem _ reflectedClosed
  rw [retractEquality, diskCellLift, dif_pos]
  · congr 2
    apply Prod.ext
    · apply Subtype.ext
      exact reflectedSpatialCell_planarPart index point
    · rfl
  · change ‖planarPart (reflectedSpatialCell index point)‖ ≤ 1
    rw [reflectedSpatialCell_planarPart]
    exact reflectedClosed

theorem exteriorSummandCellLift_continuousWithinAt_outerClosed {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : ℕ) (point : SpatialCell)
    (outside : 1 ≤ ‖planarPart point‖) :
    ContinuousWithinAt (exteriorSummandCellLift field index)
      {candidate : SpatialCell | 1 ≤ ‖planarPart candidate‖} point := by
  have planarNonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at outside
    linarith
  have normContinuous := (contDiffAt_norm_planarPart point planarNonzero).continuousAt
  by_cases active : node index * (‖planarPart point‖ - 1) ≤ cutoffSupportWidth
  · have activeStrict : node index * (‖planarPart point‖ - 1) < 1 := by
      rw [collar_constants.2.2.1] at active
      linarith
    have scaleContinuous : ContinuousAt
        (fun candidate : SpatialCell => node index * (‖planarPart candidate‖ - 1)) point :=
      (normContinuous.sub continuousAt_const).const_mul _
    have neighborhood : ∀ᶠ candidate in 𝓝 point,
        node index * (‖planarPart candidate‖ - 1) < 1 :=
      scaleContinuous.eventually (Iio_mem_nhds activeStrict)
    have sampleContinuous : ContinuousWithinAt
        (fun candidate : SpatialCell =>
          field.value (retractedReflectedDiskCell index candidate))
        {candidate : SpatialCell | 1 ≤ ‖planarPart candidate‖} point :=
      (field.value.continuous.continuousAt.comp
        (retractedReflectedDiskCell_continuousAt index point planarNonzero)).continuousWithinAt
    have scalarContinuous : ContinuousAt
        (fun candidate : SpatialCell =>
          ((coefficient index *
            plateauCutoff (node index * (‖planarPart candidate‖ - 1)) : ℝ) : ℂ)) point := by
      have scaleSmooth : ContDiffAt ℝ ∞
          (fun candidate : SpatialCell =>
            node index * (‖planarPart candidate‖ - 1)) point :=
        contDiffAt_const.mul
          ((contDiffAt_norm_planarPart point planarNonzero).sub contDiffAt_const)
      have cutoffSmooth := plateauCutoff_smooth.contDiffAt.comp point scaleSmooth
      exact (Complex.ofRealCLM.continuous.continuousAt.comp
        (contDiffAt_const.mul cutoffSmooth).continuousAt)
    apply (scalarContinuous.continuousWithinAt.smul sampleContinuous).congr_of_eventuallyEq
    filter_upwards [neighborhood.filter_mono inf_le_left,
      self_mem_nhdsWithin] with candidate activeCandidate candidateOutside
    exact exteriorSummandCellLift_eq_retracted field index candidate candidateOutside
      activeCandidate
    exact exteriorSummandCellLift_eq_retracted field index point outside activeStrict
  · have inactive : cutoffSupportWidth <
        node index * (‖planarPart point‖ - 1) := lt_of_not_ge active
    have scaleContinuous : ContinuousAt
        (fun candidate : SpatialCell => node index * (‖planarPart candidate‖ - 1)) point :=
      (normContinuous.sub continuousAt_const).const_mul _
    have neighborhood : ∀ᶠ candidate in 𝓝 point,
        cutoffSupportWidth ≤ node index * (‖planarPart candidate‖ - 1) :=
      (scaleContinuous.eventually (Ioi_mem_nhds inactive)).mono fun _ bound => bound.le
    have zeroContinuous : ContinuousWithinAt
        (fun _ : SpatialCell => (0 : ComplexEuclidean dimension))
        {candidate : SpatialCell | 1 ≤ ‖planarPart candidate‖} point :=
      continuousWithinAt_const
    apply zeroContinuous.congr_of_eventuallyEq
    filter_upwards [neighborhood.filter_mono inf_le_left] with candidate inactiveCandidate
    rw [exteriorSummandCellLift_formula, plateauCutoff_zero _ inactiveCandidate]
    simp
    rw [exteriorSummandCellLift_formula, plateauCutoff_zero _ inactive.le]
    simp

theorem exteriorSummandCellLift_continuousOn_outerClosed {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : ℕ) :
    ContinuousOn (exteriorSummandCellLift field index)
      {point : SpatialCell | 1 ≤ ‖planarPart point‖} := by
  intro point outside
  exact exteriorSummandCellLift_continuousWithinAt_outerClosed field index point outside

theorem exteriorSeriesCellLift_continuousOn_outerClosed {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    ContinuousOn (exteriorSeriesCellLift field)
      {point : SpatialCell | 1 ≤ ‖planarPart point‖} := by
  apply continuousOn_tsum
  · exact exteriorSummandCellLift_continuousOn_outerClosed field
  · exact (coefficient_absolute_summable.mul_right ‖field.value‖)
  · intro index point _
    exact exteriorSummand_norm_le field.value index (planarPart point) (point 2 : CellCircle)

theorem reflectedPoint_boundary (index : ℕ) (point : SpatialPlane)
    (boundary : ‖point‖ = 1) : reflectedPoint index point = point := by
  unfold reflectedPoint
  rw [boundary]
  simp

theorem exteriorSummand_boundary {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : ℕ) (point : SpatialPlane)
    (boundary : ‖point‖ = 1) (cell : CellCircle) :
    exteriorSummandFromValue field.value index point cell =
      (coefficient index : ℂ) • field.value (⟨point, boundary.le⟩, cell) := by
  have membership : point ∈ closedUnitDisk := by
    change ‖point‖ ≤ 1
    exact boundary.le
  have cutoffOne : plateauCutoff (node index * (‖point‖ - 1)) = 1 := by
    apply plateauCutoff_one
    rw [boundary, sub_self, mul_zero, collar_constants.2.1]
    norm_num
  have sample : closedDiskLift (fun diskPoint => field.value (diskPoint, cell))
      (reflectedPoint index point) = field.value (⟨point, membership⟩, cell) := by
    rw [reflectedPoint_boundary index point boundary, closedDiskLift, dif_pos membership]
  rw [exteriorSummandFromValue, cutoffOne, sample]
  simp

theorem coefficient_summable : Summable coefficient := by
  simpa only [pow_zero, mul_one] using coefficient_signed_moment_summable 0

theorem coefficient_tsum : ∑' index, coefficient index = 1 := by
  simpa only [pow_zero, mul_one] using infinite_moment_tsum 0

theorem exteriorSeries_boundary {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialPlane)
    (boundary : ‖point‖ = 1) (cell : CellCircle) :
    exteriorSeriesFromValue field.value point cell =
      field.value (⟨point, boundary.le⟩, cell) := by
  unfold exteriorSeriesFromValue
  simp_rw [exteriorSummand_boundary field _ point boundary cell]
  rw [show (∑' index, (coefficient index : ℂ) •
      field.value (⟨point, boundary.le⟩, cell)) =
      ∑' index, coefficient index • field.value (⟨point, boundary.le⟩, cell) by
    congr 1]
  rw [coefficient_summable.tsum_smul_const, coefficient_tsum, one_smul]

end Grad.DiskExtension.Operator
