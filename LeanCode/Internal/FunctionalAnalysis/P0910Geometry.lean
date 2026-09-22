import P0910Algebra

noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets
open Grad.DiskExtension.Seeley

def exteriorSpatialRegion : Set SpatialPlane := {point | 1 < ‖point‖}

def puncturedSpatialRegion : Set SpatialPlane := {point | point ≠ 0}

def planarPartLinear : SpatialCell →ₗ[ℝ] SpatialPlane where
  toFun := planarPart
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> rfl
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> rfl

noncomputable def planarPartCLM : SpatialCell →L[ℝ] SpatialPlane :=
  planarPartLinear.toContinuousLinearMap

@[simp] theorem planarPartCLM_apply (point : SpatialCell) :
    planarPartCLM point = planarPart point := rfl

def assembleSpatialCellLinear : SpatialPlane × ℝ →ₗ[ℝ] SpatialCell where
  toFun := fun input => assembleSpatialCell input.1 input.2
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> rfl
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> rfl

noncomputable def assembleSpatialCellCLM : SpatialPlane × ℝ →L[ℝ] SpatialCell :=
  assembleSpatialCellLinear.toContinuousLinearMap

@[simp] theorem assembleSpatialCellCLM_apply (input : SpatialPlane × ℝ) :
    assembleSpatialCellCLM input = assembleSpatialCell input.1 input.2 := rfl

noncomputable def cellCoordinateCLM : SpatialCell →L[ℝ] ℝ :=
  (PiLp.proj 2 (fun _ : Fin 3 => ℝ) 2)

@[simp] theorem cellCoordinateCLM_apply (point : SpatialCell) :
    cellCoordinateCLM point = point 2 := rfl

def reflectedSpatialCell (index : ℕ) (point : SpatialCell) : SpatialCell :=
  assembleSpatialCell (reflectedPoint index (planarPart point)) (point 2)

def exteriorSummandCellLift {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (index : ℕ) (point : SpatialCell) : ComplexEuclidean dimension :=
  exteriorSummandFromValue field.value index (planarPart point) (point 2 : CellCircle)

def exteriorSeriesCellLift {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (point : SpatialCell) : ComplexEuclidean dimension :=
  exteriorSeriesFromValue field.value (planarPart point) (point 2 : CellCircle)

theorem exteriorSpatialRegion_isOpen : IsOpen exteriorSpatialRegion := by
  exact isOpen_lt continuous_const continuous_norm

theorem exteriorSpatialRegion_nonzero {point : SpatialPlane}
    (outside : point ∈ exteriorSpatialRegion) : point ≠ 0 := by
  intro equality
  rw [equality] at outside
  change 1 < ‖(0 : SpatialPlane)‖ at outside
  rw [norm_zero] at outside
  norm_num at outside

theorem reflectedPoint_norm (index : ℕ) (point : SpatialPlane)
    (outside : 1 < ‖point‖)
    (activeRange : node index * (‖point‖ - 1) < 1) :
    ‖reflectedPoint index point‖ = 1 - node index * (‖point‖ - 1) := by
  have pointNormPositive : 0 < ‖point‖ := lt_trans zero_lt_one outside
  have radialNonnegative : 0 ≤ node index * (‖point‖ - 1) :=
    mul_nonneg (node_positive index).le (sub_nonneg.mpr outside.le)
  rw [reflectedPoint, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (sub_nonneg.mpr activeRange.le), abs_of_pos (inv_pos.mpr pointNormPositive)]
  field_simp

theorem reflectedPoint_mem_openUnitDisk (index : ℕ) (point : SpatialPlane)
    (outside : 1 < ‖point‖)
    (activeRange : node index * (‖point‖ - 1) < 1) :
    reflectedPoint index point ∈ openUnitDisk := by
  change ‖reflectedPoint index point‖ < 1
  rw [reflectedPoint_norm index point outside activeRange]
  have positiveScale : 0 < node index * (‖point‖ - 1) :=
    mul_pos (node_positive index) (sub_pos.mpr outside)
  linarith

theorem reflectedPoint_mem_closedUnitDisk (index : ℕ) (point : SpatialPlane)
    (outside : 1 < ‖point‖)
    (activeRange : node index * (‖point‖ - 1) < 1) :
    reflectedPoint index point ∈ closedUnitDisk :=
  openDiskMembershipClosed _ (reflectedPoint_mem_openUnitDisk index point outside activeRange)

theorem closedDiskLift_eq_diskCellLift_assemble {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (point : SpatialPlane) (cell : ℝ) :
    closedDiskLift (fun diskPoint => value (diskPoint, (cell : CellCircle))) point =
      diskCellLift value (assembleSpatialCell point cell) := by
  classical
  by_cases membership : point ∈ closedUnitDisk
  · have cylinderMembership : assembleSpatialCell point cell ∈ closedUnitCylinder := by
      change ‖planarPart (assembleSpatialCell point cell)‖ ≤ 1
      rw [planarPart_assembleSpatialCell]
      exact membership
    simp only [closedDiskLift, dif_pos membership, diskCellLift,
      dif_pos cylinderMembership]
    congr 2
    apply Subtype.ext
    exact (planarPart_assembleSpatialCell point cell).symm
  · have notCylinder : assembleSpatialCell point cell ∉ closedUnitCylinder := by
      intro cylinderMembership
      apply membership
      change ‖point‖ ≤ 1
      change ‖planarPart (assembleSpatialCell point cell)‖ ≤ 1 at cylinderMembership
      simpa only [planarPart_assembleSpatialCell] using cylinderMembership
    simp [closedDiskLift, diskCellLift, membership, notCylinder]

theorem exteriorSummandCellLift_formula {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : ℕ) (point : SpatialCell) :
    exteriorSummandCellLift field index point =
      (((coefficient index *
        plateauCutoff (node index * (‖planarPart point‖ - 1)) : ℝ) : ℂ) •
        diskCellLift field.value (reflectedSpatialCell index point)) := by
  rw [exteriorSummandCellLift, exteriorSummandFromValue, reflectedSpatialCell,
    closedDiskLift_eq_diskCellLift_assemble]

theorem reflectedSpatialCell_planarPart (index : ℕ) (point : SpatialCell) :
    planarPart (reflectedSpatialCell index point) =
      reflectedPoint index (planarPart point) := by
  exact planarPart_assembleSpatialCell _ _

theorem reflectedSpatialCell_mem_openUnitCylinder (index : ℕ) (point : SpatialCell)
    (outside : 1 < ‖planarPart point‖)
    (activeRange : node index * (‖planarPart point‖ - 1) < 1) :
    reflectedSpatialCell index point ∈ openUnitCylinder := by
  change ‖planarPart (reflectedSpatialCell index point)‖ < 1
  rw [reflectedSpatialCell_planarPart]
  exact reflectedPoint_mem_openUnitDisk index (planarPart point) outside activeRange

theorem contDiffAt_norm_planarPart (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    ContDiffAt ℝ ∞ (fun candidate : SpatialCell => ‖planarPart candidate‖) point := by
  have planarSmooth : ContDiff ℝ ∞ planarPart := by
    change ContDiff ℝ ∞ (fun candidate : SpatialCell => planarPartCLM candidate)
    exact planarPartCLM.contDiff
  exact planarSmooth.contDiffAt.norm ℝ nonzero

theorem reflectedSpatialCell_contDiffAt (index : ℕ) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    ContDiffAt ℝ ∞ (reflectedSpatialCell index) point := by
  have normSmooth := contDiffAt_norm_planarPart point nonzero
  have planarSmooth : ContDiff ℝ ∞ planarPart := by
    change ContDiff ℝ ∞ (fun candidate : SpatialCell => planarPartCLM candidate)
    exact planarPartCLM.contDiff
  have normNonzero : ‖planarPart point‖ ≠ 0 := norm_ne_zero_iff.mpr nonzero
  have firstScalar : ContDiffAt ℝ ∞
      (fun candidate : SpatialCell =>
        1 - node index * (‖planarPart candidate‖ - 1)) point := by
    fun_prop
  have inverseNorm : ContDiffAt ℝ ∞
      (fun candidate : SpatialCell => ‖planarPart candidate‖⁻¹) point :=
    normSmooth.inv normNonzero
  have normalized : ContDiffAt ℝ ∞
      (fun candidate : SpatialCell =>
        ‖planarPart candidate‖⁻¹ • planarPart candidate) point :=
    inverseNorm.smul planarSmooth.contDiffAt
  have reflected : ContDiffAt ℝ ∞
      (fun candidate : SpatialCell => reflectedPoint index (planarPart candidate)) point := by
    change ContDiffAt ℝ ∞
      (fun candidate : SpatialCell =>
        (1 - node index * (‖planarPart candidate‖ - 1)) •
          (‖planarPart candidate‖⁻¹ • planarPart candidate)) point
    exact firstScalar.smul normalized
  have cellSmooth : ContDiffAt ℝ ∞ (fun candidate : SpatialCell => candidate 2) point := by
    change ContDiffAt ℝ ∞ (fun candidate : SpatialCell => cellCoordinateCLM candidate) point
    exact cellCoordinateCLM.contDiff.contDiffAt
  rw [show reflectedSpatialCell index = fun candidate =>
      assembleSpatialCellCLM
        (reflectedPoint index (planarPart candidate), candidate 2) by
    funext candidate
    simp [reflectedSpatialCell]]
  exact assembleSpatialCellCLM.contDiff.contDiffAt.comp point (reflected.prodMk cellSmooth)

theorem exteriorSummandCellLift_contDiffAt {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : ℕ) (point : SpatialCell)
    (outside : 1 < ‖planarPart point‖) :
    ContDiffAt ℝ ∞ (exteriorSummandCellLift field index) point := by
  have planarNonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at outside
    linarith
  have normSmooth := contDiffAt_norm_planarPart point planarNonzero
  by_cases active : node index * (‖planarPart point‖ - 1) ≤ cutoffSupportWidth
  · have activeRange : node index * (‖planarPart point‖ - 1) < 1 := by
      rw [collar_constants.2.2.1] at active
      linarith
    have mappedMembership :=
      reflectedSpatialCell_mem_openUnitCylinder index point outside activeRange
    have fieldSmoothAt : ContDiffAt ℝ ∞ (diskCellLift field.value)
        (reflectedSpatialCell index point) :=
      (field.smoothInterior _ mappedMembership).contDiffAt
        (openUnitCylinder_isOpen.mem_nhds mappedMembership)
    rw [show exteriorSummandCellLift field index = fun candidate =>
        (((coefficient index *
          plateauCutoff (node index * (‖planarPart candidate‖ - 1)) : ℝ) : ℂ) •
          diskCellLift field.value (reflectedSpatialCell index candidate)) by
      funext candidate
      exact exteriorSummandCellLift_formula field index candidate]
    have reflectedSmooth := reflectedSpatialCell_contDiffAt index point planarNonzero
    have scaleSmooth : ContDiffAt ℝ ∞
        (fun candidate : SpatialCell =>
          node index * (‖planarPart candidate‖ - 1)) point :=
      contDiffAt_const.mul (normSmooth.sub contDiffAt_const)
    have cutoffSmooth : ContDiffAt ℝ ∞
        (fun candidate : SpatialCell =>
          plateauCutoff (node index * (‖planarPart candidate‖ - 1))) point :=
      plateauCutoff_smooth.contDiffAt.comp point scaleSmooth
    have realScalarSmooth : ContDiffAt ℝ ∞
        (fun candidate : SpatialCell => coefficient index *
          plateauCutoff (node index * (‖planarPart candidate‖ - 1))) point := by
      exact contDiffAt_const.mul cutoffSmooth
    have complexScalarSmooth : ContDiffAt ℝ ∞
        (fun candidate : SpatialCell =>
          ((coefficient index *
            plateauCutoff (node index * (‖planarPart candidate‖ - 1)) : ℝ) : ℂ)) point := by
      exact Complex.ofRealCLM.contDiff.contDiffAt.comp point realScalarSmooth
    exact complexScalarSmooth.smul (fieldSmoothAt.comp point reflectedSmooth)
  · have strictInactive : cutoffSupportWidth <
        node index * (‖planarPart point‖ - 1) := lt_of_not_ge active
    have scaleContinuousAt : ContinuousAt
        (fun candidate : SpatialCell => node index * (‖planarPart candidate‖ - 1)) point :=
      (normSmooth.continuousAt.sub continuousAt_const).const_mul _
    have eventuallyInactive : ∀ᶠ candidate in 𝓝 point,
        cutoffSupportWidth ≤ node index * (‖planarPart candidate‖ - 1) :=
      (scaleContinuousAt.eventually (Ioi_mem_nhds strictInactive)).mono
        fun _ inequality => inequality.le
    have zeroSmooth : ContDiffAt ℝ ∞
        (fun _ : SpatialCell => (0 : ComplexEuclidean dimension)) point := contDiffAt_const
    apply zeroSmooth.congr_of_eventuallyEq
    filter_upwards [eventuallyInactive] with candidate inactive
    rw [exteriorSummandCellLift_formula, plateauCutoff_zero _ inactive]
    simp

theorem exteriorSummandCellLift_contDiffOn {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : ℕ) :
    ContDiffOn ℝ ∞ (exteriorSummandCellLift field index)
      {point : SpatialCell | 1 < ‖planarPart point‖} := by
  intro point outside
  exact (exteriorSummandCellLift_contDiffAt field index point outside).contDiffWithinAt

theorem eventually_common_exterior_tail_zero {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (outside : 1 < ‖planarPart point‖) :
    ∃ cutoff : ℕ, ∀ᶠ candidate in 𝓝 point, ∀ index, cutoff ≤ index →
      exteriorSummandCellLift field index candidate = 0 := by
  have gapPositive : 0 < ‖planarPart point‖ - 1 := sub_pos.mpr outside
  have tends : Tendsto
      (fun index : ℕ => node index * (‖planarPart point‖ - 1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const
      gapPositive
  have eventuallyStrict := tends.eventually_gt_atTop cutoffSupportWidth
  rw [eventually_atTop] at eventuallyStrict
  obtain ⟨cutoff, cutoffProperty⟩ := eventuallyStrict
  have cutoffStrict : cutoffSupportWidth <
      node cutoff * (‖planarPart point‖ - 1) := cutoffProperty cutoff le_rfl
  have cutoffScaleContinuous : Continuous
      (fun candidate : SpatialCell =>
        node cutoff * (‖planarPart candidate‖ - 1)) :=
    continuous_const.mul ((continuous_norm.comp continuous_planarPart).sub continuous_const)
  have neighborhood : ∀ᶠ candidate in 𝓝 point,
      cutoffSupportWidth < node cutoff * (‖planarPart candidate‖ - 1) :=
    cutoffScaleContinuous.continuousAt.eventually (Ioi_mem_nhds cutoffStrict)
  refine ⟨cutoff, neighborhood.mono fun candidate candidateStrict index indexBound => ?_⟩
  have gapNonnegative : 0 ≤ ‖planarPart candidate‖ - 1 := by
    have cutoffPositive : 0 < node cutoff := node_positive cutoff
    rw [collar_constants.2.2.1] at candidateStrict
    nlinarith
  have nodeBound : node cutoff ≤ node index := node_strictMono.monotone indexBound
  have scaleBound : cutoffSupportWidth ≤
      node index * (‖planarPart candidate‖ - 1) :=
    candidateStrict.le.trans
      (mul_le_mul_of_nonneg_right nodeBound gapNonnegative)
  simp [exteriorSummandCellLift_formula, plateauCutoff_zero _ scaleBound]

theorem exteriorSeriesCellLift_eq_finite_sum_of_tail
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (cutoff : ℕ)
    (point : SpatialCell)
    (tail : ∀ index, cutoff ≤ index → exteriorSummandCellLift field index point = 0) :
    exteriorSeriesCellLift field point =
      ∑ index ∈ Finset.range cutoff, exteriorSummandCellLift field index point := by
  unfold exteriorSeriesCellLift exteriorSeriesFromValue exteriorSummandCellLift
  exact (hasSum_sum_of_ne_finset_zero fun index outsideRange =>
    tail index (by simpa using outsideRange)).tsum_eq

theorem exteriorSeriesCellLift_contDiffAt {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (outside : 1 < ‖planarPart point‖) :
    ContDiffAt ℝ ∞ (exteriorSeriesCellLift field) point := by
  obtain ⟨cutoff, neighborhood⟩ :=
    eventually_common_exterior_tail_zero field point outside
  have finiteSmooth : ContDiffAt ℝ ∞
      (fun candidate =>
        ∑ index ∈ Finset.range cutoff, exteriorSummandCellLift field index candidate) point := by
    exact ContDiffAt.sum fun index _ =>
      exteriorSummandCellLift_contDiffAt field index point outside
  apply finiteSmooth.congr_of_eventuallyEq
  filter_upwards [neighborhood] with candidate tail
  exact exteriorSeriesCellLift_eq_finite_sum_of_tail field cutoff candidate tail

theorem exteriorSeriesCellLift_contDiffOn {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    ContDiffOn ℝ ∞ (exteriorSeriesCellLift field)
      {point : SpatialCell | 1 < ‖planarPart point‖} := by
  intro point outside
  exact (exteriorSeriesCellLift_contDiffAt field point outside).contDiffWithinAt

theorem cutoff_nonzero_activeRange (index : ℕ) (point : SpatialPlane)
    (nonzero : plateauCutoff (node index * (‖point‖ - 1)) ≠ 0) :
    node index * (‖point‖ - 1) < cutoffSupportWidth := by
  by_contra bound
  exact nonzero (plateauCutoff_zero _ (le_of_not_gt bound))

theorem cutoff_nonzero_reflectedPoint_mem_openUnitDisk (index : ℕ)
    (point : SpatialPlane) (outside : 1 < ‖point‖)
    (nonzero : plateauCutoff (node index * (‖point‖ - 1)) ≠ 0) :
    reflectedPoint index point ∈ openUnitDisk := by
  apply reflectedPoint_mem_openUnitDisk index point outside
  have active := cutoff_nonzero_activeRange index point nonzero
  rw [collar_constants.2.2.1] at active
  linarith

theorem eventually_cutoff_zero (point : SpatialPlane) (outside : 1 < ‖point‖) :
    ∀ᶠ index : ℕ in atTop,
      plateauCutoff (node index * (‖point‖ - 1)) = 0 := by
  have gapPositive : 0 < ‖point‖ - 1 := sub_pos.mpr outside
  have tends : Tendsto (fun index : ℕ => node index * (‖point‖ - 1)) atTop atTop := by
    exact (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const
      gapPositive
  filter_upwards [tends.eventually_ge_atTop cutoffSupportWidth] with index bound
  exact plateauCutoff_zero _ bound

theorem eventually_exteriorSummand_zero {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (point : SpatialPlane) (cell : CellCircle) (outside : 1 < ‖point‖) :
    ∀ᶠ index : ℕ in atTop,
      exteriorSummandFromValue value index point cell = 0 := by
  filter_upwards [eventually_cutoff_zero point outside] with index cutoffZero
  simp [exteriorSummandFromValue, cutoffZero]

theorem exteriorSeries_eq_finite_sum_eventually {dimension : ℕ}
    (value : ContinuousMap DiskCellDomain (ComplexEuclidean dimension))
    (point : SpatialPlane) (cell : CellCircle) (outside : 1 < ‖point‖) :
    ∃ cutoff : ℕ, exteriorSeriesFromValue value point cell =
      ∑ index ∈ Finset.range cutoff, exteriorSummandFromValue value index point cell := by
  have eventualZero := eventually_exteriorSummand_zero value point cell outside
  rw [Filter.eventually_atTop] at eventualZero
  obtain ⟨cutoff, cutoffProperty⟩ := eventualZero
  refine ⟨cutoff, ?_⟩
  unfold exteriorSeriesFromValue
  exact (hasSum_sum_of_ne_finset_zero fun index outsideRange =>
    cutoffProperty index (by simpa using outsideRange)).tsum_eq

end Grad.DiskExtension.Operator
