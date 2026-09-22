import P0910HigherExterior

noncomputable section

open Filter Set
open scoped BigOperators ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets
open Grad.DiskExtension.Seeley

def boundaryJetRadius (index : ℕ) : ℝ :=
  1 / (48 * node index)

theorem boundaryJetRadius_positive (index : ℕ) :
    0 < boundaryJetRadius index := by
  unfold boundaryJetRadius
  exact one_div_pos.mpr (mul_pos (by norm_num) (node_positive index))

def exteriorJetBall (index : ℕ) (point : SpatialCell) : Set SpatialCell :=
  planarPartCLM ⁻¹' Metric.ball
    ((1 + boundaryJetRadius index) • planarPart point)
    (boundaryJetRadius index)

theorem exteriorJetBall_isOpen (index : ℕ) (point : SpatialCell) :
    IsOpen (exteriorJetBall index point) :=
  Metric.isOpen_ball.preimage planarPartCLM.continuous

theorem exteriorJetBall_convex (index : ℕ) (point : SpatialCell) :
    Convex ℝ (exteriorJetBall index point) :=
  (convex_ball
    ((1 + boundaryJetRadius index) • planarPart point)
    (boundaryJetRadius index)).linear_preimage planarPartLinear

theorem closure_exteriorJetBall (index : ℕ) (point : SpatialCell) :
    closure (exteriorJetBall index point) =
      planarPartCLM ⁻¹' Metric.closedBall
        ((1 + boundaryJetRadius index) • planarPart point)
        (boundaryJetRadius index) := by
  rw [exteriorJetBall,
    planarPartCLM.closure_preimage planarPartCLM_surjective,
    closure_ball _ (ne_of_gt (boundaryJetRadius_positive index))]

theorem closure_exteriorJetBall_convex (index : ℕ) (point : SpatialCell) :
    Convex ℝ (closure (exteriorJetBall index point)) := by
  rw [closure_exteriorJetBall]
  exact (convex_closedBall
    ((1 + boundaryJetRadius index) • planarPart point)
    (boundaryJetRadius index)).linear_preimage planarPartLinear

theorem closure_exteriorJetBall_interior_nonempty
    (index : ℕ) (point : SpatialCell) :
    (interior (closure (exteriorJetBall index point))).Nonempty := by
  let center : SpatialCell := assembleSpatialCell
    ((1 + boundaryJetRadius index) • planarPart point) (point 2)
  have centerMembership : center ∈ exteriorJetBall index point := by
    change dist (planarPart center)
      ((1 + boundaryJetRadius index) • planarPart point) <
        boundaryJetRadius index
    rw [show planarPart center =
        (1 + boundaryJetRadius index) • planarPart point by
      exact planarPart_assembleSpatialCell _ _]
    rw [dist_self]
    exact boundaryJetRadius_positive index
  refine ⟨center, mem_interior_iff_mem_nhds.mpr ?_⟩
  exact Filter.mem_of_superset
    ((exteriorJetBall_isOpen index point).mem_nhds centerMembership)
    subset_closure

theorem closure_exteriorJetBall_uniqueDiffOn (index : ℕ)
    (point : SpatialCell) :
    UniqueDiffOn ℝ (closure (exteriorJetBall index point)) :=
  uniqueDiffOn_convex
    (closure_exteriorJetBall_convex index point)
    (closure_exteriorJetBall_interior_nonempty index point)

theorem boundary_mem_closure_exteriorJetBall (index : ℕ)
    (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    point ∈ closure (exteriorJetBall index point) := by
  rw [closure_exteriorJetBall]
  change dist (planarPart point)
    ((1 + boundaryJetRadius index) • planarPart point) ≤
      boundaryJetRadius index
  rw [dist_eq_norm, show planarPart point -
      (1 + boundaryJetRadius index) • planarPart point =
        -(boundaryJetRadius index) • planarPart point by module,
    norm_smul, Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (boundaryJetRadius_positive index).le, boundary, mul_one]

theorem closure_exteriorJetBall_subset_closedExteriorRegion
    (index : ℕ) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    closure (exteriorJetBall index point) ⊆ closedExteriorRegion := by
  intro candidate membership
  rw [closure_exteriorJetBall] at membership
  change dist (planarPart candidate)
    ((1 + boundaryJetRadius index) • planarPart point) ≤
      boundaryJetRadius index at membership
  have triangle := dist_triangle
    ((1 + boundaryJetRadius index) • planarPart point)
    (planarPart candidate) 0
  rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg
      (add_nonneg (by norm_num) (boundaryJetRadius_positive index).le),
    boundary, mul_one,
    dist_comm ((1 + boundaryJetRadius index) • planarPart point)
      (planarPart candidate), dist_zero_right] at triangle
  change 1 ≤ ‖planarPart candidate‖
  linarith

theorem closure_exteriorJetBall_cutoffPlateau
    (index : ℕ) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    ∀ candidate ∈ closure (exteriorJetBall index point),
      node index * (‖planarPart candidate‖ - 1) ≤ cutoffPlateauWidth := by
  intro candidate membership
  rw [closure_exteriorJetBall] at membership
  change dist (planarPart candidate)
    ((1 + boundaryJetRadius index) • planarPart point) ≤
      boundaryJetRadius index at membership
  have triangle := dist_triangle (planarPart candidate)
    ((1 + boundaryJetRadius index) • planarPart point) 0
  simp only [dist_zero_right] at triangle
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg
      (add_nonneg (by norm_num) (boundaryJetRadius_positive index).le),
    boundary, mul_one] at triangle
  have radiusUpper : ‖planarPart candidate‖ - 1 ≤
      2 * boundaryJetRadius index := by
    linarith
  have scaledUpper := mul_le_mul_of_nonneg_left radiusUpper
    (node_positive index).le
  have radiusFormula : node index * (2 * boundaryJetRadius index) =
      (1 / 24 : ℝ) := by
    rw [boundaryJetRadius]
    field_simp [ne_of_gt (node_positive index)]
    ring
  calc
    node index * (‖planarPart candidate‖ - 1) ≤
        node index * (2 * boundaryJetRadius index) := scaledUpper
    _ = 1 / 24 := radiusFormula
    _ ≤ cutoffPlateauWidth := by
      rw [collar_constants.2.1]
      norm_num

theorem closure_exteriorJetBall_subset_closedExteriorActiveRegion
    (index : ℕ) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    closure (exteriorJetBall index point) ⊆
      closedExteriorActiveRegion index := by
  intro candidate membership
  refine ⟨closure_exteriorJetBall_subset_closedExteriorRegion
    index point boundary membership, ?_⟩
  exact (closure_exteriorJetBall_cutoffPlateau index point boundary
    candidate membership).trans (by
      rw [collar_constants.2.1]
      norm_num)

noncomputable def coefficientActionCLM {dimension : ℕ} (index : ℕ) :
    ComplexEuclidean dimension →L[ℝ] ComplexEuclidean dimension :=
  ContinuousLinearMap.lsmul ℝ ℂ (coefficient index : ℂ)

@[simp] theorem coefficientActionCLM_apply {dimension : ℕ}
    (index : ℕ) (value : ComplexEuclidean dimension) :
    coefficientActionCLM index value = coefficient index • value := by
  rw [coefficientActionCLM, ContinuousLinearMap.lsmul_apply]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ)
    (coefficient index) value).symm

noncomputable def coefficientReflectedTaylorSeries {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (index : ℕ) (point : SpatialCell) :
    FormalMultilinearSeries ℝ SpatialCell (ComplexEuclidean dimension) :=
  fun order => (coefficientActionCLM index).compContinuousMultilinearMap
    (reflectedCompositeTaylorSeries field index point order)

theorem coefficientReflected_hasFTaylorSeriesUpToOn_active
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (index : ℕ) :
    HasFTaylorSeriesUpToOn (𝕜 := ℝ) ∞
      (fun point => (coefficient index : ℂ) •
        (diskCellLift field.value ∘ reflectedSpatialCell index) point)
      (coefficientReflectedTaylorSeries field index)
      (closedExteriorActiveRegion index) := by
  have transformed :=
    HasFTaylorSeriesUpToOn.continuousLinearMap_comp
      (coefficientActionCLM (dimension := dimension) index)
      (diskCellLift_comp_reflectedSpatialCell_hasFTaylorSeriesUpToOn_active
        field index)
  change HasFTaylorSeriesUpToOn (𝕜 := ℝ) ∞
    (fun point => (coefficient index : ℂ) •
      (diskCellLift field.value ∘ reflectedSpatialCell index) point)
    (fun point order => (coefficientActionCLM index).compContinuousMultilinearMap
      (reflectedCompositeTaylorSeries field index point order))
    (closedExteriorActiveRegion index)
  apply transformed.congr
  intro point _
  simp only [Function.comp_apply, coefficientActionCLM_apply]
  exact (RCLike.real_smul_eq_coe_smul (K := ℂ)
    (coefficient index)
    (diskCellLift field.value (reflectedSpatialCell index point))).symm

theorem coefficientReflectedTaylorSeries_eq_real_smul
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (index order : ℕ)
    (point : SpatialCell) :
    coefficientReflectedTaylorSeries field index point order =
      coefficient index • reflectedCompositeTaylorSeries field index point order := by
  ext directions
  simp [coefficientReflectedTaylorSeries]

theorem exteriorSummandTaylorSeries_boundary
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (index order : ℕ)
    (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    exteriorSummandTaylorSeries field index point order =
      coefficient index • reflectedCompositeTaylorSeries field index point order := by
  let region := closure (exteriorJetBall index point)
  have regionSubset : region ⊆ closedExteriorActiveRegion index :=
    closure_exteriorJetBall_subset_closedExteriorActiveRegion
      index point boundary
  have pointMembership : point ∈ region :=
    boundary_mem_closure_exteriorJetBall index point boundary
  have regionUnique : UniqueDiffOn ℝ region :=
    closure_exteriorJetBall_uniqueDiffOn index point
  have functionEquality : Set.EqOn (exteriorSummandCellLift field index)
      (fun candidate => (coefficient index : ℂ) •
        (diskCellLift field.value ∘ reflectedSpatialCell index) candidate)
      region := by
    intro candidate membership
    have plateau := closure_exteriorJetBall_cutoffPlateau
      index point boundary candidate membership
    rw [exteriorSummandCellLift_formula, plateauCutoff_one _ plateau]
    simp
  have summandCoefficient :=
    ((exteriorSummandCellLift_hasFTaylorSeriesUpToOn_active field index).mono
      regionSubset).eq_iteratedFDerivWithin_of_uniqueDiffOn
        (m := order)
        (WithTop.coe_le_coe.mpr
          (show (order : ℕ∞) ≤ ⊤ from le_top))
        regionUnique pointMembership
  have reflectedCoefficient :=
    ((coefficientReflected_hasFTaylorSeriesUpToOn_active field index).mono
      regionSubset).eq_iteratedFDerivWithin_of_uniqueDiffOn
        (m := order)
        (WithTop.coe_le_coe.mpr
          (show (order : ℕ∞) ≤ ⊤ from le_top))
        regionUnique pointMembership
  have derivativeEquality := iteratedFDerivWithin_congr (𝕜 := ℝ)
    functionEquality pointMembership order
  calc
    exteriorSummandTaylorSeries field index point order =
        coefficientReflectedTaylorSeries field index point order :=
      summandCoefficient.trans
        (derivativeEquality.trans reflectedCoefficient.symm)
    _ = coefficient index •
        reflectedCompositeTaylorSeries field index point order :=
      coefficientReflectedTaylorSeries_eq_real_smul
        field index order point

theorem coefficient_reflectedCompositeTaylorSeries_hasSum_boundary
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    HasSum (fun index => coefficient index •
        reflectedCompositeTaylorSeries field index point order)
      (closedHigherDerivative (order := order) field point) := by
  change HasSum (fun index => coefficient index •
      ((closedTaylorSeries field (reflectedSpatialCell index point)).taylorComp
        (fun innerOrder => iteratedFDeriv ℝ innerOrder
          (reflectedSpatialCell index) point)) order)
    (closedHigherDerivative (order := order) field point)
  have reconstruction :=
    coefficient_closedTaylorSeries_taylorComp_reflectedSpatialCell_hasSum_closed
      field order point boundary
  convert reconstruction using 1
  funext index
  rw [reflectedSpatialCell_boundary index point boundary]

def strictExteriorRegion : Set SpatialCell :=
  {point | 1 < ‖planarPart point‖}

theorem eventually_mem_openExteriorActiveRegion_boundary
    (index : ℕ) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    ∀ᶠ candidate in 𝓝[strictExteriorRegion] point,
      candidate ∈ openExteriorActiveRegion index := by
  have scaleContinuous : Continuous (fun candidate : SpatialCell =>
      node index * (‖planarPart candidate‖ - 1)) :=
    continuous_const.mul
      ((continuous_norm.comp continuous_planarPart).sub continuous_const)
  have scaleAt : node index * (‖planarPart point‖ - 1) = 0 := by
    rw [boundary]
    ring
  have scaleNeighborhood : ∀ᶠ candidate in 𝓝 point,
      node index * (‖planarPart candidate‖ - 1) < 1 := by
    have targetNeighborhood : ∀ᶠ scale in
        𝓝 (node index * (‖planarPart point‖ - 1)), scale < 1 := by
      rw [scaleAt]
      exact Iio_mem_nhds (by norm_num)
    exact scaleContinuous.continuousAt.eventually targetNeighborhood
  filter_upwards [scaleNeighborhood.filter_mono inf_le_left,
    self_mem_nhdsWithin] with candidate scaleBound outside
  exact ⟨outside, scaleBound⟩

theorem exteriorSummandTaylorSeries_eq_iteratedFDeriv_of_mem_openActive
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (index order : ℕ)
    (point : SpatialCell) (membership : point ∈ openExteriorActiveRegion index) :
    exteriorSummandTaylorSeries field index point order =
      iteratedFDeriv ℝ order (exteriorSummandCellLift field index) point := by
  have restrictedTaylor :=
    (exteriorSummandCellLift_hasFTaylorSeriesUpToOn_active field index).mono
      (openExteriorActiveRegion_subset_closedExteriorActiveRegion index)
  have coefficientEquality :=
    restrictedTaylor.eq_iteratedFDerivWithin_of_uniqueDiffOn
      (m := order)
      (WithTop.coe_le_coe.mpr
        (show (order : ℕ∞) ≤ ⊤ from le_top))
      (openExteriorActiveRegion_isOpen index).uniqueDiffOn membership
  rw [iteratedFDerivWithin_of_isOpen order
    (openExteriorActiveRegion_isOpen index) membership] at coefficientEquality
  exact coefficientEquality

theorem exteriorSummand_iteratedFDeriv_tendsto_boundary
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (index order : ℕ)
    (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    Tendsto (fun candidate =>
      iteratedFDeriv ℝ order (exteriorSummandCellLift field index) candidate)
      (𝓝[strictExteriorRegion] point)
      (𝓝 (coefficient index •
        reflectedCompositeTaylorSeries field index point order)) := by
  have pointActive : point ∈ closedExteriorActiveRegion index := by
    constructor
    · exact boundary.ge
    · rw [boundary]
      simp
  have activeEventually :=
    eventually_mem_openExteriorActiveRegion_boundary index point boundary
  have filterBound : 𝓝[strictExteriorRegion] point ≤
      𝓝[closedExteriorActiveRegion index] point := by
    rw [nhdsWithin, nhdsWithin]
    apply le_inf inf_le_left
    rw [le_principal_iff]
    exact activeEventually.mono fun candidate membership =>
      openExteriorActiveRegion_subset_closedExteriorActiveRegion index membership
  have seriesConvergence : Tendsto (fun candidate =>
      exteriorSummandTaylorSeries field index candidate order)
      (𝓝[strictExteriorRegion] point)
      (𝓝 (exteriorSummandTaylorSeries field index point order)) :=
    (((exteriorSummandCellLift_hasFTaylorSeriesUpToOn_active field index).cont
      order (WithTop.coe_le_coe.mpr
        (show (order : ℕ∞) ≤ ⊤ from le_top))) point pointActive).mono_left
          filterBound
  rw [exteriorSummandTaylorSeries_boundary
    field index order point boundary] at seriesConvergence
  apply seriesConvergence.congr'
  filter_upwards [activeEventually] with candidate membership
  exact exteriorSummandTaylorSeries_eq_iteratedFDeriv_of_mem_openActive
    field index order candidate membership

theorem eventually_exteriorSummand_iteratedFDeriv_norm_le_boundary_on_exterior
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    ∀ᶠ candidate in 𝓝[strictExteriorRegion] point, ∀ index,
      ‖iteratedFDeriv ℝ order
        (exteriorSummandCellLift field index) candidate‖ ≤
          exteriorSummandJetBound field order point *
            (|coefficient index| * node index ^ order) := by
  have bounds : ∀ᶠ candidate in 𝓝[strictExteriorRegion] point, ∀ index,
      1 < ‖planarPart candidate‖ →
      ‖iteratedFDeriv ℝ order
        (exteriorSummandCellLift field index) candidate‖ ≤
          exteriorSummandJetBound field order point *
            (|coefficient index| * node index ^ order) :=
    (eventually_exteriorSummand_iteratedFDeriv_norm_le_boundary
      field order point boundary).filter_mono
        (show 𝓝[strictExteriorRegion] point ≤ 𝓝 point from inf_le_left)
  filter_upwards [bounds, self_mem_nhdsWithin] with candidate candidateBounds outside
  exact fun index => candidateBounds index outside

noncomputable def exteriorHigherDerivative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ) (point : SpatialCell) :
    SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension :=
  ∑' index, iteratedFDeriv ℝ order
    (exteriorSummandCellLift field index) point

theorem exteriorHigherDerivative_tendsto_boundary
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    Tendsto (exteriorHigherDerivative field order)
      (𝓝[strictExteriorRegion] point)
      (𝓝 (closedHigherDerivative (order := order) field point)) := by
  have convergence : Tendsto (fun candidate =>
      ∑' index, iteratedFDeriv ℝ order
        (exteriorSummandCellLift field index) candidate)
      (𝓝[strictExteriorRegion] point)
      (𝓝 (∑' index, coefficient index •
        reflectedCompositeTaylorSeries field index point order)) := by
    apply tendsto_tsum_of_dominated_convergence
      (exteriorSummandJetMajorant_summable field order point)
    · intro index
      exact exteriorSummand_iteratedFDeriv_tendsto_boundary
        field index order point boundary
    · exact eventually_exteriorSummand_iteratedFDeriv_norm_le_boundary_on_exterior
        field order point boundary
  rw [(coefficient_reflectedCompositeTaylorSeries_hasSum_boundary
    field order point boundary).tsum_eq] at convergence
  exact convergence

theorem exteriorHigherDerivative_eq_iteratedFDeriv
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (outside : point ∈ strictExteriorRegion) :
    exteriorHigherDerivative field order point =
      iteratedFDeriv ℝ order (exteriorSeriesCellLift field) point := by
  obtain ⟨cutoff, neighborhood⟩ :=
    eventually_common_exterior_tail_zero field point outside
  have functionEquality : exteriorSeriesCellLift field =ᶠ[𝓝 point]
      fun candidate =>
        ∑ index ∈ Finset.range cutoff,
          exteriorSummandCellLift field index candidate := by
    filter_upwards [neighborhood] with candidate tail
    exact exteriorSeriesCellLift_eq_finite_sum_of_tail
      field cutoff candidate tail
  have derivativeEquality :=
    (functionEquality.iteratedFDeriv ℝ order).eq_of_nhds
  have finiteDerivative :
      iteratedFDeriv ℝ order
          (fun candidate => ∑ index ∈ Finset.range cutoff,
            exteriorSummandCellLift field index candidate) point =
        ∑ index ∈ Finset.range cutoff,
          iteratedFDeriv ℝ order
            (exteriorSummandCellLift field index) point := by
    have sumFunctionEquality :
        (fun candidate => ∑ index ∈ Finset.range cutoff,
          exteriorSummandCellLift field index candidate) =
        ∑ index ∈ Finset.range cutoff,
          exteriorSummandCellLift field index := by
      funext candidate
      simp only [Finset.sum_apply]
    rw [sumFunctionEquality]
    have summandSmooth : ∀ index ∈ Finset.range cutoff,
        ContDiffAt ℝ order
          (exteriorSummandCellLift field index) point := by
      intro index _
      exact (exteriorSummandCellLift_contDiffAt field index point outside).of_le
        (WithTop.coe_le_coe.mpr
          (show (order : ℕ∞) ≤ ⊤ from le_top))
    exact iteratedFDeriv_sum_apply (f := fun index =>
        exteriorSummandCellLift field index)
        (u := Finset.range cutoff) summandSmooth
  have derivativeTailZero : ∀ index, cutoff ≤ index →
      iteratedFDeriv ℝ order
        (exteriorSummandCellLift field index) point = 0 := by
    intro index indexBound
    have summandZero : exteriorSummandCellLift field index =ᶠ[𝓝 point]
        fun _ => (0 : ComplexEuclidean dimension) := by
      filter_upwards [neighborhood] with candidate tail
      exact tail index indexBound
    have derivativeZero :=
      (summandZero.iteratedFDeriv ℝ order).eq_of_nhds
    rw [derivativeZero]
    rcases eq_or_ne order 0 with rfl | positive
    · rfl
    · rw [iteratedFDeriv_const_of_ne positive
        (0 : ComplexEuclidean dimension)]
      simp
  have tsumEquality : exteriorHigherDerivative field order point =
      ∑ index ∈ Finset.range cutoff,
        iteratedFDeriv ℝ order
          (exteriorSummandCellLift field index) point := by
    rw [exteriorHigherDerivative]
    exact (hasSum_sum_of_ne_finset_zero fun index outsideRange =>
      derivativeTailZero index (by simpa using outsideRange)).tsum_eq
  rw [tsumEquality, ← finiteDerivative, ← derivativeEquality]

theorem exteriorHigherDerivative_differentiableAt
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (outside : point ∈ strictExteriorRegion) :
    DifferentiableAt ℝ (exteriorHigherDerivative field order) point := by
  have eventuallyOutside : ∀ᶠ candidate in 𝓝 point,
      candidate ∈ strictExteriorRegion :=
    (isOpen_lt continuous_const
      (continuous_norm.comp continuous_planarPart)).mem_nhds outside
  have localEquality : exteriorHigherDerivative field order =ᶠ[𝓝 point]
      fun candidate =>
        iteratedFDeriv ℝ order (exteriorSeriesCellLift field) candidate := by
    filter_upwards [eventuallyOutside] with candidate candidateOutside
    exact exteriorHigherDerivative_eq_iteratedFDeriv
      field order candidate candidateOutside
  have smooth := exteriorSeriesCellLift_contDiffAt field point outside
  exact (smooth.differentiableAt_iteratedFDeriv
    (m := order) (WithTop.coe_lt_coe.mpr
      (show (order : ℕ∞) < ⊤ from WithTop.coe_lt_top order))).congr_of_eventuallyEq
        localEquality

theorem exteriorHigherDerivative_fderiv
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (outside : point ∈ strictExteriorRegion) :
    fderiv ℝ (exteriorHigherDerivative field order) point =
      (exteriorHigherDerivative field (order + 1) point).curryLeft := by
  have eventuallyOutside : ∀ᶠ candidate in 𝓝 point,
      candidate ∈ strictExteriorRegion :=
    (isOpen_lt continuous_const
      (continuous_norm.comp continuous_planarPart)).mem_nhds outside
  have localEquality : exteriorHigherDerivative field order =ᶠ[𝓝 point]
      fun candidate =>
        iteratedFDeriv ℝ order (exteriorSeriesCellLift field) candidate := by
    filter_upwards [eventuallyOutside] with candidate candidateOutside
    exact exteriorHigherDerivative_eq_iteratedFDeriv
      field order candidate candidateOutside
  rw [localEquality.fderiv_eq, fderiv_iteratedFDeriv]
  change (iteratedFDeriv ℝ (order + 1)
    (exteriorSeriesCellLift field) point).curryLeft =
      (exteriorHigherDerivative field (order + 1) point).curryLeft
  rw [← exteriorHigherDerivative_eq_iteratedFDeriv
    field (order + 1) point outside]

noncomputable def ambientHigherDerivative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ) (point : SpatialCell) :
    SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension :=
  if ‖planarPart point‖ ≤ 1 then
    closedHigherDerivative (order := order) field point
  else
    exteriorHigherDerivative field order point

theorem ambientHigherDerivative_continuousAt
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) :
    ContinuousAt (ambientHigherDerivative field order) point := by
  rcases lt_trichotomy ‖planarPart point‖ 1 with inside | boundary | outside
  · have eventuallyInside : ∀ᶠ candidate in 𝓝 point,
        ‖planarPart candidate‖ ≤ 1 := by
      filter_upwards [
        (isOpen_lt (continuous_norm.comp continuous_planarPart)
          continuous_const).mem_nhds inside] with candidate candidateInside
      exact candidateInside.le
    have equality : ambientHigherDerivative field order =ᶠ[𝓝 point]
        closedHigherDerivative (order := order) field := by
      filter_upwards [eventuallyInside] with candidate candidateInside
      rw [ambientHigherDerivative, if_pos candidateInside]
    exact ((closedHigherDerivative_continuous (order := order) field).continuousAt)
      |>.congr_of_eventuallyEq equality
  · have closedConvergence : Tendsto
        (closedHigherDerivative (order := order) field)
        (𝓝 point)
        (𝓝 (closedHigherDerivative (order := order) field point)) :=
      (closedHigherDerivative_continuous (order := order) field).continuousAt
    have exteriorConvergence :=
      exteriorHigherDerivative_tendsto_boundary field order point boundary
    have combined : Tendsto (ambientHigherDerivative field order)
        (𝓝 point)
        (𝓝 (closedHigherDerivative (order := order) field point)) := by
      rw [tendsto_def]
      intro target targetNeighborhood
      have exteriorTarget := exteriorConvergence targetNeighborhood
      change (exteriorHigherDerivative field order) ⁻¹' target ∈
        𝓝[strictExteriorRegion] point at exteriorTarget
      rw [mem_nhdsWithin_iff_exists_mem_nhds_inter] at exteriorTarget
      obtain ⟨source, sourceNeighborhood, sourceProperty⟩ := exteriorTarget
      have exteriorSource : ∀ᶠ candidate in 𝓝 point,
          candidate ∈ strictExteriorRegion →
            exteriorHigherDerivative field order candidate ∈ target :=
        Filter.Eventually.mono sourceNeighborhood
          (fun candidate candidateSource candidateOutside =>
            sourceProperty ⟨candidateSource, candidateOutside⟩)
      filter_upwards [closedConvergence targetNeighborhood, exteriorSource] with
        candidate closedTarget exteriorTarget
      change ambientHigherDerivative field order candidate ∈ target
      unfold ambientHigherDerivative
      split_ifs with candidateInside
      · exact closedTarget
      · exact exteriorTarget (not_le.mp candidateInside)
    change Tendsto (ambientHigherDerivative field order) (𝓝 point)
      (𝓝 (ambientHigherDerivative field order point))
    rw [ambientHigherDerivative, if_pos boundary.le]
    exact combined
  · have eventuallyOutside : ∀ᶠ candidate in 𝓝 point,
        candidate ∈ strictExteriorRegion :=
      (isOpen_lt continuous_const
        (continuous_norm.comp continuous_planarPart)).mem_nhds outside
    have equality : ambientHigherDerivative field order =ᶠ[𝓝 point]
        exteriorHigherDerivative field order := by
      filter_upwards [eventuallyOutside] with candidate candidateOutside
      rw [ambientHigherDerivative, if_neg (not_le.mpr candidateOutside)]
    exact (exteriorHigherDerivative_differentiableAt
      field order point outside).continuousAt.congr_of_eventuallyEq equality

theorem ambientHigherDerivative_continuous
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ) :
    Continuous (ambientHigherDerivative field order) :=
  continuous_iff_continuousAt.mpr
    (ambientHigherDerivative_continuousAt field order)

theorem ambientHigherDerivative_fderiv_inside
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (inside : ‖planarPart point‖ < 1) :
    fderiv ℝ (ambientHigherDerivative field order) point =
      (ambientHigherDerivative field (order + 1) point).curryLeft := by
  have eventuallyInside : ∀ᶠ candidate in 𝓝 point,
      ‖planarPart candidate‖ ≤ 1 := by
    filter_upwards [
      (isOpen_lt (continuous_norm.comp continuous_planarPart)
        continuous_const).mem_nhds inside] with candidate candidateInside
    exact candidateInside.le
  have localEquality : ambientHigherDerivative field order =ᶠ[𝓝 point]
      closedHigherDerivative (order := order) field := by
    filter_upwards [eventuallyInside] with candidate candidateInside
    rw [ambientHigherDerivative, if_pos candidateInside]
  rw [localEquality.fderiv_eq,
    closedHigherDerivative_fderiv_interior field point inside,
    ambientHigherDerivative, if_pos inside.le]

theorem ambientHigherDerivative_fderiv_outside
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (outside : point ∈ strictExteriorRegion) :
    fderiv ℝ (ambientHigherDerivative field order) point =
      (ambientHigherDerivative field (order + 1) point).curryLeft := by
  have eventuallyOutside : ∀ᶠ candidate in 𝓝 point,
      candidate ∈ strictExteriorRegion :=
    (isOpen_lt continuous_const
      (continuous_norm.comp continuous_planarPart)).mem_nhds outside
  have localEquality : ambientHigherDerivative field order =ᶠ[𝓝 point]
      exteriorHigherDerivative field order := by
    filter_upwards [eventuallyOutside] with candidate candidateOutside
    rw [ambientHigherDerivative, if_neg (not_le.mpr candidateOutside)]
  rw [localEquality.fderiv_eq,
    exteriorHigherDerivative_fderiv field order point outside,
    ambientHigherDerivative, if_neg (not_le.mpr outside)]

theorem ambientHigherDerivative_hasFDerivWithinAt_exteriorTangentClosure
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    HasFDerivWithinAt (ambientHigherDerivative field order)
      (closedHigherDerivative (order := order + 1) field point).curryLeft
      (closure (exteriorTangentBall point)) point := by
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
  · intro candidate membership
    have outside : candidate ∈ strictExteriorRegion :=
      exteriorTangentBall_subset_outerOpen point boundary membership
    have eventuallyOutside : ∀ᶠ other in 𝓝 candidate,
        other ∈ strictExteriorRegion :=
      (isOpen_lt continuous_const
        (continuous_norm.comp continuous_planarPart)).mem_nhds outside
    have localEquality : ambientHigherDerivative field order =ᶠ[𝓝 candidate]
        exteriorHigherDerivative field order := by
      filter_upwards [eventuallyOutside] with other otherOutside
      rw [ambientHigherDerivative, if_neg (not_le.mpr otherOutside)]
    exact (exteriorHigherDerivative_differentiableAt
      field order candidate outside).differentiableWithinAt.congr_of_eventuallyEq
        (localEquality.filter_mono inf_le_left) localEquality.eq_of_nhds
  · exact exteriorTangentBall_convex point
  · exact exteriorTangentBall_isOpen point
  · intro candidate _
    exact (ambientHigherDerivative_continuousAt
      field order candidate).continuousWithinAt
  · have filterBound : 𝓝[exteriorTangentBall point] point ≤
        𝓝[strictExteriorRegion] point := by
      exact nhdsWithin_mono point
        (exteriorTangentBall_subset_outerOpen point boundary)
    have convergence :=
      (exteriorHigherDerivative_tendsto_boundary
        field (order + 1) point boundary).mono_left filterBound
    have curriedConvergence : Tendsto (fun candidate =>
        (exteriorHigherDerivative field (order + 1) candidate).curryLeft)
        (𝓝[exteriorTangentBall point] point)
        (𝓝 (closedHigherDerivative
          (order := order + 1) field point).curryLeft) :=
      Filter.Tendsto.comp
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (order + 1) => SpatialCell)
          (ComplexEuclidean dimension)).continuous.continuousAt
        convergence
    apply curriedConvergence.congr'
    filter_upwards [self_mem_nhdsWithin] with candidate membership
    have outside := exteriorTangentBall_subset_outerOpen point boundary membership
    have derivativeEquality :=
      ambientHigherDerivative_fderiv_outside field order candidate outside
    rw [ambientHigherDerivative, if_neg (not_le.mpr outside)] at derivativeEquality
    exact derivativeEquality.symm

theorem ambientHigherDerivative_hasFDerivAt_inside
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (inside : ‖planarPart point‖ < 1) :
    HasFDerivAt (ambientHigherDerivative field order)
      (ambientHigherDerivative field (order + 1) point).curryLeft point := by
  have differentiable : DifferentiableAt ℝ
      (ambientHigherDerivative field order) point := by
    have eventuallyInside : ∀ᶠ candidate in 𝓝 point,
        ‖planarPart candidate‖ ≤ 1 := by
      filter_upwards [
        (isOpen_lt (continuous_norm.comp continuous_planarPart)
          continuous_const).mem_nhds inside] with candidate candidateInside
      exact candidateInside.le
    have localEquality : ambientHigherDerivative field order =ᶠ[𝓝 point]
        closedHigherDerivative (order := order) field := by
      filter_upwards [eventuallyInside] with candidate candidateInside
      rw [ambientHigherDerivative, if_pos candidateInside]
    exact (closedHigherDerivative_differentiableAt_interior
      field point inside).congr_of_eventuallyEq localEquality
  rw [← ambientHigherDerivative_fderiv_inside field order point inside]
  exact differentiable.hasFDerivAt

theorem ambientHigherDerivative_hasFDerivAt_outside
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (outside : point ∈ strictExteriorRegion) :
    HasFDerivAt (ambientHigherDerivative field order)
      (ambientHigherDerivative field (order + 1) point).curryLeft point := by
  have differentiable : DifferentiableAt ℝ
      (ambientHigherDerivative field order) point := by
    have eventuallyOutside : ∀ᶠ candidate in 𝓝 point,
        candidate ∈ strictExteriorRegion :=
      (isOpen_lt continuous_const
        (continuous_norm.comp continuous_planarPart)).mem_nhds outside
    have localEquality : ambientHigherDerivative field order =ᶠ[𝓝 point]
        exteriorHigherDerivative field order := by
      filter_upwards [eventuallyOutside] with candidate candidateOutside
      rw [ambientHigherDerivative, if_neg (not_le.mpr candidateOutside)]
    exact (exteriorHigherDerivative_differentiableAt
      field order point outside).congr_of_eventuallyEq localEquality
  rw [← ambientHigherDerivative_fderiv_outside field order point outside]
  exact differentiable.hasFDerivAt

theorem ambientHigherDerivative_hasDerivAt_radial_boundary
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    HasDerivAt (ambientHigherDerivative field order ∘ radialSpatialLine point)
      ((closedHigherDerivative (order := order + 1) field point).curryLeft
        (radialSpatialDirection point)) 0 := by
  have lineDerivative := radialSpatialLine_hasDerivAt point
  have rightAmbient : HasDerivWithinAt
      (ambientHigherDerivative field order ∘ radialSpatialLine point)
      ((closedHigherDerivative (order := order + 1) field point).curryLeft
        (radialSpatialDirection point)) (Icc (0 : ℝ) 1) 0 :=
    (ambientHigherDerivative_hasFDerivWithinAt_exteriorTangentClosure
      field order point boundary).comp_hasDerivWithinAt_of_eq
        0 lineDerivative.hasDerivWithinAt
          (radialSpatialLine_right_mapsTo_tangentClosure point boundary)
          (by simp [radialSpatialLine])
  have leftClosed : HasDerivWithinAt
      (closedHigherDerivative (order := order) field ∘ radialSpatialLine point)
      ((closedHigherDerivative (order := order + 1) field point).curryLeft
        (radialSpatialDirection point)) (Icc (-(1 / 2 : ℝ)) 0) 0 :=
    (closedHigherDerivative_hasFDerivWithinAt_closed
      (order := order) field point).comp_hasDerivWithinAt_of_eq
        0 lineDerivative.hasDerivWithinAt
          (radialSpatialLine_left_mapsTo_closedCylinder point boundary)
          (by simp [radialSpatialLine])
  have leftAmbient : HasDerivWithinAt
      (ambientHigherDerivative field order ∘ radialSpatialLine point)
      ((closedHigherDerivative (order := order + 1) field point).curryLeft
        (radialSpatialDirection point)) (Icc (-(1 / 2 : ℝ)) 0) 0 := by
    apply leftClosed.congr
    · intro scale scaleMembership
      have membership := radialSpatialLine_left_mapsTo_closedCylinder
        point boundary scaleMembership
      change ‖planarPart (radialSpatialLine point scale)‖ ≤ 1 at membership
      change ambientHigherDerivative field order (radialSpatialLine point scale) =
        closedHigherDerivative (order := order) field
          (radialSpatialLine point scale)
      rw [ambientHigherDerivative, if_pos membership]
    · simp [ambientHigherDerivative, radialSpatialLine, boundary]
  have unionDerivative := leftAmbient.union rightAmbient
  apply unionDerivative.hasDerivAt
  apply Filter.mem_of_superset
    (Ioo_mem_nhds (by norm_num : (-(1 / 2 : ℝ)) < 0)
      (by norm_num : (0 : ℝ) < 1))
  intro scale scaleMembership
  by_cases nonpositive : scale ≤ 0
  · exact Or.inl ⟨scaleMembership.1.le, nonpositive⟩
  · exact Or.inr ⟨le_of_not_ge nonpositive, scaleMembership.2.le⟩

theorem ambientHigherDerivative_boundaryRadialSegment_hasDerivAt_zero
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (nonzero : planarPart point ≠ 0) :
    HasDerivAt (ambientHigherDerivative field order ∘ boundaryRadialSegment point)
      ((closedHigherDerivative (order := order + 1) field
        (normalizedSpatialCell point)).curryLeft
          (point - normalizedSpatialCell point)) 0 := by
  have normalizedBoundary := normalizedSpatialCell_norm point nonzero
  have radialDerivative :=
    ambientHigherDerivative_hasDerivAt_radial_boundary field order
      (normalizedSpatialCell point) normalizedBoundary
  have scaleDerivative : HasDerivAt
      (fun parameter : ℝ => parameter * (‖planarPart point‖ - 1))
      (‖planarPart point‖ - 1) 0 := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id (x := (0 : ℝ))).mul_const
        (‖planarPart point‖ - 1)
  have composed := radialDerivative.scomp_of_eq 0 scaleDerivative
    (zero_mul (‖planarPart point‖ - 1)).symm
  have functionEquality :
      (ambientHigherDerivative field order ∘ boundaryRadialSegment point) =
        (ambientHigherDerivative field order ∘
          radialSpatialLine (normalizedSpatialCell point)) ∘
            (fun parameter : ℝ => parameter * (‖planarPart point‖ - 1)) := by
    funext parameter
    simp only [Function.comp_apply]
    rw [boundaryRadialSegment_eq_radialSpatialLine point nonzero parameter]
  have derivativeEquality :
      (‖planarPart point‖ - 1) •
          (closedHigherDerivative (order := order + 1) field
            (normalizedSpatialCell point)).curryLeft
              (radialSpatialDirection (normalizedSpatialCell point)) =
        (closedHigherDerivative (order := order + 1) field
          (normalizedSpatialCell point)).curryLeft
            (point - normalizedSpatialCell point) := by
    rw [← map_smul,
      radialSpatialDirection_normalized_smul point nonzero]
  rw [functionEquality, ← derivativeEquality]
  exact composed

theorem ambientHigherDerivative_boundaryRadialSegment_hasDerivAt_inside
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (nonzero : planarPart point ≠ 0)
    (inside : ‖planarPart point‖ < 1) {parameter : ℝ}
    (parameterPositive : 0 < parameter) (parameterUpper : parameter ≤ 1) :
    HasDerivAt (ambientHigherDerivative field order ∘ boundaryRadialSegment point)
      ((ambientHigherDerivative field (order + 1)
        (boundaryRadialSegment point parameter)).curryLeft
          (point - normalizedSpatialCell point)) parameter := by
  exact (ambientHigherDerivative_hasFDerivAt_inside field order
    (boundaryRadialSegment point parameter)
    (boundaryRadialSegment_mem_openUnitCylinder point nonzero inside
      parameterPositive parameterUpper)).comp_hasDerivAt parameter
        (boundaryRadialSegment_hasDerivAt point parameter)

theorem ambientHigherDerivative_boundaryRadialSegment_hasDerivAt_outside
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (nonzero : planarPart point ≠ 0)
    (outside : 1 < ‖planarPart point‖) {parameter : ℝ}
    (parameterPositive : 0 < parameter) :
    HasDerivAt (ambientHigherDerivative field order ∘ boundaryRadialSegment point)
      ((ambientHigherDerivative field (order + 1)
        (boundaryRadialSegment point parameter)).curryLeft
          (point - normalizedSpatialCell point)) parameter := by
  exact (ambientHigherDerivative_hasFDerivAt_outside field order
    (boundaryRadialSegment point parameter)
    (boundaryRadialSegment_mem_outerOpen point nonzero outside
      parameterPositive)).comp_hasDerivAt parameter
        (boundaryRadialSegment_hasDerivAt point parameter)

theorem ambientHigherDerivative_comp_normalized_hasFDerivAt_boundary
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    HasFDerivAt (ambientHigherDerivative field order ∘ normalizedSpatialCell)
      ((closedHigherDerivative (order := order + 1) field point).curryLeft.comp
        (fderiv ℝ normalizedSpatialCell point)) point := by
  have nonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  have closedComposition :=
    (closedHigherDerivative_hasFDerivWithinAt_closed
      (order := order) field point).comp_hasFDerivAt_of_eq point
        (normalizedSpatialCell_hasFDerivAt point nonzero)
        (eventually_normalizedSpatialCell_mem_closedUnitCylinder point nonzero)
        (normalizedSpatialCell_boundary point boundary).symm
  apply closedComposition.congr_of_eventuallyEq
  filter_upwards [eventually_normalizedSpatialCell_mem_closedUnitCylinder
    point nonzero] with candidate membership
  change ambientHigherDerivative field order (normalizedSpatialCell candidate) =
    closedHigherDerivative (order := order) field
      (normalizedSpatialCell candidate)
  rw [ambientHigherDerivative, if_pos]
  exact membership

def ambientHigherRadialRemainder {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ)
    (boundaryPoint point : SpatialCell) :
    SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension :=
  ambientHigherDerivative field order point -
      ambientHigherDerivative field order (normalizedSpatialCell point) -
    (closedHigherDerivative (order := order + 1) field boundaryPoint).curryLeft
      (point - normalizedSpatialCell point)

theorem ambientHigherRadialRemainder_norm_le
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (boundaryPoint point : SpatialCell) (pointNonzero : planarPart point ≠ 0)
    (pointNonboundary : ‖planarPart point‖ ≠ 1) (epsilon : ℝ)
    (derivativeBound : ∀ parameter ∈ Icc (0 : ℝ) 1,
      ‖(ambientHigherDerivative field (order + 1)
          (boundaryRadialSegment point parameter)).curryLeft -
        (closedHigherDerivative (order := order + 1) field
          boundaryPoint).curryLeft‖ ≤ epsilon) :
    ‖ambientHigherRadialRemainder field order boundaryPoint point‖ ≤
      epsilon * ‖point - normalizedSpatialCell point‖ := by
  let targetDerivative :=
    (closedHigherDerivative (order := order + 1) field boundaryPoint).curryLeft
  let direction := point - normalizedSpatialCell point
  let corrected : ℝ →
      SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension := fun parameter =>
    ambientHigherDerivative field order (boundaryRadialSegment point parameter) -
      targetDerivative (boundaryRadialSegment point parameter)
  let correctedDerivative : ℝ →
      SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension := fun parameter =>
    ((ambientHigherDerivative field (order + 1)
      (boundaryRadialSegment point parameter)).curryLeft - targetDerivative)
        direction
  have correctedHasDerivative : ∀ parameter ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt corrected (correctedDerivative parameter)
        (Icc (0 : ℝ) 1) parameter := by
    intro parameter parameterMembership
    have linearDerivative : HasDerivAt
        (fun parameter => targetDerivative (boundaryRadialSegment point parameter))
        (targetDerivative direction) parameter :=
      targetDerivative.hasFDerivAt.comp_hasDerivAt parameter
        (boundaryRadialSegment_hasDerivAt point parameter)
    by_cases parameterZero : parameter = 0
    · subst parameter
      have ambientDerivative :=
        ambientHigherDerivative_boundaryRadialSegment_hasDerivAt_zero
          field order point pointNonzero
      have differenceDerivative := ambientDerivative.sub linearDerivative
      dsimp only [corrected, correctedDerivative, targetDerivative, direction]
      rw [boundaryRadialSegment_zero, ambientHigherDerivative, if_pos]
      · change HasDerivWithinAt
          ((ambientHigherDerivative field order ∘ boundaryRadialSegment point) -
            fun parameter =>
              (closedHigherDerivative (order := order + 1) field
                boundaryPoint).curryLeft
                  (boundaryRadialSegment point parameter))
          (((closedHigherDerivative (order := order + 1) field
                (normalizedSpatialCell point)).curryLeft -
              (closedHigherDerivative (order := order + 1) field
                boundaryPoint).curryLeft)
            (point - normalizedSpatialCell point)) (Icc (0 : ℝ) 1) 0
        exact differenceDerivative.hasDerivWithinAt
      · exact (normalizedSpatialCell_norm point pointNonzero).le
    · have parameterPositive : 0 < parameter :=
        lt_of_le_of_ne parameterMembership.1 (Ne.symm parameterZero)
      have ambientDerivative : HasDerivAt
          (ambientHigherDerivative field order ∘ boundaryRadialSegment point)
          ((ambientHigherDerivative field (order + 1)
            (boundaryRadialSegment point parameter)).curryLeft direction)
          parameter := by
        rcases lt_or_gt_of_ne pointNonboundary with inside | outside
        · exact ambientHigherDerivative_boundaryRadialSegment_hasDerivAt_inside
            field order point pointNonzero inside parameterPositive
              parameterMembership.2
        · exact ambientHigherDerivative_boundaryRadialSegment_hasDerivAt_outside
            field order point pointNonzero outside parameterPositive
      have differenceDerivative := ambientDerivative.sub linearDerivative
      dsimp only [corrected, correctedDerivative]
      change HasDerivWithinAt
        ((ambientHigherDerivative field order ∘ boundaryRadialSegment point) -
          fun parameter => targetDerivative (boundaryRadialSegment point parameter))
        (((ambientHigherDerivative field (order + 1)
            (boundaryRadialSegment point parameter)).curryLeft -
          targetDerivative) direction) (Icc (0 : ℝ) 1) parameter
      exact differenceDerivative.hasDerivWithinAt
  have derivativeNormBound : ∀ parameter ∈ Ico (0 : ℝ) 1,
      ‖correctedDerivative parameter‖ ≤ epsilon * ‖direction‖ := by
    intro parameter parameterMembership
    dsimp only [correctedDerivative]
    calc
      ‖((ambientHigherDerivative field (order + 1)
            (boundaryRadialSegment point parameter)).curryLeft -
          targetDerivative) direction‖ ≤
          ‖(ambientHigherDerivative field (order + 1)
              (boundaryRadialSegment point parameter)).curryLeft -
            targetDerivative‖ * ‖direction‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ epsilon * ‖direction‖ :=
        mul_le_mul_of_nonneg_right
          (derivativeBound parameter
            (Ico_subset_Icc_self parameterMembership)) (norm_nonneg _)
  have meanValue := norm_image_sub_le_of_norm_deriv_le_segment_01'
    correctedHasDerivative derivativeNormBound
  change ‖corrected 1 - corrected 0‖ ≤ epsilon * ‖direction‖ at meanValue
  calc
    ‖ambientHigherRadialRemainder field order boundaryPoint point‖ =
        ‖corrected 1 - corrected 0‖ := by
      dsimp only [ambientHigherRadialRemainder, corrected,
        targetDerivative, direction]
      rw [boundaryRadialSegment_one, boundaryRadialSegment_zero, map_sub]
      congr 1
      abel
    _ ≤ epsilon * ‖direction‖ := meanValue

theorem ambientHigherRadialRemainder_isLittleO
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (boundaryPoint : SpatialCell)
    (boundary : ‖planarPart boundaryPoint‖ = 1) :
    (fun point => ambientHigherRadialRemainder
      field order boundaryPoint point) =o[𝓝 boundaryPoint]
      (fun point => point - boundaryPoint) := by
  rw [Asymptotics.isLittleO_iff]
  intro constant constantPositive
  let geometryConstant : ℝ := ‖assembleSpatialCellCLM‖ * ‖planarPartCLM‖
  have geometryNonnegative : 0 ≤ geometryConstant :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let epsilon : ℝ := constant / (geometryConstant + 1)
  have denominatorPositive : 0 < geometryConstant + 1 := by linarith
  have epsilonPositive : 0 < epsilon :=
    div_pos constantPositive denominatorPositive
  have coefficientBound : epsilon * geometryConstant ≤ constant := by
    dsimp only [epsilon]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ denominatorPositive).2
    nlinarith
  have curriedContinuous : Continuous (fun point =>
      (ambientHigherDerivative field (order + 1) point).curryLeft) :=
    (continuousMultilinearCurryLeftEquiv ℝ
      (fun _ : Fin (order + 1) => SpatialCell)
      (ComplexEuclidean dimension)).continuous.comp
        (ambientHigherDerivative_continuous field (order + 1))
  have derivativeEvent : ∀ᶠ point in 𝓝 boundaryPoint,
      ‖(ambientHigherDerivative field (order + 1) point).curryLeft -
        (closedHigherDerivative (order := order + 1) field
          boundaryPoint).curryLeft‖ < epsilon := by
    have convergence : Tendsto (fun point =>
        ‖(ambientHigherDerivative field (order + 1) point).curryLeft -
          (closedHigherDerivative (order := order + 1) field
            boundaryPoint).curryLeft‖)
        (𝓝 boundaryPoint) (𝓝 0) := by
      have constantConvergence : Tendsto
          (fun _ : SpatialCell =>
            (closedHigherDerivative (order := order + 1) field
              boundaryPoint).curryLeft)
          (𝓝 boundaryPoint)
          (𝓝 (closedHigherDerivative (order := order + 1) field
            boundaryPoint).curryLeft) := tendsto_const_nhds
      have differenceConvergence :=
        (curriedContinuous.continuousAt.sub constantConvergence).norm
      change Tendsto (fun point =>
        ‖(ambientHigherDerivative field (order + 1) point).curryLeft -
          (closedHigherDerivative (order := order + 1) field
            boundaryPoint).curryLeft‖)
        (𝓝 boundaryPoint)
        (𝓝 ‖(ambientHigherDerivative field (order + 1)
          boundaryPoint).curryLeft -
            (closedHigherDerivative (order := order + 1) field
              boundaryPoint).curryLeft‖) at differenceConvergence
      rw [ambientHigherDerivative, if_pos boundary.le,
        sub_self, norm_zero] at differenceConvergence
      exact differenceConvergence
    exact convergence.eventually (Iio_mem_nhds epsilonPositive)
  obtain ⟨radius, radiusPositive, ballDerivativeBound⟩ :=
    Metric.eventually_nhds_iff.mp derivativeEvent
  have boundaryNonzero : planarPart boundaryPoint ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  have normalizedTendsto : Tendsto normalizedSpatialCell
      (𝓝 boundaryPoint) (𝓝 boundaryPoint) := by
    have convergence :=
      (normalizedSpatialCell_contDiffAt
        boundaryPoint boundaryNonzero).continuousAt
    change Tendsto normalizedSpatialCell (𝓝 boundaryPoint)
      (𝓝 (normalizedSpatialCell boundaryPoint)) at convergence
    rw [normalizedSpatialCell_boundary boundaryPoint boundary] at convergence
    exact convergence
  have eventuallyNormalizedInBall : ∀ᶠ point in 𝓝 boundaryPoint,
      normalizedSpatialCell point ∈ Metric.ball boundaryPoint radius :=
    normalizedTendsto.eventually (Metric.ball_mem_nhds _ radiusPositive)
  have eventuallyPointInBall : ∀ᶠ point in 𝓝 boundaryPoint,
      point ∈ Metric.ball boundaryPoint radius :=
    Metric.ball_mem_nhds _ radiusPositive
  have eventuallyPointNonzero : ∀ᶠ point in 𝓝 boundaryPoint,
      planarPart point ≠ 0 :=
    continuous_planarPart.continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds boundaryNonzero)
  filter_upwards [eventuallyNormalizedInBall, eventuallyPointInBall,
    eventuallyPointNonzero] with point normalizedInBall pointInBall pointNonzero
  by_cases pointBoundary : ‖planarPart point‖ = 1
  · have normalizedEquality := normalizedSpatialCell_boundary point pointBoundary
    simp [ambientHigherRadialRemainder, normalizedEquality]
    exact mul_nonneg constantPositive.le (norm_nonneg _)
  · have radialEstimate :
        ‖ambientHigherRadialRemainder field order boundaryPoint point‖ ≤
          epsilon * ‖point - normalizedSpatialCell point‖ := by
      apply ambientHigherRadialRemainder_norm_le field order
        boundaryPoint point pointNonzero pointBoundary epsilon
      intro parameter parameterMembership
      exact (ballDerivativeBound
        (boundaryRadialSegment_mem_ball parameterMembership
          normalizedInBall pointInBall)).le
    calc
      ‖ambientHigherRadialRemainder field order boundaryPoint point‖ ≤
          epsilon * ‖point - normalizedSpatialCell point‖ := radialEstimate
      _ ≤ epsilon * (geometryConstant * ‖point - boundaryPoint‖) := by
        exact mul_le_mul_of_nonneg_left
          (point_sub_normalized_norm_le_boundary
            point boundaryPoint pointNonzero boundary) epsilonPositive.le
      _ = (epsilon * geometryConstant) * ‖point - boundaryPoint‖ := by ring
      _ ≤ constant * ‖point - boundaryPoint‖ :=
        mul_le_mul_of_nonneg_right coefficientBound (norm_nonneg _)

theorem ambientHigherDerivative_hasFDerivAt_boundary
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) (boundary : ‖planarPart point‖ = 1) :
    HasFDerivAt (ambientHigherDerivative field order)
      (closedHigherDerivative (order := order + 1) field point).curryLeft point := by
  have nonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  let normalizationDerivative := fderiv ℝ normalizedSpatialCell point
  let targetDerivative :=
    (closedHigherDerivative (order := order + 1) field point).curryLeft
  have baseDerivative : HasFDerivAt
      (ambientHigherDerivative field order ∘ normalizedSpatialCell)
      (targetDerivative.comp normalizationDerivative) point :=
    ambientHigherDerivative_comp_normalized_hasFDerivAt_boundary
      field order point boundary
  have normalizedTargetDerivative : HasFDerivAt
      (targetDerivative ∘ normalizedSpatialCell)
      (targetDerivative.comp normalizationDerivative) point :=
    targetDerivative.hasFDerivAt.comp point
      (normalizedSpatialCell_hasFDerivAt point nonzero)
  have radialRemainder :=
    ambientHigherRadialRemainder_isLittleO field order point boundary
  have combinedRemainder :=
    (radialRemainder.add baseDerivative.isLittleO).sub
      normalizedTargetDerivative.isLittleO
  apply HasFDerivAt.of_isLittleO
  apply combinedRemainder.congr_left
  intro candidate
  dsimp only [ambientHigherRadialRemainder, Function.comp_apply,
    targetDerivative]
  rw [show normalizedSpatialCell point = point from
    normalizedSpatialCell_boundary point boundary]
  simp only [ContinuousLinearMap.comp_apply, map_sub]
  abel

theorem ambientHigherDerivative_hasFDerivAt
    {dimension : ℕ} (field : DiskCellClosedJet dimension) (order : ℕ)
    (point : SpatialCell) :
    HasFDerivAt (ambientHigherDerivative field order)
      (ambientHigherDerivative field (order + 1) point).curryLeft point := by
  rcases lt_trichotomy ‖planarPart point‖ 1 with inside | boundary | outside
  · exact ambientHigherDerivative_hasFDerivAt_inside
      field order point inside
  · rw [ambientHigherDerivative, if_pos boundary.le]
    exact ambientHigherDerivative_hasFDerivAt_boundary
      field order point boundary
  · exact ambientHigherDerivative_hasFDerivAt_outside
      field order point outside

noncomputable def ambientTaylorSeries {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    FormalMultilinearSeries ℝ SpatialCell (ComplexEuclidean dimension) :=
  fun order => ambientHigherDerivative field order point

theorem ambientHigherDerivative_zero_curry
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (point : SpatialCell) :
    (ambientHigherDerivative field 0 point).curry0 =
      ambientExtensionCellLift field point := by
  by_cases inside : ‖planarPart point‖ ≤ 1
  · rw [ambientHigherDerivative, if_pos inside,
      closedHigherDerivative_zero_curry,
      ← diskCellLift_eq_retractedDiskCell field point inside,
      ← ambientExtensionCellLift_eq_diskCellLift field point inside]
  · have outside : point ∈ strictExteriorRegion := not_le.mp inside
    rw [ambientHigherDerivative, if_neg inside,
      exteriorHigherDerivative_eq_iteratedFDeriv field 0 point outside,
      ContinuousMultilinearMap.curry0_apply]
    exact (ambientExtensionCellLift_eq_exteriorSeries
      field point outside.le).symm

theorem ambientExtensionCellLift_hasFTaylorSeriesUpTo
    {dimension : ℕ} (field : DiskCellClosedJet dimension) :
    HasFTaylorSeriesUpTo (𝕜 := ℝ) ∞ (ambientExtensionCellLift field)
      (ambientTaylorSeries field) := by
  rw [← hasFTaylorSeriesUpToOn_univ_iff]
  constructor
  · intro point _
    exact ambientHigherDerivative_zero_curry field point
  · intro order _ point _
    exact (ambientHigherDerivative_hasFDerivAt
      field order point).hasFDerivWithinAt
  · intro order _
    exact (ambientHigherDerivative_continuous field order).continuousOn

theorem ambientExtensionCellLift_contDiff_infty
    {dimension : ℕ} (field : DiskCellClosedJet dimension) :
    ContDiff ℝ ∞ (ambientExtensionCellLift field) :=
  (ambientExtensionCellLift_hasFTaylorSeriesUpTo field).contDiff

theorem ambientHigherDerivative_eq_iteratedFDeriv_ambient
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (order : ℕ) (point : SpatialCell) :
    ambientHigherDerivative field order point =
      iteratedFDeriv ℝ order (ambientExtensionCellLift field) point := by
  have coefficientEquality :=
    (ambientExtensionCellLift_hasFTaylorSeriesUpTo field).eq_iteratedFDeriv
      (m := order)
      (WithTop.coe_le_coe.mpr
        (show (order : ℕ∞) ≤ ⊤ from le_top))
  exact coefficientEquality point

theorem mixedCartesianDerivative_boundary_all_orders
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (point : SpatialCell) (boundary : ‖planarPart point‖ = 1)
    (order : ℕ) (word : MixedCartesianWord order) :
    mixedCartesianDerivative order word (ambientExtensionCellLift field) point =
      closedMixedDerivative field order word
        (diskCellPoint point (by
          change ‖planarPart point‖ ≤ 1
          exact boundary.le)) := by
  rw [mixedCartesianDerivative,
    ← ambientHigherDerivative_eq_iteratedFDeriv_ambient field order point,
    ambientHigherDerivative, if_pos boundary.le,
    closedHigherDerivative_basis,
    retractedDiskCell_eq_diskCellPoint point boundary.le]

end Grad.DiskExtension.Operator
