import P0910AllOrderSeam

noncomputable section

open Filter Set
open scoped ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets

def localPeriodicCoordinate (base candidate : SpatialCell) (coordinate : Fin 2) : ℝ :=
  planarPart candidate coordinate - planarPart base coordinate +
    (AddCircle.equivIco (4 : ℝ) (-2)
      (planarPart base coordinate : SpatialCircle)).val

theorem coe_localPeriodicCoordinate (base candidate : SpatialCell)
    (coordinate : Fin 2) :
    ((localPeriodicCoordinate base candidate coordinate : ℝ) : SpatialCircle) =
      (planarPart candidate coordinate : SpatialCircle) := by
  rw [localPeriodicCoordinate]
  change QuotientAddGroup.mk' (AddSubgroup.zmultiples (4 : ℝ))
      (planarPart candidate coordinate - planarPart base coordinate +
        (AddCircle.equivIco (4 : ℝ) (-2)
          (planarPart base coordinate : SpatialCircle)).val) =
    QuotientAddGroup.mk' (AddSubgroup.zmultiples (4 : ℝ))
      (planarPart candidate coordinate)
  rw [map_add, map_sub]
  have representativeEquality :
      (((AddCircle.equivIco (4 : ℝ) (-2)
        (planarPart base coordinate : SpatialCircle)).val : ℝ) : SpatialCircle) =
        (planarPart base coordinate : SpatialCircle) :=
    AddCircle.coe_equivIco
  change QuotientAddGroup.mk' (AddSubgroup.zmultiples (4 : ℝ))
      ((AddCircle.equivIco (4 : ℝ) (-2)
        (planarPart base coordinate : SpatialCircle)).val) =
    QuotientAddGroup.mk' (AddSubgroup.zmultiples (4 : ℝ))
      (planarPart base coordinate) at representativeEquality
  rw [representativeEquality]
  abel

def localPeriodizationOffset (base : SpatialCell) : SpatialCell :=
  assembleSpatialCell
    (WithLp.toLp 2 ![
      (AddCircle.equivIco (4 : ℝ) (-2)
        (planarPart base 0 : SpatialCircle)).val - planarPart base 0,
      (AddCircle.equivIco (4 : ℝ) (-2)
        (planarPart base 1 : SpatialCircle)).val - planarPart base 1])
    0

def localPeriodizationChart (base candidate : SpatialCell) : SpatialCell :=
  candidate + localPeriodizationOffset base

theorem planarPart_localPeriodizationChart (base candidate : SpatialCell)
    (coordinate : Fin 2) :
    planarPart (localPeriodizationChart base candidate) coordinate =
      localPeriodicCoordinate base candidate coordinate := by
  fin_cases coordinate <;>
    simp [localPeriodizationChart, localPeriodizationOffset,
      localPeriodicCoordinate, assembleSpatialCell, planarPart] <;> ring

theorem localPeriodizationChart_cell (base candidate : SpatialCell) :
    localPeriodizationChart base candidate 2 = candidate 2 := by
  simp [localPeriodizationChart, localPeriodizationOffset, assembleSpatialCell]

theorem localPeriodizationChart_contDiff (base : SpatialCell) :
    ContDiff ℝ ∞ (localPeriodizationChart base) := by
  exact contDiff_id.add contDiff_const

def periodizedSpatialCellRepresentative (point : SpatialCell) : SpatialCell :=
  assembleSpatialCell
    (spatialTorusRepresentative
      ((planarPart point 0 : SpatialCircle),
        (planarPart point 1 : SpatialCircle)))
    (point 2)

theorem equivIco_mem_Ioo_of_ne (point : SpatialCircle)
    (nonseam : point ≠ ((-2 : ℝ) : SpatialCircle)) :
    (AddCircle.equivIco (4 : ℝ) (-2) point).val ∈
      Ioo (-2 : ℝ) (-2 + 4) := by
  have lower : (-2 : ℝ) ≤
      (AddCircle.equivIco (4 : ℝ) (-2) point).val :=
    (AddCircle.equivIco (4 : ℝ) (-2) point).property.1
  have notLower :
      (AddCircle.equivIco (4 : ℝ) (-2) point).val ≠ (-2 : ℝ) := by
    intro equality
    apply nonseam
    rw [← AddCircle.coe_equivIco (p := (4 : ℝ)) (a := (-2 : ℝ))
      (y := point)]
    exact congrArg (fun value : ℝ => (value : SpatialCircle)) equality
  refine ⟨lt_of_le_of_ne lower ?_, ?_⟩
  · exact Ne.symm notLower
  · exact (AddCircle.equivIco (4 : ℝ) (-2) point).property.2

theorem eventually_localPeriodicCoordinate_mem_Ico
    (base : SpatialCell) (coordinate : Fin 2)
    (nonseam : (planarPart base coordinate : SpatialCircle) ≠
      ((-2 : ℝ) : SpatialCircle)) :
    ∀ᶠ candidate in 𝓝 base,
      localPeriodicCoordinate base candidate coordinate ∈
        Ico (-2 : ℝ) (-2 + 4) := by
  have coordinateContinuous : Continuous
      (fun candidate => localPeriodicCoordinate base candidate coordinate) := by
    rw [← funext (planarPart_localPeriodizationChart base · coordinate)]
    exact (PiLp.continuous_apply 2 _ coordinate).comp
      (continuous_planarPart.comp (localPeriodizationChart_contDiff base).continuous)
  have baseMembership : localPeriodicCoordinate base base coordinate ∈
      Ioo (-2 : ℝ) (-2 + 4) := by
    simpa [localPeriodicCoordinate] using
      equivIco_mem_Ioo_of_ne (planarPart base coordinate : SpatialCircle) nonseam
  filter_upwards [coordinateContinuous.continuousAt.eventually
    (Ioo_mem_nhds baseMembership.1 baseMembership.2)]
      with candidate candidateMembership
  exact Ioo_subset_Ico_self candidateMembership

theorem eventually_periodizedSpatialCellRepresentative_eq_chart
    (base : SpatialCell)
    (firstNonseam : (planarPart base 0 : SpatialCircle) ≠
      ((-2 : ℝ) : SpatialCircle))
    (secondNonseam : (planarPart base 1 : SpatialCircle) ≠
      ((-2 : ℝ) : SpatialCircle)) :
    ∀ᶠ candidate in 𝓝 base,
      periodizedSpatialCellRepresentative candidate =
        localPeriodizationChart base candidate := by
  filter_upwards [eventually_localPeriodicCoordinate_mem_Ico base 0 firstNonseam,
    eventually_localPeriodicCoordinate_mem_Ico base 1 secondNonseam]
      with candidate firstMembership secondMembership
  ext coordinate
  fin_cases coordinate
  · change (AddCircle.equivIco (4 : ℝ) (-2)
      (planarPart candidate 0 : SpatialCircle)).val =
        planarPart (localPeriodizationChart base candidate) 0
    rw [planarPart_localPeriodizationChart]
    rw [← coe_localPeriodicCoordinate base candidate 0]
    exact congrArg Subtype.val
      (AddCircle.equivIco_coe_eq firstMembership)
  · change (AddCircle.equivIco (4 : ℝ) (-2)
      (planarPart candidate 1 : SpatialCircle)).val =
        planarPart (localPeriodizationChart base candidate) 1
    rw [planarPart_localPeriodizationChart]
    rw [← coe_localPeriodicCoordinate base candidate 1]
    exact congrArg Subtype.val
      (AddCircle.equivIco_coe_eq secondMembership)
  · exact localPeriodizationChart_cell base candidate |>.symm

def periodizedExtensionValue {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    ContinuousMap TorusCellDomain (ComplexEuclidean dimension) where
  toFun := periodizedExtensionFromValue field.value
  continuous_toFun := periodizedExtensionFromValue_continuous field

@[simp] theorem periodizedExtensionValue_apply {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : TorusCellDomain) :
    periodizedExtensionValue field point =
      periodizedExtensionFromValue field.value point := rfl

theorem torusCellLift_periodizedExtensionValue {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    torusCellLift (periodizedExtensionValue field) point =
      ambientExtensionCellLift field
        (periodizedSpatialCellRepresentative point) := by
  rw [torusCellLift, periodizedExtensionValue_apply,
    periodizedExtensionFromValue, ambientExtensionCellLift,
    periodizedSpatialCellRepresentative, planarPart_assembleSpatialCell]
  rfl

theorem spatialRepresentativeAbs_comp_continuous (coordinate : Fin 2) :
    Continuous (fun point : SpatialCell =>
      spatialRepresentativeAbs
        (planarPart point coordinate : SpatialCircle)) := by
  exact spatialRepresentativeAbs_continuous.comp
    ((AddCircle.continuous_mk' (4 : ℝ)).comp
      ((PiLp.continuous_apply 2 _ coordinate).comp continuous_planarPart))

theorem eventually_torusCellLift_periodized_eq_zero_of_seam
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (base : SpatialCell) (coordinate : Fin 2)
    (seam : (planarPart base coordinate : SpatialCircle) =
      ((-2 : ℝ) : SpatialCircle)) :
    torusCellLift (periodizedExtensionValue field) =ᶠ[𝓝 base]
      (0 : SpatialCell → ComplexEuclidean dimension) := by
  have atPoint : outerSupportRadius <
      spatialRepresentativeAbs
        (planarPart base coordinate : SpatialCircle) := by
    rw [seam, spatialRepresentativeAbs_seam, collar_constants.2.2.2.2]
    norm_num
  have neighborhood : ∀ᶠ candidate in 𝓝 base,
      outerSupportRadius < spatialRepresentativeAbs
        (planarPart candidate coordinate : SpatialCircle) :=
    (spatialRepresentativeAbs_comp_continuous coordinate).continuousAt.eventually
      (Ioi_mem_nhds atPoint)
  filter_upwards [neighborhood] with candidate candidateBound
  rw [torusCellLift_periodizedExtensionValue, ambientExtensionCellLift]
  apply ambientExtension_zero_of_support
  rw [periodizedSpatialCellRepresentative, planarPart_assembleSpatialCell]
  fin_cases coordinate
  · exact candidateBound.le.trans
      (spatialPlane_coordinate_abs_le_norm
        (spatialTorusRepresentative
          ((planarPart candidate 0 : SpatialCircle),
            (planarPart candidate 1 : SpatialCircle))) 0)
  · exact candidateBound.le.trans
      (spatialPlane_coordinate_abs_le_norm
        (spatialTorusRepresentative
          ((planarPart candidate 0 : SpatialCircle),
            (planarPart candidate 1 : SpatialCircle))) 1)

theorem torusCellLift_periodizedExtensionValue_contDiff
    {dimension : ℕ} (field : DiskCellClosedJet dimension) :
    ContDiff ℝ ∞ (torusCellLift (periodizedExtensionValue field)) := by
  rw [contDiff_iff_contDiffAt]
  intro base
  by_cases firstSeam : (planarPart base 0 : SpatialCircle) =
      ((-2 : ℝ) : SpatialCircle)
  · exact (contDiffAt_const (c := (0 : ComplexEuclidean dimension))).congr_of_eventuallyEq
      (eventually_torusCellLift_periodized_eq_zero_of_seam field base 0 firstSeam)
  · by_cases secondSeam : (planarPart base 1 : SpatialCircle) =
        ((-2 : ℝ) : SpatialCircle)
    · exact (contDiffAt_const (c := (0 : ComplexEuclidean dimension))).congr_of_eventuallyEq
        (eventually_torusCellLift_periodized_eq_zero_of_seam field base 1 secondSeam)
    · have localEquality : torusCellLift (periodizedExtensionValue field) =ᶠ[𝓝 base]
          (ambientExtensionCellLift field ∘ localPeriodizationChart base) := by
        filter_upwards [eventually_periodizedSpatialCellRepresentative_eq_chart
          base firstSeam secondSeam] with candidate equality
        rw [torusCellLift_periodizedExtensionValue, Function.comp_apply, equality]
      exact ((ambientExtensionCellLift_contDiff_infty field).comp
        (localPeriodizationChart_contDiff base)).contDiffAt.congr_of_eventuallyEq
          localEquality

def spatialCellCoordinateHomeomorph :
    SpatialCell ≃ₜ ((ℝ × ℝ) × ℝ) where
  toFun point := ((point 0, point 1), point 2)
  invFun input := assembleSpatialCell
    (WithLp.toLp 2 ![input.1.1, input.1.2]) input.2
  left_inv point := by
    ext coordinate
    fin_cases coordinate <;> rfl
  right_inv input := by
    rcases input with ⟨⟨first, second⟩, cell⟩
    rfl
  continuous_toFun := by
    exact (((PiLp.continuous_apply 2 _ 0).prodMk
      (PiLp.continuous_apply 2 _ 1)).prodMk
        (PiLp.continuous_apply 2 _ 2))
  continuous_invFun := by
    have pairContinuous : Continuous (fun input : ((ℝ × ℝ) × ℝ) =>
        (WithLp.toLp 2 ![input.1.1, input.1.2], input.2)) := by
      apply Continuous.prodMk
      · exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp (by
          apply continuous_pi
          intro coordinate
          fin_cases coordinate
          · exact continuous_fst.comp continuous_fst
          · exact continuous_snd.comp continuous_fst)
      · exact continuous_snd
    change Continuous (fun input : ((ℝ × ℝ) × ℝ) =>
      assembleSpatialCellCLM
        (WithLp.toLp 2 ![input.1.1, input.1.2], input.2))
    exact assembleSpatialCellCLM.continuous.comp pairContinuous

def torusCoordinateQuotient (input : ((ℝ × ℝ) × ℝ)) :
    TorusCellDomain :=
  (((input.1.1 : SpatialCircle), (input.1.2 : SpatialCircle)),
    (input.2 : CellCircle))

theorem torusCoordinateQuotient_isOpenQuotientMap :
    IsOpenQuotientMap torusCoordinateQuotient := by
  exact (QuotientAddGroup.isOpenQuotientMap_mk.prodMap
    QuotientAddGroup.isOpenQuotientMap_mk).prodMap
      QuotientAddGroup.isOpenQuotientMap_mk

theorem torusCellPoint_eq_coordinateQuotient_comp :
    torusCellPoint = torusCoordinateQuotient ∘ spatialCellCoordinateHomeomorph := by
  funext point
  rfl

theorem torusCellPoint_isOpenQuotientMap :
    IsOpenQuotientMap torusCellPoint := by
  rw [torusCellPoint_eq_coordinateQuotient_comp]
  refine ⟨torusCoordinateQuotient_isOpenQuotientMap.surjective.comp
      spatialCellCoordinateHomeomorph.surjective, ?_, ?_⟩
  · exact torusCoordinateQuotient_isOpenQuotientMap.continuous.comp
      spatialCellCoordinateHomeomorph.continuous
  · exact torusCoordinateQuotient_isOpenQuotientMap.isOpenMap.comp
      spatialCellCoordinateHomeomorph.isOpenMap

def torusCellPointContinuousMap : ContinuousMap SpatialCell TorusCellDomain where
  toFun := torusCellPoint
  continuous_toFun := torusCellPoint_isOpenQuotientMap.continuous

theorem torusCellPointContinuousMap_isQuotientMap :
    Topology.IsQuotientMap torusCellPointContinuousMap :=
  torusCellPoint_isOpenQuotientMap.isQuotientMap

@[simp] theorem torusCellPoint_zero :
    torusCellPoint (0 : SpatialCell) = 0 := by
  rfl

@[simp] theorem torusCellPoint_add (first second : SpatialCell) :
    torusCellPoint (first + second) =
      torusCellPoint first + torusCellPoint second := by
  rfl

@[simp] theorem torusCellPoint_sub (first second : SpatialCell) :
    torusCellPoint (first - second) =
      torusCellPoint first - torusCellPoint second := by
  rfl

def periodicMixedDerivativeLift {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ)
    (word : MixedCartesianWord order) :
    ContinuousMap SpatialCell (ComplexEuclidean dimension) where
  toFun := mixedCartesianDerivative order word
    (torusCellLift (periodizedExtensionValue field))
  continuous_toFun := by
    have derivativesContinuous : Continuous (iteratedFDeriv ℝ order
        (torusCellLift (periodizedExtensionValue field))) :=
      (torusCellLift_periodizedExtensionValue_contDiff field).continuous_iteratedFDeriv
        (WithTop.coe_le_coe.mpr
          (show (order : ℕ∞) ≤ ⊤ from le_top))
    exact (ContinuousMultilinearMap.apply ℝ
      (fun _ : Fin order => SpatialCell) (ComplexEuclidean dimension)
      (fun position => spatialCellBasis (word position))).continuous.comp
        derivativesContinuous

theorem periodicMixedDerivativeLift_factors {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ)
    (word : MixedCartesianWord order) :
    Function.FactorsThrough (periodicMixedDerivativeLift field order word)
      torusCellPointContinuousMap := by
  intro first second quotientEquality
  change torusCellPoint first = torusCellPoint second at quotientEquality
  let shift : SpatialCell := second - first
  have quotientShiftZero : torusCellPoint shift = 0 := by
    dsimp only [shift]
    rw [torusCellPoint_sub, quotientEquality, sub_self]
  have functionShift :
      (fun point : SpatialCell =>
        torusCellLift (periodizedExtensionValue field) (point + shift)) =
        torusCellLift (periodizedExtensionValue field) := by
    funext point
    unfold torusCellLift
    rw [torusCellPoint_add, quotientShiftZero, add_zero]
  unfold periodicMixedDerivativeLift mixedCartesianDerivative
  change iteratedFDeriv ℝ order
      (torusCellLift (periodizedExtensionValue field)) first
        (fun position => spatialCellBasis (word position)) =
    iteratedFDeriv ℝ order
      (torusCellLift (periodizedExtensionValue field)) second
        (fun position => spatialCellBasis (word position))
  calc
    iteratedFDeriv ℝ order
        (torusCellLift (periodizedExtensionValue field)) first
          (fun position => spatialCellBasis (word position)) =
        iteratedFDeriv ℝ order
          (fun point : SpatialCell =>
            torusCellLift (periodizedExtensionValue field) (point + shift)) first
          (fun position => spatialCellBasis (word position)) := by
      rw [functionShift]
    _ = iteratedFDeriv ℝ order
          (torusCellLift (periodizedExtensionValue field)) (first + shift)
          (fun position => spatialCellBasis (word position)) := by
      rw [iteratedFDeriv_comp_add_right]
    _ = iteratedFDeriv ℝ order
          (torusCellLift (periodizedExtensionValue field)) second
          (fun position => spatialCellBasis (word position)) := by
      rw [show first + shift = second by dsimp only [shift]; abel]

noncomputable def periodizedDerivativeExtension {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ)
    (word : MixedCartesianWord order) :
    ContinuousMap TorusCellDomain (ComplexEuclidean dimension) :=
  torusCellPointContinuousMap_isQuotientMap.lift
    (periodicMixedDerivativeLift field order word)
    (periodicMixedDerivativeLift_factors field order word)

theorem periodizedDerivativeExtension_spec {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (order : ℕ)
    (word : MixedCartesianWord order) (point : SpatialCell) :
    periodizedDerivativeExtension field order word (torusCellPoint point) =
      mixedCartesianDerivative order word
        (torusCellLift (periodizedExtensionValue field)) point := by
  change (periodizedDerivativeExtension field order word).comp
      torusCellPointContinuousMap point =
    periodicMixedDerivativeLift field order word point
  rw [periodizedDerivativeExtension,
    Topology.IsQuotientMap.lift_comp]

noncomputable def periodizedExtension {dimension : ℕ}
    (field : DiskCellClosedJet dimension) : TorusSmoothField dimension where
  value := periodizedExtensionValue field
  smoothLift := torusCellLift_periodizedExtensionValue_contDiff field
  derivativeExists := fun order word =>
    ⟨periodizedDerivativeExtension field order word,
      periodizedDerivativeExtension_spec field order word⟩

end Grad.DiskExtension.Operator
