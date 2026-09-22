import P0910GradeMeasure

noncomputable section

open Filter Set MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets

theorem spatialCircle_coe_ne_seam_of_mem_Ioo
    (coordinate : ℝ) (membership : coordinate ∈ Ioo (-2 : ℝ) 2) :
    (coordinate : SpatialCircle) ≠ ((-2 : ℝ) : SpatialCircle) := by
  intro equality
  have representativeEquality := congrArg
    (fun point : SpatialCircle =>
      (AddCircle.equivIco (4 : ℝ) (-2) point).val) equality
  rw [show (AddCircle.equivIco (4 : ℝ) (-2)
      (coordinate : SpatialCircle)).val = coordinate by
    exact congrArg Subtype.val (AddCircle.equivIco_coe_eq
      ⟨membership.1.le, by
        norm_num
        exact membership.2⟩),
    show (AddCircle.equivIco (4 : ℝ) (-2)
      ((-2 : ℝ) : SpatialCircle)).val = -2 by
    exact congrArg Subtype.val (AddCircle.equivIco_coe_eq (by norm_num))]
      at representativeEquality
  linarith [membership.1]

theorem localPeriodizationOffset_eq_zero_of_mem_Ioo
    (base : SpatialCell)
    (firstMembership : planarPart base 0 ∈ Ioo (-2 : ℝ) 2)
    (secondMembership : planarPart base 1 ∈ Ioo (-2 : ℝ) 2) :
    localPeriodizationOffset base = 0 := by
  have firstRepresentative :
      (AddCircle.equivIco (4 : ℝ) (-2)
        (planarPart base 0 : SpatialCircle)).val = planarPart base 0 :=
    congrArg Subtype.val (AddCircle.equivIco_coe_eq
      ⟨firstMembership.1.le, by
        norm_num
        exact firstMembership.2⟩)
  have secondRepresentative :
      (AddCircle.equivIco (4 : ℝ) (-2)
        (planarPart base 1 : SpatialCircle)).val = planarPart base 1 :=
    congrArg Subtype.val (AddCircle.equivIco_coe_eq
      ⟨secondMembership.1.le, by
        norm_num
        exact secondMembership.2⟩)
  ext coordinate
  fin_cases coordinate <;>
    simp [localPeriodizationOffset, assembleSpatialCell,
      firstRepresentative, secondRepresentative]

theorem eventually_torusCellLift_periodized_eq_ambient_of_mem_Ioo
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (base : SpatialCell)
    (firstMembership : planarPart base 0 ∈ Ioo (-2 : ℝ) 2)
    (secondMembership : planarPart base 1 ∈ Ioo (-2 : ℝ) 2) :
    torusCellLift (periodizedExtension field).value =ᶠ[nhds base]
      ambientExtensionCellLift field := by
  have firstNonseam := spatialCircle_coe_ne_seam_of_mem_Ioo
    (planarPart base 0) firstMembership
  have secondNonseam := spatialCircle_coe_ne_seam_of_mem_Ioo
    (planarPart base 1) secondMembership
  have representativeChart :=
    eventually_periodizedSpatialCellRepresentative_eq_chart
      base firstNonseam secondNonseam
  have offsetZero := localPeriodizationOffset_eq_zero_of_mem_Ioo
    base firstMembership secondMembership
  filter_upwards [representativeChart] with candidate equality
  change torusCellLift (periodizedExtensionValue field) candidate = _
  rw [torusCellLift_periodizedExtensionValue, equality,
    localPeriodizationChart, offsetZero, add_zero]

theorem eventually_ambientExtension_eq_zero_of_large_coordinate
    {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (base : SpatialCell) (coordinate : Fin 2)
    (large : outerSupportRadius < |planarPart base coordinate|) :
    ambientExtensionCellLift field =ᶠ[nhds base]
      (0 : SpatialCell → ComplexEuclidean dimension) := by
  have coordinateContinuous : Continuous
      (fun point : SpatialCell => |planarPart point coordinate|) :=
    ((PiLp.continuous_apply 2 _ coordinate).comp continuous_planarPart).abs
  filter_upwards [coordinateContinuous.continuousAt.eventually
    (Ioi_mem_nhds large)] with candidate candidateLarge
  rw [ambientExtensionCellLift]
  exact ambientExtension_zero_of_support field.value
    (planarPart candidate) (candidate 2 : CellCircle)
    (candidateLarge.le.trans
      (spatialPlane_coordinate_abs_le_norm (planarPart candidate) coordinate))

theorem mixedCartesianDerivative_eq_zero_of_eventually_zero
    {dimension order : ℕ} (function : SpatialCell → ComplexEuclidean dimension)
    (word : MixedCartesianWord order) (point : SpatialCell)
    (zeroNeighborhood : function =ᶠ[nhds point]
      (0 : SpatialCell → ComplexEuclidean dimension)) :
    mixedCartesianDerivative order word function point = 0 := by
  unfold mixedCartesianDerivative
  have derivativeEquality :=
    (zeroNeighborhood.iteratedFDeriv ℝ order).eq_of_nhds
  rw [derivativeEquality]
  simp

theorem periodized_mixedDerivative_eq_ambient_on_fundamental
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (word : MixedCartesianWord order) (point : SpatialPlane)
    (cell : ℝ) (membership : point ∈ fundamentalIocSquare) :
    torusDerivative (periodizedExtension field) order word
        (torusCellPoint (assembleSpatialCell point cell)) =
      mixedCartesianDerivative order word (ambientExtensionCellLift field)
        (assembleSpatialCell point cell) := by
  rw [torusDerivative_spec]
  let base := assembleSpatialCell point cell
  by_cases firstSeam : point 0 = 2
  · have quotientSeam : (planarPart base 0 : SpatialCircle) =
        ((-2 : ℝ) : SpatialCircle) := by
      change ((point 0 : ℝ) : SpatialCircle) = _
      rw [firstSeam]
      calc
        ((2 : ℝ) : SpatialCircle) =
            (((-2 : ℝ) + 4 : ℝ) : SpatialCircle) := by norm_num
        _ = ((-2 : ℝ) : SpatialCircle) :=
          AddCircle.coe_add_period (p := (4 : ℝ)) (-2 : ℝ)
    have torusZero := mixedCartesianDerivative_eq_zero_of_eventually_zero
      (torusCellLift (periodizedExtension field).value) word base
      (by
        change torusCellLift (periodizedExtensionValue field) =ᶠ[nhds base] _
        exact eventually_torusCellLift_periodized_eq_zero_of_seam
          field base 0 quotientSeam)
    have ambientZero := mixedCartesianDerivative_eq_zero_of_eventually_zero
      (ambientExtensionCellLift field) word base
      (eventually_ambientExtension_eq_zero_of_large_coordinate
        field base 0 (by
          change outerSupportRadius < |point 0|
          rw [firstSeam, collar_constants.2.2.2.2]
          norm_num))
    rw [torusZero, ambientZero]
  · by_cases secondSeam : point 1 = 2
    · have quotientSeam : (planarPart base 1 : SpatialCircle) =
          ((-2 : ℝ) : SpatialCircle) := by
        change ((point 1 : ℝ) : SpatialCircle) = _
        rw [secondSeam]
        calc
          ((2 : ℝ) : SpatialCircle) =
              (((-2 : ℝ) + 4 : ℝ) : SpatialCircle) := by norm_num
          _ = ((-2 : ℝ) : SpatialCircle) :=
            AddCircle.coe_add_period (p := (4 : ℝ)) (-2 : ℝ)
      have torusZero := mixedCartesianDerivative_eq_zero_of_eventually_zero
        (torusCellLift (periodizedExtension field).value) word base
        (by
          change torusCellLift (periodizedExtensionValue field) =ᶠ[nhds base] _
          exact eventually_torusCellLift_periodized_eq_zero_of_seam
            field base 1 quotientSeam)
      have ambientZero := mixedCartesianDerivative_eq_zero_of_eventually_zero
        (ambientExtensionCellLift field) word base
        (eventually_ambientExtension_eq_zero_of_large_coordinate
          field base 1 (by
            change outerSupportRadius < |point 1|
            rw [secondSeam, collar_constants.2.2.2.2]
            norm_num))
      rw [torusZero, ambientZero]
    · have firstMembership : planarPart base 0 ∈ Ioo (-2 : ℝ) 2 := by
          change point 0 ∈ Ioo (-2 : ℝ) 2
          exact ⟨membership.1.1, lt_of_le_of_ne membership.1.2 firstSeam⟩
      have secondMembership : planarPart base 1 ∈ Ioo (-2 : ℝ) 2 := by
          change point 1 ∈ Ioo (-2 : ℝ) 2
          exact ⟨membership.2.1, lt_of_le_of_ne membership.2.2 secondSeam⟩
      unfold mixedCartesianDerivative
      have derivativeEquality :=
        ((eventually_torusCellLift_periodized_eq_ambient_of_mem_Ioo
          field base firstMembership secondMembership).iteratedFDeriv
            ℝ order).eq_of_nhds
      rw [derivativeEquality]

end Grad.DiskExtension.Operator
