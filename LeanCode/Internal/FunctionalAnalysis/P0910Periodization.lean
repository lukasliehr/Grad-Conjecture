import P0910JetBoundary

noncomputable section

open Filter Set
open scoped BigOperators ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets
open Grad.DiskExtension.Seeley

def ambientExtensionPlaneCell {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (input : SpatialPlane × CellCircle) :
    ComplexEuclidean dimension :=
  ambientExtensionFromValue field.value input.1 input.2

def planeCellQuotient (input : SpatialPlane × ℝ) : SpatialPlane × CellCircle :=
  (input.1, (input.2 : CellCircle))

theorem planeCellQuotient_isOpenQuotientMap :
    IsOpenQuotientMap planeCellQuotient := by
  exact IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk

theorem ambientExtensionPlaneCell_continuous {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    Continuous (ambientExtensionPlaneCell field) := by
  apply planeCellQuotient_isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
  rw [show ambientExtensionPlaneCell field ∘ planeCellQuotient =
      ambientExtensionCellLift field ∘ assembleSpatialCellCLM by
    funext input
    unfold Function.comp ambientExtensionPlaneCell planeCellQuotient
    rw [ambientExtensionCellLift, assembleSpatialCellCLM_apply,
      planarPart_assembleSpatialCell]
    rfl]
  exact (ambientExtensionCellLift_continuous field).comp assembleSpatialCellCLM.continuous

theorem spatialTorusRepresentative_continuousAt
    (point : SpatialTorus)
    (firstNonseam : point.1 ≠ ((-2 : ℝ) : SpatialCircle))
    (secondNonseam : point.2 ≠ ((-2 : ℝ) : SpatialCircle)) :
    ContinuousAt spatialTorusRepresentative point := by
  have firstContinuous : ContinuousAt
      (fun first : SpatialCircle =>
        (AddCircle.equivIco (4 : ℝ) (-2) first).val) point.1 :=
    continuous_subtype_val.continuousAt.comp
      (AddCircle.continuousAt_equivIco 4 (-2) firstNonseam)
  have secondContinuous : ContinuousAt
      (fun second : SpatialCircle =>
        (AddCircle.equivIco (4 : ℝ) (-2) second).val) point.2 :=
    continuous_subtype_val.continuousAt.comp
      (AddCircle.continuousAt_equivIco 4 (-2) secondNonseam)
  unfold spatialTorusRepresentative
  fun_prop

def spatialRepresentativeAbs (point : SpatialCircle) : ℝ :=
  |(AddCircle.equivIco (4 : ℝ) (-2) point).val|

theorem spatialRepresentativeAbs_continuous : Continuous spatialRepresentativeAbs := by
  change Continuous (AddCircle.liftIco (4 : ℝ) (-2) abs)
  apply AddCircle.liftIco_continuous
  · norm_num
  · exact continuous_abs.continuousOn

theorem spatialRepresentativeAbs_seam :
    spatialRepresentativeAbs (((-2 : ℝ) : SpatialCircle)) = 2 := by
  rw [spatialRepresentativeAbs, AddCircle.equivIco_coe_eq]
  · norm_num
  · constructor <;> norm_num

theorem spatialPlane_coordinate_abs_le_norm (point : SpatialPlane) (coordinate : Fin 2) :
    |point coordinate| ≤ ‖point‖ := by
  have squareBound : (point coordinate) ^ 2 ≤ ‖point‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    exact Finset.single_le_sum (fun index _ => sq_nonneg (point index))
      (Finset.mem_univ coordinate)
  nlinarith [sq_abs (point coordinate), abs_nonneg (point coordinate), norm_nonneg point]

theorem periodizedExtensionFromValue_continuous {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    Continuous (periodizedExtensionFromValue field.value) := by
  rw [continuous_iff_continuousAt]
  intro point
  by_cases firstSeam : point.1.1 = (((-2 : ℝ) : SpatialCircle))
  · have atPoint : outerSupportRadius < spatialRepresentativeAbs point.1.1 := by
      rw [firstSeam, spatialRepresentativeAbs_seam, collar_constants.2.2.2.2]
      norm_num
    have absContinuous : Continuous
        (fun candidate : TorusCellDomain => spatialRepresentativeAbs candidate.1.1) :=
      spatialRepresentativeAbs_continuous.comp (continuous_fst.comp continuous_fst)
    have neighborhood : ∀ᶠ candidate in 𝓝 point,
        outerSupportRadius < spatialRepresentativeAbs candidate.1.1 :=
      absContinuous.continuousAt.eventually (Ioi_mem_nhds atPoint)
    apply continuousAt_const.congr_of_eventuallyEq
    filter_upwards [neighborhood] with candidate candidateBound
    rw [periodizedExtensionFromValue]
    apply ambientExtension_zero_of_support
    exact candidateBound.le.trans
      (spatialPlane_coordinate_abs_le_norm
        (spatialTorusRepresentative candidate.1) 0)
  · by_cases secondSeam : point.1.2 = (((-2 : ℝ) : SpatialCircle))
    · have atPoint : outerSupportRadius < spatialRepresentativeAbs point.1.2 := by
        rw [secondSeam, spatialRepresentativeAbs_seam, collar_constants.2.2.2.2]
        norm_num
      have absContinuous : Continuous
          (fun candidate : TorusCellDomain => spatialRepresentativeAbs candidate.1.2) :=
        spatialRepresentativeAbs_continuous.comp (continuous_snd.comp continuous_fst)
      have neighborhood : ∀ᶠ candidate in 𝓝 point,
          outerSupportRadius < spatialRepresentativeAbs candidate.1.2 :=
        absContinuous.continuousAt.eventually (Ioi_mem_nhds atPoint)
      apply continuousAt_const.congr_of_eventuallyEq
      filter_upwards [neighborhood] with candidate candidateBound
      rw [periodizedExtensionFromValue]
      apply ambientExtension_zero_of_support
      exact candidateBound.le.trans
        (spatialPlane_coordinate_abs_le_norm
          (spatialTorusRepresentative candidate.1) 1)
    · have spatialContinuous : ContinuousAt
          (fun candidate : TorusCellDomain => spatialTorusRepresentative candidate.1) point :=
        (spatialTorusRepresentative_continuousAt point.1 firstSeam secondSeam).comp
          continuous_fst.continuousAt
      change ContinuousAt
        (fun candidate : TorusCellDomain =>
          ambientExtensionPlaneCell field
            (spatialTorusRepresentative candidate.1, candidate.2)) point
      exact (ambientExtensionPlaneCell_continuous field).continuousAt.comp
        (spatialContinuous.prodMk continuous_snd.continuousAt)

end Grad.DiskExtension.Operator
