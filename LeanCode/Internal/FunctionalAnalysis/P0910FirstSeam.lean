import P0910ExteriorDerivative
import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Filter Set
open scoped BigOperators ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets
open Grad.DiskExtension.Seeley

theorem planarPart_normalizedSpatialCell (point : SpatialCell) :
    planarPart (normalizedSpatialCell point) =
      ‖planarPart point‖⁻¹ • planarPart point := by
  ext coordinate
  fin_cases coordinate <;>
    simp [normalizedSpatialCell, planarPart, assembleSpatialCell]

theorem normalizedSpatialCell_cell (point : SpatialCell) :
    normalizedSpatialCell point 2 = point 2 := by
  simp [normalizedSpatialCell, assembleSpatialCell]

theorem normalizedSpatialCell_boundary (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    normalizedSpatialCell point = point := by
  ext coordinate
  fin_cases coordinate
  · change ‖planarPart point‖⁻¹ * point 0 = point 0
    rw [boundary]
    simp
  · change ‖planarPart point‖⁻¹ * point 1 = point 1
    rw [boundary]
    simp
  · exact normalizedSpatialCell_cell point

theorem normalizedSpatialCell_mem_closedUnitCylinder (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    normalizedSpatialCell point ∈ closedUnitCylinder := by
  change ‖planarPart (normalizedSpatialCell point)‖ ≤ 1
  rw [planarPart_normalizedSpatialCell, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr nonzero)]

theorem normalizedSpatialCell_norm (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    ‖planarPart (normalizedSpatialCell point)‖ = 1 := by
  rw [planarPart_normalizedSpatialCell, norm_smul, Real.norm_eq_abs,
    abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr nonzero)]

theorem radialSpatialLine_normalized (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    radialSpatialLine (normalizedSpatialCell point) (‖planarPart point‖ - 1) = point := by
  have normNonzero : ‖planarPart point‖ ≠ 0 := norm_ne_zero_iff.mpr nonzero
  ext coordinate
  fin_cases coordinate <;>
    simp [radialSpatialLine, radialSpatialDirection, normalizedSpatialCell,
      assembleSpatialCell, planarPart] <;>
    field_simp [show ‖WithLp.toLp 2 ![point 0, point 1]‖ ≠ 0 by
      simpa [planarPart] using normNonzero] <;>
    ring

theorem radialSpatialDirection_normalized_smul (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    (‖planarPart point‖ - 1) •
        radialSpatialDirection (normalizedSpatialCell point) =
      point - normalizedSpatialCell point := by
  have lineIdentity := radialSpatialLine_normalized point nonzero
  rw [radialSpatialLine] at lineIdentity
  exact eq_sub_of_add_eq' lineIdentity

theorem normalizedSpatialCell_hasFDerivAt (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    HasFDerivAt normalizedSpatialCell
      (fderiv ℝ normalizedSpatialCell point) point :=
  ((normalizedSpatialCell_contDiffAt point nonzero).differentiableAt
    (by simp)).hasFDerivAt

theorem eventually_normalizedSpatialCell_mem_closedUnitCylinder
    (point : SpatialCell) (nonzero : planarPart point ≠ 0) :
    ∀ᶠ candidate in nhds point,
      normalizedSpatialCell candidate ∈ closedUnitCylinder := by
  have eventuallyNonzero : ∀ᶠ candidate in nhds point,
      planarPart candidate ≠ 0 :=
    continuous_planarPart.continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds nonzero)
  filter_upwards [eventuallyNonzero] with candidate candidateNonzero
  exact normalizedSpatialCell_mem_closedUnitCylinder candidate candidateNonzero

theorem diskCellLift_comp_normalized_hasFDerivAt_boundary {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    HasFDerivAt (diskCellLift field.value ∘ normalizedSpatialCell)
      ((closedFirstDerivative field point).comp
        (fderiv ℝ normalizedSpatialCell point)) point := by
  have nonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  exact (diskCellLift_hasFDerivWithinAt_closed field point).comp_hasFDerivAt_of_eq point
    (normalizedSpatialCell_hasFDerivAt point nonzero)
    (eventually_normalizedSpatialCell_mem_closedUnitCylinder point nonzero)
    (normalizedSpatialCell_boundary point boundary).symm

def boundaryRadialSegment (point : SpatialCell) (parameter : ℝ) : SpatialCell :=
  normalizedSpatialCell point +
    parameter • (point - normalizedSpatialCell point)

@[simp] theorem boundaryRadialSegment_zero (point : SpatialCell) :
    boundaryRadialSegment point 0 = normalizedSpatialCell point := by
  simp [boundaryRadialSegment]

@[simp] theorem boundaryRadialSegment_one (point : SpatialCell) :
    boundaryRadialSegment point 1 = point := by
  simp [boundaryRadialSegment]

theorem boundaryRadialSegment_eq_radialSpatialLine (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) (parameter : ℝ) :
    boundaryRadialSegment point parameter =
      radialSpatialLine (normalizedSpatialCell point)
        (parameter * (‖planarPart point‖ - 1)) := by
  rw [boundaryRadialSegment, radialSpatialLine,
    ← radialSpatialDirection_normalized_smul point nonzero]
  module

theorem boundaryRadialSegment_hasDerivAt (point : SpatialCell) (parameter : ℝ) :
    HasDerivAt (boundaryRadialSegment point)
      (point - normalizedSpatialCell point) parameter := by
  rw [hasDerivAt_iff_hasFDerivAt, ← hasFDerivWithinAt_univ,
    hasFDerivWithinAt_piLp]
  intro coordinate
  change HasFDerivWithinAt (fun scale : ℝ =>
    normalizedSpatialCell point coordinate +
      scale * (point - normalizedSpatialCell point) coordinate)
    ((1 : ℝ →L[ℝ] ℝ).smulRight
      ((point - normalizedSpatialCell point) coordinate)) univ parameter
  fun_prop

theorem boundaryRadialSegment_mem_closedUnitCylinder (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) (inside : ‖planarPart point‖ ≤ 1)
    {parameter : ℝ} (parameterMembership : parameter ∈ Icc (0 : ℝ) 1) :
    boundaryRadialSegment point parameter ∈ closedUnitCylinder := by
  have radiusPositive : 0 < ‖planarPart point‖ := norm_pos_iff.mpr nonzero
  have coefficientLower : ‖planarPart point‖ ≤
      1 + parameter * (‖planarPart point‖ - 1) := by
    have productNonnegative : 0 ≤
        (1 - parameter) * (1 - ‖planarPart point‖) :=
      mul_nonneg (by linarith [parameterMembership.2]) (by linarith)
    nlinarith
  have coefficientUpper :
      1 + parameter * (‖planarPart point‖ - 1) ≤ 1 := by
    have productNonpositive :
        parameter * (‖planarPart point‖ - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos parameterMembership.1 (by linarith)
    linarith
  change ‖planarPart (boundaryRadialSegment point parameter)‖ ≤ 1
  rw [boundaryRadialSegment_eq_radialSpatialLine point nonzero,
    planarPart_radialSpatialLine, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (le_trans radiusPositive.le coefficientLower),
    normalizedSpatialCell_norm point nonzero, mul_one]
  exact coefficientUpper

theorem boundaryRadialSegment_mem_outerClosed (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) (outside : 1 ≤ ‖planarPart point‖)
    {parameter : ℝ} (parameterMembership : parameter ∈ Icc (0 : ℝ) 1) :
    1 ≤ ‖planarPart (boundaryRadialSegment point parameter)‖ := by
  have productNonnegative : 0 ≤
      parameter * (‖planarPart point‖ - 1) :=
    mul_nonneg parameterMembership.1 (by linarith)
  rw [boundaryRadialSegment_eq_radialSpatialLine point nonzero,
    planarPart_radialSpatialLine, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by linarith), normalizedSpatialCell_norm point nonzero, mul_one]
  linarith

theorem boundaryRadialSegment_mem_openUnitCylinder (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) (inside : ‖planarPart point‖ < 1)
    {parameter : ℝ} (parameterPositive : 0 < parameter)
    (parameterUpper : parameter ≤ 1) :
    boundaryRadialSegment point parameter ∈ openUnitCylinder := by
  have parameterMembership : parameter ∈ Icc (0 : ℝ) 1 :=
    ⟨parameterPositive.le, parameterUpper⟩
  have radiusPositive : 0 < ‖planarPart point‖ := norm_pos_iff.mpr nonzero
  have coefficientLower : ‖planarPart point‖ ≤
      1 + parameter * (‖planarPart point‖ - 1) := by
    have productNonnegative : 0 ≤
        (1 - parameter) * (1 - ‖planarPart point‖) :=
      mul_nonneg (by linarith) (by linarith)
    nlinarith
  have coefficientUpper :
      1 + parameter * (‖planarPart point‖ - 1) < 1 := by
    have productNegative : parameter * (‖planarPart point‖ - 1) < 0 :=
      mul_neg_of_pos_of_neg parameterPositive (by linarith)
    linarith
  change ‖planarPart (boundaryRadialSegment point parameter)‖ < 1
  rw [boundaryRadialSegment_eq_radialSpatialLine point nonzero,
    planarPart_radialSpatialLine, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (le_trans radiusPositive.le coefficientLower),
    normalizedSpatialCell_norm point nonzero, mul_one]
  exact coefficientUpper

theorem boundaryRadialSegment_mem_outerOpen (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) (outside : 1 < ‖planarPart point‖)
    {parameter : ℝ} (parameterPositive : 0 < parameter) :
    1 < ‖planarPart (boundaryRadialSegment point parameter)‖ := by
  have productPositive : 0 < parameter * (‖planarPart point‖ - 1) :=
    mul_pos parameterPositive (by linarith)
  rw [boundaryRadialSegment_eq_radialSpatialLine point nonzero,
    planarPart_radialSpatialLine, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by linarith), normalizedSpatialCell_norm point nonzero, mul_one]
  linarith

theorem ambientExtensionCellLift_hasFDerivAt_inside {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (inside : point ∈ openUnitCylinder) :
    HasFDerivAt (ambientExtensionCellLift field)
      (closedFirstDerivative field point) point := by
  have diskDerivative : HasFDerivAt (diskCellLift field.value)
      (closedFirstDerivative field point) point := by
    rw [closedFirstDerivative_eq_fderiv field point inside]
    exact ((field.smoothInterior point inside).contDiffAt
      (openUnitCylinder_isOpen.mem_nhds inside)).differentiableAt (by simp) |>.hasFDerivAt
  have eventuallyInside : ∀ᶠ candidate in nhds point,
      candidate ∈ closedUnitCylinder := by
    filter_upwards [openUnitCylinder_isOpen.mem_nhds inside] with candidate membership
    exact openCylinderMembershipClosed candidate membership
  apply diskDerivative.congr_of_eventuallyEq
  filter_upwards [eventuallyInside] with candidate candidateInside
  exact ambientExtensionCellLift_eq_diskCellLift field candidate candidateInside

theorem ambientExtensionCellLift_hasFDerivAt_outside {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (outside : 1 < ‖planarPart point‖) :
    HasFDerivAt (ambientExtensionCellLift field)
      (∑' index, exteriorSummandFirstModel field index point) point := by
  have eventuallyOutside : ∀ᶠ candidate in nhds point,
      1 ≤ ‖planarPart candidate‖ := by
    filter_upwards [
      (isOpen_lt continuous_const (continuous_norm.comp continuous_planarPart)).mem_nhds
        outside] with candidate membership
    exact membership.le
  apply (exteriorSeriesCellLift_hasFDerivAt field point outside).congr_of_eventuallyEq
  filter_upwards [eventuallyOutside] with candidate candidateOutside
  exact ambientExtensionCellLift_eq_exteriorSeries field candidate candidateOutside

theorem ambientExtension_boundaryRadialSegment_hasDerivAt_zero {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    HasDerivAt (ambientExtensionCellLift field ∘ boundaryRadialSegment point)
      (closedFirstDerivative field (normalizedSpatialCell point)
        (point - normalizedSpatialCell point)) 0 := by
  have normalizedBoundary := normalizedSpatialCell_norm point nonzero
  have radialDerivative :=
    ambientExtensionCellLift_hasDerivAt_radial_boundary field
      (normalizedSpatialCell point) normalizedBoundary
  have scaleDerivative : HasDerivAt
      (fun parameter : ℝ => parameter * (‖planarPart point‖ - 1))
      (‖planarPart point‖ - 1) 0 := by
    simpa only [id_eq, one_mul] using
      (hasDerivAt_id (x := (0 : ℝ))).mul_const (‖planarPart point‖ - 1)
  have composed := radialDerivative.scomp_of_eq 0 scaleDerivative
    (zero_mul (‖planarPart point‖ - 1)).symm
  have functionEquality :
      (ambientExtensionCellLift field ∘ boundaryRadialSegment point) =
        (ambientExtensionCellLift field ∘ radialSpatialLine (normalizedSpatialCell point)) ∘
          (fun parameter : ℝ => parameter * (‖planarPart point‖ - 1)) := by
    funext parameter
    simp only [Function.comp_apply]
    rw [boundaryRadialSegment_eq_radialSpatialLine point nonzero parameter]
  have derivativeEquality :
      (‖planarPart point‖ - 1) •
          closedFirstDerivative field (normalizedSpatialCell point)
            (radialSpatialDirection (normalizedSpatialCell point)) =
        closedFirstDerivative field (normalizedSpatialCell point)
          (point - normalizedSpatialCell point) := by
    rw [← map_smul,
      radialSpatialDirection_normalized_smul point nonzero]
  rw [functionEquality]
  rw [← derivativeEquality]
  exact composed

theorem ambientExtension_boundaryRadialSegment_hasDerivAt_inside {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) (inside : ‖planarPart point‖ < 1)
    {parameter : ℝ} (parameterPositive : 0 < parameter)
    (parameterUpper : parameter ≤ 1) :
    HasDerivAt (ambientExtensionCellLift field ∘ boundaryRadialSegment point)
      (closedFirstDerivative field (boundaryRadialSegment point parameter)
        (point - normalizedSpatialCell point)) parameter := by
  exact (ambientExtensionCellLift_hasFDerivAt_inside field
    (boundaryRadialSegment point parameter)
    (boundaryRadialSegment_mem_openUnitCylinder point nonzero inside
      parameterPositive parameterUpper)).comp_hasDerivAt parameter
        (boundaryRadialSegment_hasDerivAt point parameter)

theorem ambientExtension_boundaryRadialSegment_hasDerivAt_outside {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) (outside : 1 < ‖planarPart point‖)
    {parameter : ℝ} (parameterPositive : 0 < parameter) :
    HasDerivAt (ambientExtensionCellLift field ∘ boundaryRadialSegment point)
      ((∑' index, exteriorSummandFirstModel field index
        (boundaryRadialSegment point parameter))
          (point - normalizedSpatialCell point)) parameter := by
  exact (ambientExtensionCellLift_hasFDerivAt_outside field
    (boundaryRadialSegment point parameter)
    (boundaryRadialSegment_mem_outerOpen point nonzero outside parameterPositive)).comp_hasDerivAt
      parameter (boundaryRadialSegment_hasDerivAt point parameter)

theorem radialSpatialDirection_normalized_norm_le (point : SpatialCell)
    (nonzero : planarPart point ≠ 0) :
    ‖radialSpatialDirection (normalizedSpatialCell point)‖ ≤
      ‖assembleSpatialCellCLM‖ := by
  change ‖assembleSpatialCellCLM
      (planarPart (normalizedSpatialCell point), 0)‖ ≤
    ‖assembleSpatialCellCLM‖
  calc
    ‖assembleSpatialCellCLM
        (planarPart (normalizedSpatialCell point), 0)‖ ≤
        ‖assembleSpatialCellCLM‖ *
          ‖(planarPart (normalizedSpatialCell point), (0 : ℝ))‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ = ‖assembleSpatialCellCLM‖ := by
      rw [Prod.norm_def, norm_zero, max_eq_left (norm_nonneg _),
        normalizedSpatialCell_norm point nonzero, mul_one]

theorem point_sub_normalized_norm_le_boundary (point boundaryPoint : SpatialCell)
    (nonzero : planarPart point ≠ 0)
    (boundary : ‖planarPart boundaryPoint‖ = 1) :
    ‖point - normalizedSpatialCell point‖ ≤
      (‖assembleSpatialCellCLM‖ * ‖planarPartCLM‖) *
        ‖point - boundaryPoint‖ := by
  have radialEquality := radialSpatialDirection_normalized_smul point nonzero
  have radialBound := radialSpatialDirection_normalized_norm_le point nonzero
  have radiusDifference :
      |‖planarPart point‖ - 1| ≤
        ‖planarPartCLM‖ * ‖point - boundaryPoint‖ := by
    calc
      |‖planarPart point‖ - 1| =
          |‖planarPart point‖ - ‖planarPart boundaryPoint‖| := by rw [boundary]
      _ ≤ ‖planarPart point - planarPart boundaryPoint‖ :=
        abs_norm_sub_norm_le _ _
      _ = ‖planarPartCLM (point - boundaryPoint)‖ := by
        rw [map_sub, planarPartCLM_apply, planarPartCLM_apply]
      _ ≤ ‖planarPartCLM‖ * ‖point - boundaryPoint‖ :=
        ContinuousLinearMap.le_opNorm _ _
  rw [← radialEquality, norm_smul, Real.norm_eq_abs]
  calc
    |‖planarPart point‖ - 1| *
        ‖radialSpatialDirection (normalizedSpatialCell point)‖ ≤
        |‖planarPart point‖ - 1| * ‖assembleSpatialCellCLM‖ :=
      mul_le_mul_of_nonneg_left radialBound (abs_nonneg _)
    _ ≤ (‖planarPartCLM‖ * ‖point - boundaryPoint‖) *
        ‖assembleSpatialCellCLM‖ :=
      mul_le_mul_of_nonneg_right radiusDifference (norm_nonneg _)
    _ = (‖assembleSpatialCellCLM‖ * ‖planarPartCLM‖) *
        ‖point - boundaryPoint‖ := by ring

theorem ambient_radial_remainder_norm_le_inside {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (boundaryPoint point : SpatialCell)
    (pointNonzero : planarPart point ≠ 0)
    (inside : ‖planarPart point‖ < 1) (epsilon : ℝ)
    (derivativeBound : ∀ parameter ∈ Icc (0 : ℝ) 1,
      ‖closedFirstDerivative field (boundaryRadialSegment point parameter) -
        closedFirstDerivative field boundaryPoint‖ ≤ epsilon) :
    ‖ambientExtensionCellLift field point -
        ambientExtensionCellLift field (normalizedSpatialCell point) -
      closedFirstDerivative field boundaryPoint
        (point - normalizedSpatialCell point)‖ ≤
      epsilon * ‖point - normalizedSpatialCell point‖ := by
  let corrected : ℝ → ComplexEuclidean dimension := fun parameter =>
    ambientExtensionCellLift field (boundaryRadialSegment point parameter) -
      closedFirstDerivative field boundaryPoint
        (boundaryRadialSegment point parameter)
  let correctedDerivative : ℝ → ComplexEuclidean dimension := fun parameter =>
    (closedFirstDerivative field (boundaryRadialSegment point parameter) -
      closedFirstDerivative field boundaryPoint)
        (point - normalizedSpatialCell point)
  have correctedHasDerivative : ∀ parameter ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt corrected (correctedDerivative parameter)
        (Icc (0 : ℝ) 1) parameter := by
    intro parameter parameterMembership
    have ambientDerivative : HasDerivAt
        (ambientExtensionCellLift field ∘ boundaryRadialSegment point)
        (closedFirstDerivative field (boundaryRadialSegment point parameter)
          (point - normalizedSpatialCell point)) parameter := by
      by_cases parameterZero : parameter = 0
      · subst parameter
        simpa only [boundaryRadialSegment_zero] using
          ambientExtension_boundaryRadialSegment_hasDerivAt_zero
            field point pointNonzero
      · exact ambientExtension_boundaryRadialSegment_hasDerivAt_inside
          field point pointNonzero inside (lt_of_le_of_ne parameterMembership.1
            (Ne.symm parameterZero)) parameterMembership.2
    have linearDerivative : HasDerivAt
        (fun parameter => closedFirstDerivative field boundaryPoint
          (boundaryRadialSegment point parameter))
        (closedFirstDerivative field boundaryPoint
          (point - normalizedSpatialCell point)) parameter :=
      (closedFirstDerivative field boundaryPoint).hasFDerivAt.comp_hasDerivAt
        parameter (boundaryRadialSegment_hasDerivAt point parameter)
    have differenceDerivative := ambientDerivative.sub linearDerivative
    change HasDerivWithinAt
      ((ambientExtensionCellLift field ∘ boundaryRadialSegment point) -
        fun parameter => closedFirstDerivative field boundaryPoint
          (boundaryRadialSegment point parameter))
      ((closedFirstDerivative field (boundaryRadialSegment point parameter) -
        closedFirstDerivative field boundaryPoint)
          (point - normalizedSpatialCell point)) (Icc (0 : ℝ) 1) parameter
    exact differenceDerivative.hasDerivWithinAt
  have derivativeNormBound : ∀ parameter ∈ Ico (0 : ℝ) 1,
      ‖correctedDerivative parameter‖ ≤
        epsilon * ‖point - normalizedSpatialCell point‖ := by
    intro parameter parameterMembership
    calc
      ‖correctedDerivative parameter‖ ≤
          ‖closedFirstDerivative field (boundaryRadialSegment point parameter) -
            closedFirstDerivative field boundaryPoint‖ *
              ‖point - normalizedSpatialCell point‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ epsilon * ‖point - normalizedSpatialCell point‖ :=
        mul_le_mul_of_nonneg_right
          (derivativeBound parameter (Ico_subset_Icc_self parameterMembership))
          (norm_nonneg _)
  have meanValue := norm_image_sub_le_of_norm_deriv_le_segment_01'
    correctedHasDerivative derivativeNormBound
  change ‖corrected 1 - corrected 0‖ ≤
    epsilon * ‖point - normalizedSpatialCell point‖ at meanValue
  calc
    ‖ambientExtensionCellLift field point -
        ambientExtensionCellLift field (normalizedSpatialCell point) -
      closedFirstDerivative field boundaryPoint
        (point - normalizedSpatialCell point)‖ =
        ‖corrected 1 - corrected 0‖ := by
      dsimp only [corrected]
      rw [boundaryRadialSegment_one, boundaryRadialSegment_zero, map_sub]
      congr 1
      abel
    _ ≤ epsilon * ‖point - normalizedSpatialCell point‖ := meanValue

theorem ambient_radial_remainder_norm_le_outside {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (boundaryPoint point : SpatialCell)
    (pointNonzero : planarPart point ≠ 0)
    (outside : 1 < ‖planarPart point‖) (epsilon : ℝ)
    (boundaryDerivativeBound :
      ‖closedFirstDerivative field (normalizedSpatialCell point) -
        closedFirstDerivative field boundaryPoint‖ ≤ epsilon)
    (exteriorDerivativeBound : ∀ parameter ∈ Ioc (0 : ℝ) 1,
      ‖(∑' index, exteriorSummandFirstModel field index
          (boundaryRadialSegment point parameter)) -
        closedFirstDerivative field boundaryPoint‖ ≤ epsilon) :
    ‖ambientExtensionCellLift field point -
        ambientExtensionCellLift field (normalizedSpatialCell point) -
      closedFirstDerivative field boundaryPoint
        (point - normalizedSpatialCell point)‖ ≤
      epsilon * ‖point - normalizedSpatialCell point‖ := by
  let corrected : ℝ → ComplexEuclidean dimension := fun parameter =>
    ambientExtensionCellLift field (boundaryRadialSegment point parameter) -
      closedFirstDerivative field boundaryPoint
        (boundaryRadialSegment point parameter)
  let correctedDerivative : ℝ → ComplexEuclidean dimension := fun parameter =>
    if parameter = 0 then
      (closedFirstDerivative field (normalizedSpatialCell point) -
        closedFirstDerivative field boundaryPoint)
          (point - normalizedSpatialCell point)
    else
      ((∑' index, exteriorSummandFirstModel field index
          (boundaryRadialSegment point parameter)) -
        closedFirstDerivative field boundaryPoint)
          (point - normalizedSpatialCell point)
  have correctedHasDerivative : ∀ parameter ∈ Icc (0 : ℝ) 1,
      HasDerivWithinAt corrected (correctedDerivative parameter)
        (Icc (0 : ℝ) 1) parameter := by
    intro parameter parameterMembership
    by_cases parameterZero : parameter = 0
    · subst parameter
      have ambientDerivative :=
        ambientExtension_boundaryRadialSegment_hasDerivAt_zero
          field point pointNonzero
      have linearDerivative : HasDerivAt
          (fun parameter => closedFirstDerivative field boundaryPoint
            (boundaryRadialSegment point parameter))
          (closedFirstDerivative field boundaryPoint
            (point - normalizedSpatialCell point)) 0 :=
        (closedFirstDerivative field boundaryPoint).hasFDerivAt.comp_hasDerivAt
          0 (boundaryRadialSegment_hasDerivAt point 0)
      have differenceDerivative := ambientDerivative.sub linearDerivative
      dsimp only [corrected, correctedDerivative]
      rw [if_pos rfl]
      change HasDerivWithinAt
        ((ambientExtensionCellLift field ∘ boundaryRadialSegment point) -
          fun parameter => closedFirstDerivative field boundaryPoint
            (boundaryRadialSegment point parameter))
        ((closedFirstDerivative field (normalizedSpatialCell point) -
          closedFirstDerivative field boundaryPoint)
            (point - normalizedSpatialCell point)) (Icc (0 : ℝ) 1) 0
      exact differenceDerivative.hasDerivWithinAt
    · have ambientDerivative :=
        ambientExtension_boundaryRadialSegment_hasDerivAt_outside
          field point pointNonzero outside
            (lt_of_le_of_ne parameterMembership.1 (Ne.symm parameterZero))
      have linearDerivative : HasDerivAt
          (fun scale => closedFirstDerivative field boundaryPoint
            (boundaryRadialSegment point scale))
          (closedFirstDerivative field boundaryPoint
            (point - normalizedSpatialCell point)) parameter :=
        (closedFirstDerivative field boundaryPoint).hasFDerivAt.comp_hasDerivAt
          parameter (boundaryRadialSegment_hasDerivAt point parameter)
      have differenceDerivative := ambientDerivative.sub linearDerivative
      dsimp only [corrected, correctedDerivative]
      rw [if_neg parameterZero]
      change HasDerivWithinAt
        ((ambientExtensionCellLift field ∘ boundaryRadialSegment point) -
          fun scale => closedFirstDerivative field boundaryPoint
            (boundaryRadialSegment point scale))
        (((∑' index, exteriorSummandFirstModel field index
            (boundaryRadialSegment point parameter)) -
          closedFirstDerivative field boundaryPoint)
            (point - normalizedSpatialCell point)) (Icc (0 : ℝ) 1) parameter
      exact differenceDerivative.hasDerivWithinAt
  have derivativeNormBound : ∀ parameter ∈ Ico (0 : ℝ) 1,
      ‖correctedDerivative parameter‖ ≤
        epsilon * ‖point - normalizedSpatialCell point‖ := by
    intro parameter parameterMembership
    by_cases parameterZero : parameter = 0
    · simp only [correctedDerivative, if_pos parameterZero]
      calc
        ‖(closedFirstDerivative field (normalizedSpatialCell point) -
            closedFirstDerivative field boundaryPoint)
              (point - normalizedSpatialCell point)‖ ≤
            ‖closedFirstDerivative field (normalizedSpatialCell point) -
              closedFirstDerivative field boundaryPoint‖ *
                ‖point - normalizedSpatialCell point‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ epsilon * ‖point - normalizedSpatialCell point‖ :=
          mul_le_mul_of_nonneg_right boundaryDerivativeBound (norm_nonneg _)
    · simp only [correctedDerivative, if_neg parameterZero]
      calc
        ‖((∑' index, exteriorSummandFirstModel field index
              (boundaryRadialSegment point parameter)) -
            closedFirstDerivative field boundaryPoint)
              (point - normalizedSpatialCell point)‖ ≤
            ‖(∑' index, exteriorSummandFirstModel field index
                (boundaryRadialSegment point parameter)) -
              closedFirstDerivative field boundaryPoint‖ *
                ‖point - normalizedSpatialCell point‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ epsilon * ‖point - normalizedSpatialCell point‖ :=
          mul_le_mul_of_nonneg_right
            (exteriorDerivativeBound parameter
              ⟨lt_of_le_of_ne parameterMembership.1 (Ne.symm parameterZero),
                parameterMembership.2.le⟩) (norm_nonneg _)
  have meanValue := norm_image_sub_le_of_norm_deriv_le_segment_01'
    correctedHasDerivative derivativeNormBound
  change ‖corrected 1 - corrected 0‖ ≤
    epsilon * ‖point - normalizedSpatialCell point‖ at meanValue
  calc
    ‖ambientExtensionCellLift field point -
        ambientExtensionCellLift field (normalizedSpatialCell point) -
      closedFirstDerivative field boundaryPoint
        (point - normalizedSpatialCell point)‖ =
        ‖corrected 1 - corrected 0‖ := by
      dsimp only [corrected]
      rw [boundaryRadialSegment_one, boundaryRadialSegment_zero, map_sub]
      congr 1
      abel
    _ ≤ epsilon * ‖point - normalizedSpatialCell point‖ := meanValue

theorem boundaryRadialSegment_mem_ball {center point : SpatialCell} {radius : ℝ}
    {parameter : ℝ} (parameterMembership : parameter ∈ Icc (0 : ℝ) 1)
    (normalizedMembership : normalizedSpatialCell point ∈ Metric.ball center radius)
    (pointMembership : point ∈ Metric.ball center radius) :
    boundaryRadialSegment point parameter ∈ Metric.ball center radius := by
  have lineMembership := (convex_ball center radius).lineMap_mem
    normalizedMembership pointMembership parameterMembership
  rw [AffineMap.lineMap_apply_module'] at lineMembership
  change parameter • (point - normalizedSpatialCell point) +
      normalizedSpatialCell point ∈ Metric.ball center radius at lineMembership
  simpa only [boundaryRadialSegment, add_comm] using lineMembership

def ambientRadialRemainder {dimension : ℕ} (field : DiskCellClosedJet dimension)
    (boundaryPoint point : SpatialCell) : ComplexEuclidean dimension :=
  ambientExtensionCellLift field point -
      ambientExtensionCellLift field (normalizedSpatialCell point) -
    closedFirstDerivative field boundaryPoint
      (point - normalizedSpatialCell point)

theorem ambientRadialRemainder_isLittleO {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (boundaryPoint : SpatialCell)
    (boundary : ‖planarPart boundaryPoint‖ = 1) :
    (fun point => ambientRadialRemainder field boundaryPoint point) =o[nhds boundaryPoint]
      (fun point => point - boundaryPoint) := by
  rw [Asymptotics.isLittleO_iff]
  intro constant constantPositive
  let geometryConstant : ℝ :=
    ‖assembleSpatialCellCLM‖ * ‖planarPartCLM‖
  have geometryNonnegative : 0 ≤ geometryConstant := by
    exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
  let epsilon : ℝ := constant / (geometryConstant + 1)
  have denominatorPositive : 0 < geometryConstant + 1 := by linarith
  have epsilonPositive : 0 < epsilon :=
    div_pos constantPositive denominatorPositive
  have coefficientBound : epsilon * geometryConstant ≤ constant := by
    dsimp only [epsilon]
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ denominatorPositive).2
    nlinarith
  have closedDerivativeEvent : ∀ᶠ point in nhds boundaryPoint,
      ‖closedFirstDerivative field point -
        closedFirstDerivative field boundaryPoint‖ < epsilon := by
    have convergence : Tendsto (fun point =>
        ‖closedFirstDerivative field point -
          closedFirstDerivative field boundaryPoint‖)
        (nhds boundaryPoint) (nhds 0) := by
      have constantConvergence : Tendsto
          (fun _ : SpatialCell => closedFirstDerivative field boundaryPoint)
          (nhds boundaryPoint) (nhds (closedFirstDerivative field boundaryPoint)) :=
        tendsto_const_nhds
      have differenceConvergence :=
        ((closedFirstDerivative_continuous field).continuousAt.sub
          constantConvergence).norm
      change Tendsto (fun point =>
        ‖closedFirstDerivative field point -
          closedFirstDerivative field boundaryPoint‖)
        (nhds boundaryPoint)
        (nhds ‖closedFirstDerivative field boundaryPoint -
          closedFirstDerivative field boundaryPoint‖) at differenceConvergence
      simpa only [sub_self, norm_zero] using differenceConvergence
    exact convergence.eventually (Iio_mem_nhds epsilonPositive)
  have exteriorDerivativeEvent : ∀ᶠ point in nhds boundaryPoint,
      ‖(∑' index, exteriorSummandFirstModel field index point) -
        closedFirstDerivative field boundaryPoint‖ < epsilon := by
    have convergence : Tendsto (fun point =>
        ‖(∑' index, exteriorSummandFirstModel field index point) -
          closedFirstDerivative field boundaryPoint‖)
        (nhds boundaryPoint) (nhds 0) := by
      have constantConvergence : Tendsto
          (fun _ : SpatialCell => closedFirstDerivative field boundaryPoint)
          (nhds boundaryPoint) (nhds (closedFirstDerivative field boundaryPoint)) :=
        tendsto_const_nhds
      simpa only [sub_self, norm_zero] using
        (((exteriorFirstModel_tendsto_boundary
          field boundaryPoint boundary).sub constantConvergence).norm)
    exact convergence.eventually (Iio_mem_nhds epsilonPositive)
  have combinedDerivativeEvent : ∀ᶠ point in nhds boundaryPoint,
      ‖closedFirstDerivative field point -
          closedFirstDerivative field boundaryPoint‖ < epsilon ∧
        ‖(∑' index, exteriorSummandFirstModel field index point) -
          closedFirstDerivative field boundaryPoint‖ < epsilon :=
    closedDerivativeEvent.and exteriorDerivativeEvent
  obtain ⟨radius, radiusPositive, ballDerivativeBound⟩ :=
    (Metric.eventually_nhds_iff.mp combinedDerivativeEvent)
  have boundaryNonzero : planarPart boundaryPoint ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  have normalizedTendsto : Tendsto normalizedSpatialCell
      (nhds boundaryPoint) (nhds boundaryPoint) := by
    have convergence :=
      (normalizedSpatialCell_contDiffAt boundaryPoint boundaryNonzero).continuousAt
    change Tendsto normalizedSpatialCell (nhds boundaryPoint)
      (nhds (normalizedSpatialCell boundaryPoint)) at convergence
    rw [normalizedSpatialCell_boundary boundaryPoint boundary] at convergence
    exact convergence
  have eventuallyNormalizedInBall : ∀ᶠ point in nhds boundaryPoint,
      normalizedSpatialCell point ∈ Metric.ball boundaryPoint radius :=
    normalizedTendsto.eventually (Metric.ball_mem_nhds _ radiusPositive)
  have eventuallyPointInBall : ∀ᶠ point in nhds boundaryPoint,
      point ∈ Metric.ball boundaryPoint radius :=
    Metric.ball_mem_nhds _ radiusPositive
  have eventuallyPointNonzero : ∀ᶠ point in nhds boundaryPoint,
      planarPart point ≠ 0 :=
    continuous_planarPart.continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds boundaryNonzero)
  filter_upwards [eventuallyNormalizedInBall, eventuallyPointInBall,
    eventuallyPointNonzero] with point normalizedInBall pointInBall pointNonzero
  have radialEstimate :
      ‖ambientRadialRemainder field boundaryPoint point‖ ≤
        epsilon * ‖point - normalizedSpatialCell point‖ := by
    rcases lt_trichotomy ‖planarPart point‖ 1 with inside | pointBoundary | outside
    · apply ambient_radial_remainder_norm_le_inside
        field boundaryPoint point pointNonzero inside epsilon
      intro parameter parameterMembership
      exact (ballDerivativeBound
        (boundaryRadialSegment_mem_ball parameterMembership
          normalizedInBall pointInBall)).1.le
    · have normalizedEquality := normalizedSpatialCell_boundary point pointBoundary
      simp [ambientRadialRemainder, normalizedEquality]
    · apply ambient_radial_remainder_norm_le_outside
        field boundaryPoint point pointNonzero outside epsilon
      · exact (ballDerivativeBound normalizedInBall).1.le
      · intro parameter parameterMembership
        exact (ballDerivativeBound
          (boundaryRadialSegment_mem_ball
            ⟨parameterMembership.1.le, parameterMembership.2⟩
            normalizedInBall pointInBall)).2.le
  calc
    ‖ambientRadialRemainder field boundaryPoint point‖ ≤
        epsilon * ‖point - normalizedSpatialCell point‖ := radialEstimate
    _ ≤ epsilon * (geometryConstant * ‖point - boundaryPoint‖) := by
      exact mul_le_mul_of_nonneg_left
        (point_sub_normalized_norm_le_boundary point boundaryPoint pointNonzero boundary)
        epsilonPositive.le
    _ = (epsilon * geometryConstant) * ‖point - boundaryPoint‖ := by ring
    _ ≤ constant * ‖point - boundaryPoint‖ :=
      mul_le_mul_of_nonneg_right coefficientBound (norm_nonneg _)

theorem ambient_comp_normalized_hasFDerivAt_boundary {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    HasFDerivAt (ambientExtensionCellLift field ∘ normalizedSpatialCell)
      ((closedFirstDerivative field point).comp
        (fderiv ℝ normalizedSpatialCell point)) point := by
  have nonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  have eventuallyNonzero : ∀ᶠ candidate in nhds point,
      planarPart candidate ≠ 0 :=
    continuous_planarPart.continuousAt.eventually
      (isOpen_compl_singleton.mem_nhds nonzero)
  apply (diskCellLift_comp_normalized_hasFDerivAt_boundary
    field point boundary).congr_of_eventuallyEq
  filter_upwards [eventuallyNonzero] with candidate candidateNonzero
  exact ambientExtensionCellLift_eq_diskCellLift field
    (normalizedSpatialCell candidate)
      (normalizedSpatialCell_mem_closedUnitCylinder candidate candidateNonzero)

theorem ambientExtensionCellLift_hasFDerivAt_boundary {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) :
    HasFDerivAt (ambientExtensionCellLift field)
      (closedFirstDerivative field point) point := by
  have nonzero : planarPart point ≠ 0 := by
    intro equality
    rw [equality, norm_zero] at boundary
    norm_num at boundary
  let normalizationDerivative := fderiv ℝ normalizedSpatialCell point
  have normalizedDerivative : HasFDerivAt normalizedSpatialCell
      normalizationDerivative point := by
    exact normalizedSpatialCell_hasFDerivAt point nonzero
  have baseDerivative : HasFDerivAt
      (ambientExtensionCellLift field ∘ normalizedSpatialCell)
      ((closedFirstDerivative field point).comp normalizationDerivative) point := by
    exact ambient_comp_normalized_hasFDerivAt_boundary field point boundary
  have normalizedFieldDerivative : HasFDerivAt
      (closedFirstDerivative field point ∘ normalizedSpatialCell)
      ((closedFirstDerivative field point).comp normalizationDerivative) point :=
    (closedFirstDerivative field point).hasFDerivAt.comp point normalizedDerivative
  have radialRemainder := ambientRadialRemainder_isLittleO field point boundary
  have combinedRemainder :=
    (radialRemainder.add baseDerivative.isLittleO).sub
      normalizedFieldDerivative.isLittleO
  apply HasFDerivAt.of_isLittleO
  apply combinedRemainder.congr_left
  intro candidate
  dsimp only [ambientRadialRemainder, Function.comp_apply]
  rw [show normalizedSpatialCell point = point from
    normalizedSpatialCell_boundary point boundary]
  simp only [ContinuousLinearMap.comp_apply, map_sub]
  abel

noncomputable def ambientFirstDerivative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    SpatialCell →L[ℝ] ComplexEuclidean dimension :=
  if ‖planarPart point‖ ≤ 1 then
    closedFirstDerivative field point
  else
    ∑' index, exteriorSummandFirstModel field index point

theorem ambientExtensionCellLift_hasFDerivAt {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    HasFDerivAt (ambientExtensionCellLift field)
      (ambientFirstDerivative field point) point := by
  rcases lt_trichotomy ‖planarPart point‖ 1 with inside | boundary | outside
  · rw [ambientFirstDerivative, if_pos inside.le]
    exact ambientExtensionCellLift_hasFDerivAt_inside field point inside
  · rw [ambientFirstDerivative, if_pos boundary.le]
    exact ambientExtensionCellLift_hasFDerivAt_boundary field point boundary
  · rw [ambientFirstDerivative, if_neg (not_le.mpr outside)]
    exact ambientExtensionCellLift_hasFDerivAt_outside field point outside

theorem exteriorFirstModel_continuousAt_outside {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (outside : 1 < ‖planarPart point‖) :
    ContinuousAt (fun candidate =>
      ∑' index, exteriorSummandFirstModel field index candidate) point := by
  have smooth := exteriorSeriesCellLift_contDiffAt field point outside
  have derivativeContinuous : ContinuousAt
      (fun candidate => fderiv ℝ (exteriorSeriesCellLift field) candidate) point :=
    smooth.continuousAt_fderiv (by simp)
  have eventuallyOutside : ∀ᶠ candidate in nhds point,
      1 < ‖planarPart candidate‖ :=
    (isOpen_lt continuous_const (continuous_norm.comp continuous_planarPart)).mem_nhds
      outside
  apply derivativeContinuous.congr_of_eventuallyEq
  filter_upwards [eventuallyOutside] with candidate candidateOutside
  exact (exteriorSeriesCellLift_fderiv field candidate candidateOutside).symm

theorem ambientFirstDerivative_continuousAt {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    ContinuousAt (ambientFirstDerivative field) point := by
  rcases lt_trichotomy ‖planarPart point‖ 1 with inside | boundary | outside
  · have eventuallyInside : ∀ᶠ candidate in nhds point,
        ‖planarPart candidate‖ ≤ 1 := by
      filter_upwards [
        (isOpen_lt (continuous_norm.comp continuous_planarPart) continuous_const).mem_nhds
          inside] with candidate candidateInside
      exact candidateInside.le
    have equality : ambientFirstDerivative field =ᶠ[nhds point]
        closedFirstDerivative field := by
      filter_upwards [eventuallyInside] with candidate candidateInside
      rw [ambientFirstDerivative, if_pos candidateInside]
    exact (closedFirstDerivative_continuous field).continuousAt.congr_of_eventuallyEq equality
  · have closedConvergence : Tendsto (closedFirstDerivative field)
        (nhds point) (nhds (closedFirstDerivative field point)) :=
      (closedFirstDerivative_continuous field).continuousAt
    have exteriorConvergence : Tendsto (fun candidate =>
        ∑' index, exteriorSummandFirstModel field index candidate)
        (nhds point) (nhds (closedFirstDerivative field point)) :=
      exteriorFirstModel_tendsto_boundary field point boundary
    have combined : Tendsto (ambientFirstDerivative field)
        (nhds point) (nhds (closedFirstDerivative field point)) := by
      rw [tendsto_def]
      intro target targetNeighborhood
      filter_upwards [closedConvergence targetNeighborhood,
        exteriorConvergence targetNeighborhood] with candidate closedTarget exteriorTarget
      change ambientFirstDerivative field candidate ∈ target
      unfold ambientFirstDerivative
      split_ifs <;> assumption
    have valueEquality : ambientFirstDerivative field point =
        closedFirstDerivative field point := by
      rw [ambientFirstDerivative, if_pos boundary.le]
    change Tendsto (ambientFirstDerivative field) (nhds point)
      (nhds (ambientFirstDerivative field point))
    rw [valueEquality]
    exact combined
  · have eventuallyOutside : ∀ᶠ candidate in nhds point,
        ¬‖planarPart candidate‖ ≤ 1 := by
      filter_upwards [
        (isOpen_lt continuous_const (continuous_norm.comp continuous_planarPart)).mem_nhds
          outside] with candidate candidateOutside
      exact not_le.mpr candidateOutside
    have equality : ambientFirstDerivative field =ᶠ[nhds point]
        fun candidate => ∑' index, exteriorSummandFirstModel field index candidate := by
      filter_upwards [eventuallyOutside] with candidate candidateOutside
      rw [ambientFirstDerivative, if_neg candidateOutside]
    exact (exteriorFirstModel_continuousAt_outside field point outside).congr_of_eventuallyEq
      equality

theorem ambientFirstDerivative_continuous {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    Continuous (ambientFirstDerivative field) :=
  continuous_iff_continuousAt.mpr (ambientFirstDerivative_continuousAt field)

theorem ambientExtensionCellLift_contDiff_one {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    ContDiff ℝ 1 (ambientExtensionCellLift field) := by
  exact contDiff_one_iff_hasFDerivAt.mpr
    ⟨ambientFirstDerivative field, ambientFirstDerivative_continuous field,
      ambientExtensionCellLift_hasFDerivAt field⟩

theorem ambientExtensionCellLift_fderiv {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    fderiv ℝ (ambientExtensionCellLift field) point =
      ambientFirstDerivative field point :=
  (ambientExtensionCellLift_hasFDerivAt field point).fderiv

theorem closedFirstDerivative_basis {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (coordinate : Fin 3) :
    closedFirstDerivative field point (spatialCellBasis coordinate) =
      closedMixedDerivative field 1 (fun _ => coordinate) (retractedDiskCell point) := by
  simp only [closedFirstDerivative, sum_apply, ContinuousLinearMap.smulRight_apply,
    spatialCellCoordinateCLM_apply, spatialCellBasis]
  rw [Finset.sum_eq_single coordinate]
  · simp
  · intro other _ otherNe
    simp [Pi.single_eq_of_ne otherNe]
  · simp

theorem mixedCartesianDerivative_one_boundary {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (boundary : ‖planarPart point‖ = 1) (word : MixedCartesianWord 1) :
    mixedCartesianDerivative 1 word (ambientExtensionCellLift field) point =
      closedMixedDerivative field 1 word
        (diskCellPoint point (by
          change ‖planarPart point‖ ≤ 1
          exact boundary.le)) := by
  simp only [mixedCartesianDerivative, iteratedFDeriv_one_apply]
  rw [ambientExtensionCellLift_fderiv, ambientFirstDerivative,
    if_pos boundary.le, closedFirstDerivative_basis,
    retractedDiskCell_eq_diskCellPoint point boundary.le]
  congr
  funext position
  exact Subsingleton.elim position 0 ▸ rfl

theorem ambientExtensionCellLift_contDiffOn_one_gluingCollar {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    ContDiffOn ℝ 1 (ambientExtensionCellLift field) gluingCollar :=
  (ambientExtensionCellLift_contDiff_one field).contDiffOn

end Grad.DiskExtension.Operator
