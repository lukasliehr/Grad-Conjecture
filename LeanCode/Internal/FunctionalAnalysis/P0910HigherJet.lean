import P0910FirstSeam
import Mathlib.LinearAlgebra.Multilinear.Basis

noncomputable section

open Filter Set
open scoped BigOperators ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets
open Grad.DiskExtension.Seeley

noncomputable def spatialCellWordCoefficient {order : ℕ}
    (word : MixedCartesianWord order) : SpatialCell [×order]→L[ℝ] ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebraFin ℝ order ℝ).compContinuousLinearMap
    (fun position => spatialCellCoordinateCLM (word position))

@[simp] theorem spatialCellWordCoefficient_apply {order : ℕ}
    (word : MixedCartesianWord order) (directions : Fin order → SpatialCell) :
    spatialCellWordCoefficient word directions =
      (List.ofFn fun position => directions position (word position)).prod := by
  simp [spatialCellWordCoefficient,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]

@[simp] theorem spatialCellWordCoefficient_basis {order : ℕ}
    (coefficientWord word : MixedCartesianWord order) :
    spatialCellWordCoefficient coefficientWord
        (fun position => spatialCellBasis (word position)) =
      if coefficientWord = word then 1 else 0 := by
  classical
  rw [spatialCellWordCoefficient_apply]
  split_ifs with equality
  · subst coefficientWord
    simp [spatialCellBasis]
  · apply List.prod_eq_zero
    rw [List.mem_ofFn]
    have differingPosition : ∃ position, coefficientWord position ≠ word position := by
      by_contra noDifferingPosition
      apply equality
      funext position
      by_contra positionDiffers
      exact (not_exists.mp noDifferingPosition position) positionDiffers
    obtain ⟨position, positionDiffers⟩ := differingPosition
    refine ⟨position, ?_⟩
    simp only [spatialCellBasis, Pi.single_apply]
    exact if_neg positionDiffers

noncomputable def closedHigherDerivative {dimension order : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension :=
  ∑ word : MixedCartesianWord order,
    (spatialCellWordCoefficient word).smulRight
      (closedMixedDerivative field order word (retractedDiskCell point))

theorem closedHigherDerivative_continuous {dimension order : ℕ}
    (field : DiskCellClosedJet dimension) :
    Continuous (closedHigherDerivative (order := order) field) := by
  apply continuous_finsetSum
  intro word _
  exact ((ContinuousMultilinearMap.smulRightL ℝ
      (fun _ : Fin order => SpatialCell) (ComplexEuclidean dimension)
      (spatialCellWordCoefficient word)).continuous.comp
        ((closedMixedDerivative field order word).continuous.comp
          continuous_retractedDiskCell))

@[simp] theorem closedHigherDerivative_basis {dimension order : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (word : MixedCartesianWord order) :
    closedHigherDerivative field point
        (fun position => spatialCellBasis (word position)) =
      closedMixedDerivative field order word (retractedDiskCell point) := by
  classical
  rw [closedHigherDerivative, sum_apply]
  rw [Finset.sum_eq_single word]
  · rw [ContinuousMultilinearMap.smulRight_apply,
      spatialCellWordCoefficient_basis, if_pos rfl, one_smul]
  · intro other _ otherNe
    rw [ContinuousMultilinearMap.smulRight_apply,
      spatialCellWordCoefficient_basis, if_neg otherNe, zero_smul]
  · simp

theorem continuousMultilinearMap_ext_spatialCellBasis
    {dimension order : ℕ}
    (first second : SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension)
    (basisEquality : ∀ word : MixedCartesianWord order,
      first (fun position => spatialCellBasis (word position)) =
        second (fun position => spatialCellBasis (word position))) :
    first = second := by
  apply ContinuousMultilinearMap.toMultilinearMap_injective
  apply Module.Basis.ext_multilinear
    (fun _ : Fin order => PiLp.basisFun 2 ℝ (Fin 3))
  intro word
  rw [show (fun position => PiLp.basisFun 2 ℝ (Fin 3) (word position)) =
      fun position => spatialCellBasis (word position) by
    funext position
    rw [PiLp.basisFun_apply]
    rfl]
  exact basisEquality word

theorem closedHigherDerivative_eq_iteratedFDeriv {dimension order : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (membership : point ∈ openUnitCylinder) :
    closedHigherDerivative field point =
      iteratedFDeriv ℝ order (diskCellLift field.value) point := by
  apply continuousMultilinearMap_ext_spatialCellBasis
  intro word
  rw [closedHigherDerivative_basis,
    retractedDiskCell_eq_diskCellPoint point
      (openCylinderMembershipClosed point membership)]
  exact closedMixedDerivative_spec field order word point membership

theorem iteratedFDeriv_diskCellLift_tendsto_closedHigherDerivative
    {dimension order : ℕ} (field : DiskCellClosedJet dimension)
    (point : SpatialCell) :
    Tendsto (fun candidate =>
      iteratedFDeriv ℝ order (diskCellLift field.value) candidate)
      (𝓝[openUnitCylinder] point)
      (𝓝 (closedHigherDerivative (order := order) field point)) := by
  apply ((closedHigherDerivative_continuous (order := order) field).continuousAt.mono_left
    inf_le_left).congr'
  filter_upwards [self_mem_nhdsWithin] with candidate candidateMembership
  exact (closedHigherDerivative_eq_iteratedFDeriv
    (order := order) field candidate candidateMembership)

theorem closedHigherDerivative_fderiv_interior {dimension order : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (membership : point ∈ openUnitCylinder) :
    fderiv ℝ (closedHigherDerivative (order := order) field) point =
      (closedHigherDerivative (order := order + 1) field point).curryLeft := by
  have localEquality : closedHigherDerivative (order := order) field =ᶠ[𝓝 point]
      iteratedFDeriv ℝ order (diskCellLift field.value) := by
    filter_upwards [openUnitCylinder_isOpen.mem_nhds membership] with candidate
      candidateMembership
    exact closedHigherDerivative_eq_iteratedFDeriv
      (order := order) field candidate candidateMembership
  rw [localEquality.fderiv_eq, fderiv_iteratedFDeriv]
  rw [closedHigherDerivative_eq_iteratedFDeriv
    (order := order + 1) field point membership]
  rfl

theorem closedHigherDerivative_differentiableAt_interior {dimension order : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (membership : point ∈ openUnitCylinder) :
    DifferentiableAt ℝ (closedHigherDerivative (order := order) field) point := by
  have localEquality : closedHigherDerivative (order := order) field =ᶠ[𝓝 point]
      iteratedFDeriv ℝ order (diskCellLift field.value) := by
    filter_upwards [openUnitCylinder_isOpen.mem_nhds membership] with candidate
      candidateMembership
    exact closedHigherDerivative_eq_iteratedFDeriv
      (order := order) field candidate candidateMembership
  have smoothAt := (field.smoothInterior point membership).contDiffAt
    (openUnitCylinder_isOpen.mem_nhds membership)
  exact (smoothAt.differentiableAt_iteratedFDeriv (m := order)
    (WithTop.coe_lt_coe.mpr
      (show (order : ℕ∞) < ⊤ from WithTop.coe_lt_top order))).congr_of_eventuallyEq
        localEquality

theorem closedHigherDerivative_hasFDerivWithinAt_closed {dimension order : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    HasFDerivWithinAt (closedHigherDerivative (order := order) field)
      (closedHigherDerivative (order := order + 1) field point).curryLeft
      closedUnitCylinder point := by
  rw [← closure_openUnitCylinder]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
  · intro candidate candidateMembership
    exact (closedHigherDerivative_differentiableAt_interior
      (order := order) field candidate candidateMembership).differentiableWithinAt
  · exact openUnitCylinder_convex
  · exact openUnitCylinder_isOpen
  · intro candidate _
    exact (closedHigherDerivative_continuous
      (order := order) field).continuousAt.continuousWithinAt
  · have curriedContinuous : Continuous (fun candidate =>
        (closedHigherDerivative (order := order + 1) field candidate).curryLeft) :=
      (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (order + 1) => SpatialCell)
        (ComplexEuclidean dimension)).continuous.comp
          (closedHigherDerivative_continuous (order := order + 1) field)
    apply (curriedContinuous.continuousAt.mono_left inf_le_left).congr'
    filter_upwards [self_mem_nhdsWithin] with candidate candidateMembership
    exact (closedHigherDerivative_fderiv_interior
      (order := order) field candidate candidateMembership).symm

theorem closedHigherDerivative_zero_curry {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    (closedHigherDerivative (order := 0) field point).curry0 =
      field.value (retractedDiskCell point) := by
  rw [ContinuousMultilinearMap.curry0_apply]
  have basisValue := closedHigherDerivative_basis
    (order := 0) field point emptyMixedCartesianWord
  rw [closedMixedDerivative_zero_order] at basisValue
  exact basisValue

noncomputable def closedTaylorSeries {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    FormalMultilinearSeries ℝ SpatialCell (ComplexEuclidean dimension) :=
  fun order => closedHigherDerivative (order := order) field point

theorem diskCellLift_hasFTaylorSeriesUpToOn_closed {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    HasFTaylorSeriesUpToOn (𝕜 := ℝ) ∞ (diskCellLift field.value)
      (closedTaylorSeries field) closedUnitCylinder := by
  constructor
  · intro point pointMembership
    rw [closedTaylorSeries, closedHigherDerivative_zero_curry,
      diskCellLift_eq_retractedDiskCell field point pointMembership]
  · intro order _ point _
    exact closedHigherDerivative_hasFDerivWithinAt_closed
      (order := order) field point
  · intro order _
    exact (closedHigherDerivative_continuous
      (order := order) field).continuousOn

theorem diskCellLift_contDiffOn_closed {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    ContDiffOn ℝ ∞ (diskCellLift field.value) closedUnitCylinder :=
  (diskCellLift_hasFTaylorSeriesUpToOn_closed field).contDiffOn

end Grad.DiskExtension.Operator
