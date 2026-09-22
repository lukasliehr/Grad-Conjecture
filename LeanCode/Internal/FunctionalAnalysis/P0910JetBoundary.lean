import P0910Seam
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section

open Filter Set
open scoped BigOperators ContDiff Topology

namespace Grad.DiskExtension.Operator

open Grad.ClosedJets
open Grad.DiskExtension.Seeley

noncomputable def spatialCellCoordinateCLM (coordinate : Fin 3) :
    SpatialCell →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) coordinate

@[simp] theorem spatialCellCoordinateCLM_apply (coordinate : Fin 3)
    (point : SpatialCell) : spatialCellCoordinateCLM coordinate point = point coordinate := rfl

theorem spatialCell_basis_expansion (point : SpatialCell) :
    ∑ coordinate : Fin 3, point coordinate • spatialCellBasis coordinate = point := by
  ext target
  simp [spatialCellBasis, Pi.single_apply]

theorem openUnitCylinder_eq_preimage_ball :
    openUnitCylinder = planarPartCLM ⁻¹' Metric.ball (0 : SpatialPlane) 1 := by
  ext point
  change ‖planarPart point‖ < 1 ↔ dist (planarPartCLM point) 0 < 1
  rw [planarPartCLM_apply, dist_zero_right]

theorem closedUnitCylinder_eq_preimage_closedBall :
    closedUnitCylinder = planarPartCLM ⁻¹' Metric.closedBall (0 : SpatialPlane) 1 := by
  ext point
  change ‖planarPart point‖ ≤ 1 ↔ dist (planarPartCLM point) 0 ≤ 1
  rw [planarPartCLM_apply, dist_zero_right]

theorem planarPartCLM_surjective : Function.Surjective planarPartCLM := by
  intro point
  refine ⟨assembleSpatialCell point 0, ?_⟩
  exact planarPart_assembleSpatialCell point 0

theorem closure_openUnitCylinder : closure openUnitCylinder = closedUnitCylinder := by
  rw [openUnitCylinder_eq_preimage_ball,
    planarPartCLM.closure_preimage planarPartCLM_surjective,
    closure_ball (0 : SpatialPlane) (by norm_num : (1 : ℝ) ≠ 0),
    ← closedUnitCylinder_eq_preimage_closedBall]

theorem openUnitCylinder_convex : Convex ℝ openUnitCylinder := by
  rw [openUnitCylinder_eq_preimage_ball]
  exact (convex_ball (0 : SpatialPlane) 1).linear_preimage planarPartLinear

noncomputable def closedFirstDerivative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    SpatialCell →L[ℝ] ComplexEuclidean dimension :=
  ∑ coordinate : Fin 3,
    (spatialCellCoordinateCLM coordinate).smulRight
      (closedMixedDerivative field 1 (fun _ => coordinate) (retractedDiskCell point))

theorem closedFirstDerivative_continuous {dimension : ℕ}
    (field : DiskCellClosedJet dimension) :
    Continuous (closedFirstDerivative field) := by
  apply continuous_finsetSum
  intro coordinate _
  exact ((ContinuousLinearMap.smulRightL ℝ SpatialCell (ComplexEuclidean dimension))
    (spatialCellCoordinateCLM coordinate)).continuous.comp
      ((closedMixedDerivative field 1 (fun _ => coordinate)).continuous.comp
        continuous_retractedDiskCell)

theorem closedFirstDerivative_eq_fderiv {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (membership : point ∈ openUnitCylinder) :
    closedFirstDerivative field point = fderiv ℝ (diskCellLift field.value) point := by
  have closedMembership := openCylinderMembershipClosed point membership
  have sampleEquality := retractedDiskCell_eq_diskCellPoint point closedMembership
  apply ContinuousLinearMap.ext
  intro direction
  simp only [closedFirstDerivative, sum_apply,
    ContinuousLinearMap.smulRight_apply, spatialCellCoordinateCLM_apply]
  calc
    ∑ coordinate : Fin 3,
        direction coordinate •
          closedMixedDerivative field 1 (fun _ => coordinate) (retractedDiskCell point) =
        ∑ coordinate : Fin 3, direction coordinate •
          fderiv ℝ (diskCellLift field.value) point (spatialCellBasis coordinate) := by
            apply Finset.sum_congr rfl
            intro coordinate _
            rw [sampleEquality,
              closedMixedDerivative_spec field 1 (fun _ => coordinate) point membership]
            simp only [mixedCartesianDerivative, iteratedFDeriv_one_apply]
    _ = fderiv ℝ (diskCellLift field.value) point
        (∑ coordinate : Fin 3, direction coordinate • spatialCellBasis coordinate) := by
          rw [map_sum]
          simp only [map_smul]
    _ = fderiv ℝ (diskCellLift field.value) point direction := by
      rw [spatialCell_basis_expansion]

theorem diskCellLift_eq_retractedDiskCell {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (membership : point ∈ closedUnitCylinder) :
    diskCellLift field.value point = field.value (retractedDiskCell point) := by
  rw [diskCellLift, dif_pos membership,
    retractedDiskCell_eq_diskCellPoint point membership]

theorem diskCellLift_continuousWithinAt_open_at_closed {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell)
    (membership : point ∈ closedUnitCylinder) :
    ContinuousWithinAt (diskCellLift field.value) openUnitCylinder point := by
  have retractedContinuous : Continuous
      (fun candidate : SpatialCell => field.value (retractedDiskCell candidate)) :=
    field.value.continuous.comp continuous_retractedDiskCell
  apply retractedContinuous.continuousAt.continuousWithinAt.congr_of_eventuallyEq
  · filter_upwards [self_mem_nhdsWithin] with candidate candidateMembership
    exact diskCellLift_eq_retractedDiskCell field candidate
      (openCylinderMembershipClosed candidate candidateMembership)
  · exact diskCellLift_eq_retractedDiskCell field point membership

theorem fderiv_diskCellLift_tendsto_closedFirstDerivative {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    Tendsto (fun candidate => fderiv ℝ (diskCellLift field.value) candidate)
      (𝓝[openUnitCylinder] point) (𝓝 (closedFirstDerivative field point)) := by
  apply ((closedFirstDerivative_continuous field).continuousAt.mono_left
    inf_le_left).congr'
  filter_upwards [self_mem_nhdsWithin] with candidate candidateMembership
  exact closedFirstDerivative_eq_fderiv field candidate candidateMembership

theorem diskCellLift_hasFDerivWithinAt_closed {dimension : ℕ}
    (field : DiskCellClosedJet dimension) (point : SpatialCell) :
    HasFDerivWithinAt (diskCellLift field.value) (closedFirstDerivative field point)
      closedUnitCylinder point := by
  rw [← closure_openUnitCylinder]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
  · exact field.smoothInterior.differentiableOn (by simp)
  · exact openUnitCylinder_convex
  · exact openUnitCylinder_isOpen
  · intro candidate candidateClosure
    rw [closure_openUnitCylinder] at candidateClosure
    exact diskCellLift_continuousWithinAt_open_at_closed field candidate candidateClosure
  · exact fderiv_diskCellLift_tendsto_closedFirstDerivative field point

end Grad.DiskExtension.Operator
