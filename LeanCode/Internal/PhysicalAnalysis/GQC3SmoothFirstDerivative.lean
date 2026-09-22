import GQC2CoefficientCoordinates

noncomputable section

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 200000

open Set Filter
open scoped Topology ContDiff

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem smoothOperator_zero {input output : ℕ} (field : SmoothOperatorJet input output) :
    smoothOperatorDerivative field (0, 0) = field.value := by
  apply continuousMap_eq_of_openDisk
  intro point inside
  change (Classical.choose (field.derivativeExists (0, 0))) point = _
  rw [Classical.choose_spec (field.derivativeExists (0, 0)) point inside]
  exact closedLift_value _ point.val inside

theorem smoothOperator_first_basis {input output : ℕ} (field : SmoothOperatorJet input output)
    (point : SpatialPlane) (inside : point ∈ openUnitDisk) (coordinate : Fin 2) :
    fderiv ℝ (closedDiskLift field.value) point (spatialBasis coordinate) =
      smoothOperatorDerivative field (derivativeMultiIndex (firstCoordinateIndex coordinate))
        ⟨point, openDiskMembershipClosed point inside⟩ := by
  fin_cases coordinate
  · have equality := Classical.choose_spec (field.derivativeExists (1, 0))
      ⟨point, openDiskMembershipClosed point inside⟩ inside
    have actual : cartesianMultiDerivative (1, 0) (closedDiskLift field.value) point =
        fderiv ℝ (closedDiskLift field.value) point (spatialBasis 0) := by
      exact iteratedFDeriv_one_apply (fun position : Fin 1 => spatialBasis (cartesianMultiIndexWord (1, 0) position))
    rw [actual] at equality
    exact equality.symm
  · have equality := Classical.choose_spec (field.derivativeExists (0, 1))
      ⟨point, openDiskMembershipClosed point inside⟩ inside
    have actual : cartesianMultiDerivative (0, 1) (closedDiskLift field.value) point =
        fderiv ℝ (closedDiskLift field.value) point (spatialBasis 1) := by
      exact iteratedFDeriv_one_apply (fun position : Fin 1 => spatialBasis (cartesianMultiIndexWord (0, 1) position))
    rw [actual] at equality
    exact equality.symm

theorem linear_eq_planarDerivative {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (mapping : SpatialPlane →L[ℝ] Value) :
    mapping = planarDerivative (mapping (spatialBasis 0)) (mapping (spatialBasis 1)) := by
  apply ContinuousLinearMap.ext
  intro direction
  have decomposition : direction = direction 0 • spatialBasis 0 + direction 1 • spatialBasis 1 := by
    apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [spatialBasis]
  rw [planarDerivative_apply]
  conv_lhs => rw [decomposition, map_add, map_smul, map_smul]

theorem smoothOperator_first {input output : ℕ} (field : SmoothOperatorJet input output)
    (point : SpatialPlane) (inside : point ∈ openUnitDisk) :
    HasFDerivAt (closedDiskLift field.value)
      (planarDerivative
        (closedDiskLift (smoothOperatorDerivative field (1, 0)) point)
        (closedDiskLift (smoothOperatorDerivative field (0, 1)) point)) point := by
  have derivative := (field.smoothInterior.differentiableOn (by simp) point inside).differentiableAt
    (openUnitDisk_isOpen.mem_nhds inside) |>.hasFDerivAt
  have equality : fderiv ℝ (closedDiskLift field.value) point =
      planarDerivative (closedDiskLift (smoothOperatorDerivative field (1, 0)) point)
        (closedDiskLift (smoothOperatorDerivative field (0, 1)) point) := by
    rw [linear_eq_planarDerivative (fderiv ℝ (closedDiskLift field.value) point), smoothOperator_first_basis field point inside 0,
      smoothOperator_first_basis field point inside 1,
      closedLift_value _ point inside, closedLift_value _ point inside]
    rfl
  rwa [equality] at derivative

end Grad.GaugeCoefficients.Physical.Compensated
