import ClosedJetOrthogonal
import FC3Coordinates

noncomputable section

open Set MeasureTheory Grad.ClosedJets Grad.CartesianState
open Grad.RepresentedKernel.SpatialProduct Grad.GaugeCoefficients.Radial
open Grad.KernelPullback.Domain
open scoped BigOperators ContDiff Topology

namespace Grad.Constraints

theorem cartesianWeight_orthogonal (parameters : PhaseParameters) (cell : ℤ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (point : SpatialPlane) :
    cartesianWeight parameters cell (orthogonal point) = cartesianWeight parameters cell point := by
  simp only [cartesianWeight_exp, cartesianPhase_formula, orthogonal.norm_map]

theorem orthogonalJet_phaseWeighted {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ)
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane) (field : ClosedJet dimension) :
    orthogonalJet orthogonal (phaseWeightedJet parameters cell field) =
      phaseWeightedJet parameters cell (orthogonalJet orthogonal field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change (phaseWeightedJet parameters cell field).value
    (orthogonalClosedPoint orthogonal point) = _
  rw [phaseWeightedJet_spec, phaseWeightedJet_spec]
  change cartesianWeight parameters cell (orthogonal point.val) •
    field.value (orthogonalClosedPoint orthogonal point) =
      cartesianWeight parameters cell point.val •
        field.value (orthogonalClosedPoint orthogonal point)
  rw [cartesianWeight_orthogonal]

def closedValueL2Linear (dimension : ℕ) :
    C(ClosedDisk, ComplexEuclidean dimension) →ₗ[ℂ] DiskL2 dimension where
  toFun := closedContinuousToDiskL2
  map_add' := closedContinuousToDiskL2_add
  map_smul' := closedContinuousToDiskL2_smul

theorem lift_comp_orthogonalClosedMap {dimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    closedDiskLift (field.comp (orthogonalClosedMap orthogonal)) =
      fun point => closedDiskLift field (orthogonal point) := by
  funext point
  have invariant : orthogonal point ∈ closedUnitDisk ↔ point ∈ closedUnitDisk := by
    change ‖orthogonal point‖ ≤ 1 ↔ ‖point‖ ≤ 1
    rw [orthogonal.norm_map]
  by_cases inside : point ∈ closedUnitDisk
  · simp only [closedDiskLift, inside, invariant.mpr inside, dite_true]
    rfl
  · simp only [closedDiskLift, inside, mt invariant.mp inside, dite_false]

theorem closedValueL2_orthogonal {dimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    closedContinuousToDiskL2 (field.comp (orthogonalClosedMap orthogonal)) =
      Lp.compMeasurePreservingₗᵢ ℂ orthogonal
        (domainMeasurePreserving openUnitDisk openUnitDisk_isOpen.measurableSet orthogonal
          (openUnitDisk_invariant orthogonal))
        (closedContinuousToDiskL2 field) := by
  apply Lp.ext
  have pulled := (domainMeasurePreserving openUnitDisk openUnitDisk_isOpen.measurableSet
    orthogonal (openUnitDisk_invariant orthogonal)).quasiMeasurePreserving.ae_eq_comp
      (closedContinuousToDiskL2_ae field)
  filter_upwards [closedContinuousToDiskL2_ae (field.comp (orthogonalClosedMap orthogonal)),
    Lp.coeFn_compMeasurePreserving (closedContinuousToDiskL2 field)
      (domainMeasurePreserving openUnitDisk openUnitDisk_isOpen.measurableSet orthogonal
        (openUnitDisk_invariant orthogonal)), pulled] with point leftAt rightAt sourceAt
  exact leftAt.trans ((congrFun (lift_comp_orthogonalClosedMap orthogonal field) point).trans
    (sourceAt.symm.trans rightAt.symm))

theorem closedValueL2_orthogonal_norm {dimension : ℕ}
    (orthogonal : SpatialPlane ≃ₗᵢ[ℝ] SpatialPlane)
    (field : C(ClosedDisk, ComplexEuclidean dimension)) :
    ‖closedContinuousToDiskL2 (field.comp (orthogonalClosedMap orthogonal))‖ =
      ‖closedContinuousToDiskL2 field‖ := by
  rw [closedValueL2_orthogonal]
  exact (Lp.compMeasurePreservingₗᵢ ℂ orthogonal
    (domainMeasurePreserving openUnitDisk openUnitDisk_isOpen.measurableSet orthogonal
      (openUnitDisk_invariant orthogonal))).norm_map _

end Grad.Constraints
