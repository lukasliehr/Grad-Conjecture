import FP17DerivativeShift
import FC2WeightedJet
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState

theorem ray_interior (point : ClosedDisk) {scale : ℝ} (inside : scale ∈ Ioo (0 : ℝ) 1) :
    scale • point.val ∈ openUnitDisk := by
  change ‖scale • point.val‖ < 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos inside.1]
  exact lt_of_le_of_lt (mul_le_of_le_one_right inside.1.le point.property) inside.2

theorem closedDerivativeEvaluation_continuous {dimension order : ℕ}
    (field : ClosedJet dimension) (directions : Fin order → SpatialPlane) :
    Continuous (closedPlaneDerivativeEvaluation field directions) :=
  (ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => SpatialPlane)
    (ComplexEuclidean dimension) directions).continuous.comp
      (closedPlaneHigherDerivative_continuous field)

theorem closedDerivativeEvaluation_differentiableAt {dimension order : ℕ}
    (field : ClosedJet dimension) (directions : Fin order → SpatialPlane)
    {point : SpatialPlane} (inside : point ∈ openUnitDisk) :
    DifferentiableAt ℝ (closedPlaneDerivativeEvaluation field directions) point := by
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin order => SpatialPlane)
    (ComplexEuclidean dimension) directions).differentiableAt.comp point
      ((closedPlaneHigherDerivative_contDiffAt_interior field point inside).differentiableAt (by simp))

/-- The radial fundamental theorem includes both actual closed-disk endpoints.
No derivative of the zero extension across the boundary is used. -/
theorem closedJet_ray_integral {dimension order : ℕ}
    (field : ClosedJet dimension) (directions : Fin order → SpatialPlane) (point : ClosedDisk) :
    (∫ scale in (0 : ℝ)..1,
      closedPlaneDerivativeEvaluation field (Fin.cons point.val directions) (scale • point.val)) =
      closedPlaneDerivativeEvaluation field directions point.val -
        closedPlaneDerivativeEvaluation field directions 0 := by
  let value : ℝ → ComplexEuclidean dimension := fun scale =>
    closedPlaneDerivativeEvaluation field directions (scale • point.val)
  have valueContinuous : Continuous value :=
    (closedDerivativeEvaluation_continuous field directions).comp (continuous_id.smul continuous_const)
  have derivativeContinuous : Continuous (fun scale : ℝ =>
      closedPlaneDerivativeEvaluation field (Fin.cons point.val directions) (scale • point.val)) :=
    (closedDerivativeEvaluation_continuous field _).comp (continuous_id.smul continuous_const)
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (f := value) zero_lt_one ?_ (derivativeContinuous.intervalIntegrable 0 1) ?_ ?_
  · intro scale inside
    have derivative := (closedDerivativeEvaluation_differentiableAt field directions
      (ray_interior point inside)).hasFDerivAt.comp_hasDerivAt scale
        ((hasDerivAt_id scale).smul_const point.val)
    apply derivative.congr_deriv
    simpa only [one_smul] using
      (closedPlaneDerivativeEvaluation_fderiv field directions (scale • point.val)
        point.val (ray_interior point inside))
  · simpa [value] using tendsto_nhdsWithin_of_tendsto_nhds
      (valueContinuous.continuousAt (x := 0))
  · simpa [value] using tendsto_nhdsWithin_of_tendsto_nhds
      (valueContinuous.continuousAt (x := 1))

theorem closedDerivativeEvaluation_zero {dimension : ℕ}
    (field : ClosedJet dimension) (point : SpatialPlane) :
    closedPlaneDerivativeEvaluation field (fun index : Fin 0 => Fin.elim0 index) point =
      field.value (ambientClosedDisk point) := by
  have equality := closedPlaneHigherDerivative_basis (order := 0) field point emptyCartesianWord
  have directions : (fun index : Fin 0 => Fin.elim0 index) =
      (fun index => spatialBasis (emptyCartesianWord index)) := by funext index; exact Fin.elim0 index
  rw [closedPlaneDerivativeEvaluation, directions]
  simpa only [closedDerivative_zero_order] using equality

theorem ambientClosedDisk_coe (point : ClosedDisk) : ambientClosedDisk point.val = point := by
  apply Subtype.ext
  exact ambientClosedDisk_val_of_mem point.property

/-- Flat division is represented by an integral of the derivative of the
whole weighted field, not by pulling its weight through the integral. -/
theorem weighted_flat_ray_integral {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (flat : field.value (ambientClosedDisk 0) = 0) (point : ClosedDisk) :
    (∫ scale in (0 : ℝ)..1,
      closedPlaneDerivativeEvaluation (phaseWeightedJet parameters cell field)
        (Fin.cons point.val (fun index : Fin 0 => Fin.elim0 index)) (scale • point.val)) =
      cartesianWeight parameters cell point.val • field.value point := by
  rw [closedJet_ray_integral, closedDerivativeEvaluation_zero,
    closedDerivativeEvaluation_zero, ambientClosedDisk_coe,
    phaseWeightedJet_value, phaseWeightedJet_value, flat, smul_zero, sub_zero]

end Grad.SourceCollarDivision
