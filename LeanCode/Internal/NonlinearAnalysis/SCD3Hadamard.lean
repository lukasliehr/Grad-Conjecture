import SCD2RayAverage
import BT6OriginalDensity

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

theorem firstDerivative_direction {dimension : ℕ} (field : ClosedJet dimension)
    (point : ClosedDisk) (direction : SpatialPlane) :
    closedPlaneDerivativeEvaluation field
      (Fin.cons direction (fun index : Fin 0 => Fin.elim0 index)) point.val =
      ∑ coordinate : Fin 2, (direction coordinate) •
        closedDerivative field 1 (fun _ => coordinate) point := by
  have expansion : (∑ coordinate : Fin 2,
      (direction coordinate) • spatialBasis coordinate) = direction := by
    ext coordinate
    fin_cases coordinate <;> simp [Fin.sum_univ_two, spatialBasis]
  rw [closedPlaneDerivativeEvaluation, ← smoothClosedExtension_higherDerivative field point,
    iteratedFDeriv_one_apply]
  change (fderiv ℝ (smoothClosedExtension field) point.val) direction = _
  conv_lhs => rw [← expansion]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [map_smul]
  congr 1
  have derivative := smoothClosedExtension_derivative field (fun _ : Fin 1 => coordinate) point
  simpa only [cartesianDerivative, iteratedFDeriv_one_apply] using derivative

theorem partial_rayAverage_value {dimension : ℕ} (field : ClosedJet dimension)
    (coordinate : Fin 2) (point : ClosedDisk) :
    rayAverageValue (shiftedClosedJet field (fun _ : Fin 1 => coordinate)) point.val =
      ∫ scale in (0 : ℝ)..1,
        closedDerivative field 1 (fun _ => coordinate) (ambientClosedDisk (scale • point.val)) := by
  rw [rayAverageValue, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
  apply intervalIntegral.integral_congr
  intro scale inside
  dsimp only
  have member : scale ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using inside
  have ambient : ambientClosedDisk (scale • point.val) =
      dilationPoint scale member.1 member.2 point := by
    apply Subtype.ext
    exact ambientClosedDisk_val_of_mem (dilation_mem_closed member.1 member.2 point)
  rw [ambient]
  exact smoothClosedExtension_value (shiftedClosedJet field (fun _ : Fin 1 => coordinate))
    (dilationPoint scale member.1 member.2 point)

/-- Exact closed-disk Hadamard identity in the two fixed Cartesian directions. -/
theorem closedJet_hadamard {dimension : ℕ} (field : ClosedJet dimension) (point : ClosedDisk) :
    field.value point - field.value (ambientClosedDisk 0) =
      ∑ coordinate : Fin 2, (point.val coordinate) •
        rayAverageValue (shiftedClosedJet field (fun _ : Fin 1 => coordinate)) point.val := by
  have ray := closedJet_ray_integral field (fun index : Fin 0 => Fin.elim0 index) point
  rw [closedDerivativeEvaluation_zero, closedDerivativeEvaluation_zero, ambientClosedDisk_coe] at ray
  rw [← ray]
  have continuousPartial : ∀ coordinate : Fin 2, Continuous (fun scale : ℝ =>
      closedDerivative field 1 (fun _ => coordinate) (ambientClosedDisk (scale • point.val))) := by
    intro coordinate
    exact (closedDerivative field 1 _).continuous.comp
      (continuous_ambientClosedDisk.comp (continuous_id.smul continuous_const))
  calc
    _ = ∫ scale in (0 : ℝ)..1, ∑ coordinate : Fin 2, (point.val coordinate) •
        closedDerivative field 1 (fun _ => coordinate) (ambientClosedDisk (scale • point.val)) := by
      apply intervalIntegral.integral_congr
      intro scale inside
      have member : scale ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using inside
      have ambient : (ambientClosedDisk (scale • point.val)).val = scale • point.val :=
        ambientClosedDisk_val_of_mem (dilation_mem_closed member.1 member.2 point)
      convert firstDerivative_direction field (ambientClosedDisk (scale • point.val)) point.val using 1
      rw [ambient]
    _ = ∑ coordinate : Fin 2, (point.val coordinate) •
        (∫ scale in (0 : ℝ)..1,
          closedDerivative field 1 (fun _ => coordinate) (ambientClosedDisk (scale • point.val))) := by
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro coordinate _
        rw [intervalIntegral.integral_smul]
      · intro coordinate _
        exact ((continuous_const : Continuous fun _ : ℝ => point.val coordinate).smul
          (continuousPartial coordinate)).intervalIntegrable 0 1
    _ = _ := by simp_rw [partial_rayAverage_value]

end Grad.SourceCollarDivision
