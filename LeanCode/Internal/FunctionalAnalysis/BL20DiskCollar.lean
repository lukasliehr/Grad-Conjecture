import BL19KernelConjugation

noncomputable section

open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology

namespace Grad.BoundaryLift

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.DiskExtension.Operator

theorem weightedFiniteKernelField_zero_inner {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension) (point : SpatialPlane)
    (inside : ‖point‖ ≤ (7 / 8 : ℝ)) : weightedFiniteKernelField parameters cell modes values point = 0 := by
  unfold weightedFiniteKernelField finiteKernelField
  simp_rw [boundaryKernel_zero_inner _ point inside, zero_smul]
  rw [Finset.sum_const_zero, smul_zero]

theorem weightedFiniteKernelField_derivative_zero {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (modes : Finset ℤ) (values : ℤ → ComplexEuclidean dimension) (order : ℕ) (point : SpatialPlane)
    (inside : ‖point‖ ≤ (3 / 4 : ℝ)) :
    iteratedFDeriv ℝ order (weightedFiniteKernelField parameters cell modes values) point = 0 := by
  have pointIn : point ∈ Metric.ball (0 : SpatialPlane) (7 / 8 : ℝ) := by
    rw [Metric.mem_ball, dist_zero_right]
    linarith
  have agreement : weightedFiniteKernelField parameters cell modes values =ᶠ[𝓝 point]
      (0 : SpatialPlane → ComplexEuclidean dimension) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds pointIn] with source sourceIn
    apply weightedFiniteKernelField_zero_inner
    simpa only [Metric.mem_ball, dist_zero_right] using (Metric.mem_ball.mp sourceIn).le
  have derivative := (agreement.iteratedFDeriv (𝕜 := ℝ) order).eq_of_nhds
  simpa only [iteratedFDeriv_zero, Pi.zero_apply] using derivative

theorem disk_integral_le_collar (function : SpatialPlane → ℝ) (continuousFunction : Continuous function)
    (nonnegative : ∀ point, 0 ≤ function point)
    (vanishes : ∀ point, ‖point‖ ≤ (3 / 4 : ℝ) → function point = 0) :
    (∫ point in closedUnitDisk, function point) ≤
      collarIntegral (fun point => function (collarPlane point)) := by
  let polarIntegrand : ℝ × ℝ → ℝ := fun point =>
    point.1 * function (spatialPlaneOfPair (polarCoord.symm point))
  have polarContinuous : Continuous polarIntegrand :=
    continuous_fst.mul (continuousFunction.comp
      (continuous_spatialPlaneOfPair.comp continuous_polarCoord_symm))
  have plainContinuous : Continuous (fun point : ℝ × ℝ =>
      function (spatialPlaneOfPair (polarCoord.symm point))) :=
    continuousFunction.comp (continuous_spatialPlaneOfPair.comp continuous_polarCoord_symm)
  have collarContinuous : Continuous (fun point : ℝ × ℝ => function (collarPlane point)) :=
    continuousFunction.comp collarPlane_smooth.continuous
  have pointwise (angle : ℝ) :
      (∫ radius in (0 : ℝ)..1, polarIntegrand (radius, angle)) ≤
        ∫ time in (0 : ℝ)..(1 / 4 : ℝ), function (collarPlane (time, angle)) := by
    have polarSlice : Continuous (fun radius : ℝ => polarIntegrand (radius, angle)) := polarContinuous.comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => angle)))
    have plainSlice : Continuous (fun radius : ℝ => function (spatialPlaneOfPair (polarCoord.symm (radius, angle)))) := plainContinuous.comp
      (continuous_id.prodMk (continuous_const : Continuous (fun _ : ℝ => angle)))
    have zeroIntegral : (∫ radius in (0 : ℝ)..(3 / 4 : ℝ), polarIntegrand (radius, angle)) = 0 := by
      rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 3 / 4)]
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with radius radiusIn
      have radiusBounds : 0 ≤ radius ∧ radius ≤ (3 / 4 : ℝ) := ⟨radiusIn.1.le, radiusIn.2⟩
      change radius * function (spatialPlaneOfPair (polarCoord.symm (radius, angle))) = 0
      rw [vanishes _ ?_, mul_zero]
      have representation : spatialPlaneOfPair (polarCoord.symm (radius, angle)) = collarPlane (1 - radius, angle) := by
        rw [collarPlane_eq_polar, sub_sub_cancel]
      rw [representation, collarPlane_norm, sub_sub_cancel, abs_of_nonneg radiusBounds.1]
      exact radiusBounds.2
    rw [← intervalIntegral.integral_add_adjacent_intervals (polarSlice.intervalIntegrable 0 (3 / 4))
      (polarSlice.intervalIntegrable (3 / 4) 1), zeroIntegral, zero_add]
    have comparison := intervalIntegral.integral_mono_on (μ := volume) (by norm_num : (3 / 4 : ℝ) ≤ 1)
      (polarSlice.intervalIntegrable _ _) (plainSlice.intervalIntegrable _ _)
      (fun radius radiusIn => mul_le_of_le_one_left (nonnegative _) radiusIn.2)
    apply comparison.trans_eq
    have substitution := intervalIntegral.integral_comp_sub_left
      (fun radius => function (spatialPlaneOfPair (polarCoord.symm (radius, angle))))
      (a := (0 : ℝ)) (b := (1 / 4 : ℝ)) 1
    simpa only [sub_zero, show (1 : ℝ) - 1 / 4 = 3 / 4 by norm_num,
      ← collarPlane_eq_polar] using substitution.symm
  rw [closedUnitDisk_polar_integral function continuousFunction]
  unfold collarIntegral
  apply integral_mono
  · exact ((timeIntegral_continuous polarIntegrand polarContinuous 0 1 (by norm_num)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · exact ((timeIntegral_continuous _ collarContinuous 0 (1 / 4) (by norm_num)).continuousOn.integrableOn_compact
      isCompact_Icc).mono_set Ioo_subset_Icc_self
  · exact pointwise

end Grad.BoundaryLift
