import SCD1WeightedRay
import RadialSmoothIntegral

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial

/-- This averages an already weighted jet. No phase factor is moved from
the endpoint to the integration point. -/
def rayAverageValue {dimension : ℕ} (field : ClosedJet dimension)
    (point : SpatialPlane) : ComplexEuclidean dimension :=
  ∫ scale in Icc (0 : ℝ) 1, smoothClosedExtension field (scale • point)

theorem rayAverageValue_smooth {dimension : ℕ} (field : ClosedJet dimension) :
    ContDiff ℝ ∞ (rayAverageValue field) := by
  unfold rayAverageValue
  simpa only [one_smul] using weightedIntegral_contDiff
    (field := fun argument : SpatialPlane × ℝ => smoothClosedExtension field (argument.2 • argument.1))
    ((smoothClosedExtension_smooth field).comp (contDiff_snd.smul contDiff_fst))
    (fun _ => 1) continuous_const 0 1

def rayAverageJet {dimension : ℕ} (field : ClosedJet dimension) : ClosedJet dimension :=
  globalClosedJet (rayAverageValue field) (rayAverageValue_smooth field)

theorem rayAverage_derivative {dimension order : ℕ} (field : ClosedJet dimension)
    (word : CartesianWord order) (point : ClosedDisk) :
    closedDerivative (rayAverageJet field) order word point =
      ∫ scale in (0 : ℝ)..1, scale ^ order •
        cartesianDerivative order word (smoothClosedExtension field) (scale • point.val) := by
  rw [rayAverageJet, globalClosedJet_derivative]
  have integralDerivative := cartesianDerivative_weightedIntegral order word
    (field := fun argument : SpatialPlane × ℝ => smoothClosedExtension field (argument.2 • argument.1))
    ((smoothClosedExtension_smooth field).comp (contDiff_snd.smul contDiff_fst))
    (fun _ => 1) continuous_const 0 1 point.val
  simp only [one_smul] at integralDerivative
  rw [show cartesianDerivative order word (rayAverageValue field) point.val = _ from integralDerivative]
  simp_rw [cartesianDerivative_dilation _ _ (smoothClosedExtension_smooth field)]
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le zero_le_one]

theorem rayAverage_derivative_bound {dimension order : ℕ} (field : ClosedJet dimension)
    (word : CartesianWord order) (point : ClosedDisk) :
    ‖closedDerivative (rayAverageJet field) order word point‖ ≤ ‖closedDerivative field order word‖ := by
  rw [rayAverage_derivative]
  have bounded : ∀ scale ∈ Icc (0 : ℝ) 1,
      ‖scale ^ order • cartesianDerivative order word (smoothClosedExtension field)
        (scale • point.val)‖ ≤ ‖closedDerivative field order word‖ := by
    intro scale inside
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg inside.1 _)]
    have value := smoothClosedExtension_derivative field word (dilationPoint scale inside.1 inside.2 point)
    change cartesianDerivative order word (smoothClosedExtension field) (scale • point.val) = _ at value
    rw [value]
    exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ inside.1 inside.2)).trans
      (ContinuousMap.norm_coe_le_norm _ _)
  have integralBound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1)
    (f := fun scale => scale ^ order • cartesianDerivative order word
      (smoothClosedExtension field) (scale • point.val))
    (fun scale inside => by
      have member : scale ∈ Ioc (0 : ℝ) 1 := by
        simpa only [uIoc_of_le zero_le_one] using inside
      exact bounded scale ⟨member.1.le, member.2⟩)
  simpa only [sub_zero, abs_one, mul_one] using integralBound

theorem rayAverage_derivative_M4 {dimension order : ℕ} (field : ClosedJet dimension)
    (word : CartesianWord order) (point : ClosedDisk) :
    ‖closedDerivative (rayAverageJet field) order word point‖ ≤
      diskSupConstant * Real.sqrt (diskSupEnergy (shiftedClosedJet field word)) := by
  apply (rayAverage_derivative_bound field word point).trans
  apply (ContinuousMap.norm_le _ (mul_nonneg diskSupConstant_pos.le (Real.sqrt_nonneg _))).mpr
  intro value
  exact diskSup_bound (shiftedClosedJet field word) value

end Grad.SourceCollarDivision
