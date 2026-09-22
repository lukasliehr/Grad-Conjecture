import RadialTruncation
import RadialDivision

noncomputable section

open Set MeasureTheory
open scoped ContDiff Interval

namespace Grad.NonlinearRadial

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotient Grad.PhysicalFamily

theorem radialCore_origin {dimension : ℕ} (parameters : PhaseParameters)
    (field : ACore parameters dimension) (cell : ℤ) :
    ((radialCore parameters field).val cell).value ⟨0, by simp [closedUnitDisk]⟩ =
      (1 / 4 : ℝ) • (field.val cell).value ⟨0, by simp [closedUnitDisk]⟩ := by
  rw [radialCore_actual parameters field cell]
  unfold integralCoefficient radialIntegral
  simp only [smul_zero]
  rw [intervalIntegral.integral_smul_const, integral_radialKernel]
  exact congrArg (fun value => (1 / 4 : ℝ) • value)
    (smoothClosedExtension_value (field.val cell) ⟨0, by simp [closedUnitDisk]⟩)

/-- Immediate literal O11 consumer. The input is already an actual ACore
Laplacian coefficient field. No derivative bound, gauge, or solution-family
construction is assumed or credited by this statement. -/
theorem radialCore_laplacian_consumer {dimension : ℕ} (parameters : PhaseParameters)
    (source : ACore parameters dimension) (potential : ℤ → SpatialPlane → ComplexEuclidean dimension)
    (radius : ℝ) (collar : 1 < radius)
    (smooth : ∀ cell, ContDiffOn ℝ ∞ (potential cell) (Metric.ball 0 radius))
    (radial : ∀ cell angle point, point ∈ Metric.ball 0 radius →
      potential cell (planeRotationAction angle point) = potential cell point)
    (origin : ∀ cell, potential cell 0 = 0)
    (sourceLaw : ∀ (cell : ℤ) (point : ClosedDisk),
      (source.val cell).value point = diskLaplacian (potential cell) point.val) :
    (∀ (cell : ℤ) (point : ClosedDisk), potential cell point.val =
      ‖point.val‖ ^ 2 • ((radialCore parameters source).val cell).value point) ∧
    ∀ grade, originalGradeNorm grade (radialCore parameters source) ≤
      dilationGradeConstant grade * originalGradeNorm grade source := by
  refine ⟨?_, fun grade => radialCore_bound parameters grade source⟩
  intro cell point
  have inside : point.val ∈ Metric.ball (0 : SpatialPlane) radius := by
    rw [Metric.mem_ball, dist_zero_right]
    exact point.property.trans_lt collar
  have identity := radialIntegral_laplacian (potential cell) radius (smooth cell) (radial cell) point.val inside
  rw [origin cell, sub_zero] at identity
  rw [identity, radialCore_actual parameters source cell]
  congr 1
  unfold integralCoefficient radialIntegral
  apply intervalIntegral.integral_congr
  intro scale scaleIn
  have unitScale : scale ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using scaleIn
  apply congrArg (fun value : ComplexEuclidean dimension => Real.negMulLog scale • value)
  let contracted := dilationPoint scale unitScale.1 unitScale.2 point
  change diskLaplacian (potential cell) contracted.val = smoothClosedExtension (source.val cell) contracted.val
  rw [smoothClosedExtension_value, sourceLaw]

end Grad.NonlinearRadial
