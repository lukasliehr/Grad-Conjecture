import AXL15OuterRow

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit Grad.BoundaryTrace
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.PhysicalCoordinates Grad.ChartAxisSplit Grad.Cor18

variable {parameters : PhaseParameters}

theorem boundaryCirclePoint_squares (angle : CellCircle) :
    (boundaryCirclePoint angle 0 : ℂ)^2 + (boundaryCirclePoint angle 1 : ℂ)^2 = 1 := by
  have squared := congrArg (fun value : ℝ => value ^ 2) (boundaryCirclePoint_norm angle)
  rw [PiLp.norm_eq_of_L2, Fin.sum_univ_two,
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))] at squared
  simp only [Real.norm_eq_abs, sq_abs, one_pow] at squared
  exact_mod_cast squared

theorem rowFunction_storedCapRemainder (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) (cell : ℤ) :
    rowFunction parameters
      (rowField parameters seed inside (storedCapChartRemainder parameters radius positive seed inside coefficient tangent))
      cell = fun _ => -(coefficient.val cell) := by
  funext angle
  unfold rowFunction
  rw [rowField_storedCapRemainder_boundary radius positive bounded seed inside coefficient tangent]
  simp only [PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul, complexDiskPoint,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  change (boundaryCirclePoint angle 0 : ℂ) * (-(coefficient.val cell * (boundaryCirclePoint angle 0 : ℂ))) +
    (boundaryCirclePoint angle 1 : ℂ) * (-(coefficient.val cell * (boundaryCirclePoint angle 1 : ℂ))) = _
  calc
    _ = -(coefficient.val cell) * ((boundaryCirclePoint angle 0 : ℂ)^2 + (boundaryCirclePoint angle 1 : ℂ)^2) := by ring
    _ = _ := by rw [boundaryCirclePoint_squares, mul_one]

theorem fourierCoeff_constant_nonzero (value : ℂ) (mode : ℤ) (nonzero : mode ≠ 0) :
    fourierCoeff (fun _ : CellCircle => value) mode = 0 := by
  have identity : (fun _ : CellCircle => value) = fun angle => value * fourier 0 angle := by
    funext angle
    simp
  rw [identity, fourierCoeff_const_mul]
  have coefficient := congrFun (fourierCoeff_fourier (T := 2 * Real.pi) 0) mode
  rw [coefficient]
  simp [nonzero]

/-- Literal AL18: only the angular zero mode survives before the original
high-mode projection. No outer constraint is assumed. -/
theorem storedCapChartRemainder_outer (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) :
    physicalRow parameters seed inside
      (storedCapChartRemainder parameters radius positive seed inside coefficient tangent) = 0 := by
  apply Subtype.ext
  funext mode
  change (if |mode.1| ≤ 2 then 0 else EuclideanSpace.single 0
    (fourierCoeff (rowFunction parameters
      (rowField parameters seed inside (storedCapChartRemainder parameters radius positive seed inside coefficient tangent))
      mode.2) mode.1)) = 0
  by_cases low : |mode.1| ≤ 2
  · rw [if_pos low]
  · rw [if_neg low, rowFunction_storedCapRemainder radius positive bounded seed inside coefficient tangent,
      fourierCoeff_constant_nonzero _ mode.1 (by intro zero; simp [zero] at low)]
    simp

theorem storedCapChartRemainder_vectorConstraints (radius : ℝ) (positive : 0 < radius) (bounded : radius ≤ 1)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain)
    (coefficient : TameCoefficient parameters) (tangent : TangentCoefficient parameters) :
    VectorConstraints parameters seed inside
      (storedCapChartRemainder parameters radius positive seed inside coefficient tangent) :=
  ⟨storedCapChartRemainder_zeroJets radius positive seed inside coefficient tangent,
    storedCapChartRemainder_poloidal radius positive seed inside coefficient tangent,
    storedCapChartRemainder_toroidal radius positive seed inside coefficient tangent,
    storedCapChartRemainder_outer radius positive bounded seed inside coefficient tangent⟩

end Grad.ChartAxisLift
