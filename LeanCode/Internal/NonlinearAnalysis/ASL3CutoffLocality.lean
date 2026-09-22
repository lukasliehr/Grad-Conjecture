import ASL2CoefficientEvaluation
import AXL23AxisDataLift
import Mathlib.Analysis.Calculus.LocalExtr.Basic

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

open scoped ContDiff Topology
open Filter

namespace Grad.AxisSourceLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.AxisSplit Grad.ChartAxisLift

theorem radialCap_fderiv_zero (radius : ℝ) (positive : 0 < radius)
    (point : SpatialPlane) (outside : radius / 2 ≤ ‖point‖) :
    fderiv ℝ (radialCap radius positive) point = 0 := by
  apply IsLocalMin.fderiv_eq_zero
  apply Filter.Eventually.of_forall
  intro other
  rw [radialCap_zero radius positive point outside]
  exact (radialCapBase radius positive).nonneg

/-- Multiplication by the actual radial cutoff kills the first jet on the
whole exterior, including both the cap circle and the closed-disk boundary. -/
theorem cutoffJet_partial_zero {dimension : ℕ} (radius : ℝ) (positive : 0 < radius)
    (field source : ClosedJet dimension)
    (factor : ∀ point : ClosedDisk, field.value point =
      (radialCap radius positive point.val : ℂ) • source.value point)
    (direction : Fin 2) (point : ClosedDisk) (outside : radius / 2 ≤ ‖point.val‖) :
    partialCoefficient direction field point = 0 := by
  let mapping : SpatialPlane → ComplexEuclidean dimension :=
    fun argument => radialCap radius positive argument • smoothClosedExtension source argument
  have smooth : ContDiff ℝ ∞ mapping :=
    (radialCap_smooth radius positive).smul (smoothClosedExtension_smooth source)
  have represented : field = globalClosedJet mapping smooth := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro argument
    rw [globalClosedJet_value]
    dsimp only [mapping]
    rw [smoothClosedExtension_value, ← Complex.coe_smul]
    exact factor argument
  have differential : fderiv ℝ mapping point.val = 0 := by
    dsimp only [mapping]
    rw [fderiv_fun_smul
      (((radialCap_smooth radius positive).differentiable (by simp)).differentiableAt)
      (((smoothClosedExtension_smooth source).differentiable (by simp)).differentiableAt),
      radialCap_zero radius positive point.val outside,
      radialCap_fderiv_zero radius positive point.val outside]
    simp
  change (partialJet direction field).value point = 0
  rw [represented, partialJet_global_value, differential]
  rfl

theorem capAffineField_partial_zero {parameters : PhaseParameters}
    (radius : ℝ) (positive : 0 < radius) (seed : Seed.Parameters)
    (inside : seed ∈ Seed.parameterDomain) (coefficient : TameCoefficient parameters)
    (tangent : TangentCoefficient parameters) (cell : ℤ) (direction : Fin 2)
    (point : ClosedDisk) (outside : radius / 2 ≤ ‖point.val‖) :
    partialCoefficient direction
      ((capAffineField parameters radius positive seed inside coefficient tangent).val cell) point = 0 :=
  cutoffJet_partial_zero radius positive _ _
    (capAffineField_value_factor radius positive seed inside coefficient tangent cell)
    direction point outside

theorem capScalarAffine_partial_zero {parameters : PhaseParameters}
    (radius : ℝ) (positive : 0 < radius) (sigma : TangentCoefficient parameters)
    (cell : ℤ) (direction : Fin 2) (point : ClosedDisk)
    (outside : radius / 2 ≤ ‖point.val‖) :
    partialCoefficient direction ((capScalarAffine parameters radius positive sigma).val cell) point = 0 :=
  cutoffJet_partial_zero radius positive _ _
    (capScalarAffine_value_factor radius positive sigma cell) direction point outside

end Grad.AxisSourceLift
