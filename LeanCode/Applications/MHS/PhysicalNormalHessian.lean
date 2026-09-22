import PhysicalHessianCovariance
import NormalHessianCovariance
import NormalHessianSeedBridge
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases

noncomputable section

open Set Filter

namespace Grad.MainAssembly.PhysicalNormalHessian

open Grad.MainTarget
open Grad.MainAssembly.CircleIsometryClassification
open Grad.MainAssembly.NormalHessianCovariance
open Grad.MainAssembly.PhysicalHessianCovariance
open Grad.GeometryClosure
open Matrix

variable {E F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem second_comp_at_critical
    (pressure : F → ℝ) (chart : E → F) (point : E)
    (pressureSmooth : ContDiffAt ℝ 2 pressure (chart point))
    (chartSmooth : ContDiffAt ℝ 2 chart point)
    (critical : fderiv ℝ pressure (chart point) = 0) :
    iteratedFDeriv ℝ 2 (pressure ∘ chart) point =
      (iteratedFDeriv ℝ 2 pressure (chart point)).compContinuousLinearMap
        (fun _ => fderiv ℝ chart point) := by
  let outerDerivative := fun argument : E => fderiv ℝ pressure (chart argument)
  let innerDerivative := fun argument : E => fderiv ℝ chart argument
  have pressureDifferentiable : DifferentiableAt ℝ pressure (chart point) :=
    pressureSmooth.differentiableAt (by norm_num)
  have chartDifferentiable : DifferentiableAt ℝ chart point :=
    chartSmooth.differentiableAt (by norm_num)
  have outerDerivativeDifferentiable :
      DifferentiableAt ℝ outerDerivative point := by
    exact ((pressureSmooth.fderiv_right (m := 1) (by norm_num)).comp point
      (chartSmooth.of_le (by norm_num))).differentiableAt (by norm_num)
  have innerDerivativeDifferentiable :
      DifferentiableAt ℝ innerDerivative point := by
    exact (chartSmooth.fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  have firstDerivativeEventual :
      fderiv ℝ (pressure ∘ chart) =ᶠ[nhds point]
        (fun argument => (outerDerivative argument).comp
          (innerDerivative argument)) := by
    filter_upwards
      [chartSmooth.eventually (by norm_num),
        chartSmooth.continuousAt.eventually
          (pressureSmooth.eventually (by norm_num))]
      with argument chartAt pressureAt
    exact fderiv_comp argument
      (pressureAt.differentiableAt (by norm_num))
      (chartAt.differentiableAt (by norm_num))
  have secondDerivativeEquality :
      fderiv ℝ (fderiv ℝ (pressure ∘ chart)) point =
        fderiv ℝ (fun argument => (outerDerivative argument).comp
          (innerDerivative argument)) point :=
    firstDerivativeEventual.fderiv_eq
  rw [fderiv_clm_comp outerDerivativeDifferentiable
    innerDerivativeDifferentiable] at secondDerivativeEquality
  have outerDerivativeFormula :
      fderiv ℝ outerDerivative point =
        (fderiv ℝ (fderiv ℝ pressure) (chart point)).comp
          (fderiv ℝ chart point) := by
    exact fderiv_comp point
      (pressureSmooth.fderiv_right (m := 1) (by norm_num) |>.differentiableAt
        (by norm_num)) chartDifferentiable
  ext directions
  rw [iteratedFDeriv_two_apply]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have evaluated := congrArg
    (fun derivative : E →L[ℝ] E →L[ℝ] ℝ =>
      derivative (directions 0) (directions 1)) secondDerivativeEquality
  rw [outerDerivativeFormula] at evaluated
  simpa [outerDerivative, innerDerivative, critical,
    iteratedFDeriv_two_apply] using evaluated

def coordinateDirection (disk : Fin 2 → ℝ) (toroidal : ℝ) : Vec :=
  vector (disk 0) (disk 1) toroidal

def physicalNormalVector (angle : ℝ) (normal : Fin 2 → ℝ) : Vec :=
  normal 0 • axisRadial angle + normal 1 • axisVertical

def coordinateNormalPreimage (radius a : ℝ)
    (matrix : Matrix (Fin 2) (Fin 2) ℝ) (tilt normal : Fin 2 → ℝ) : Vec :=
  let disk := a⁻¹ • (matrix⁻¹ *ᵥ normal)
  coordinateDirection disk (-(tilt ⬝ᵥ disk) / radius)

def HasAxisDerivative (chart : Vec → Vec) (coordinatePoint : Vec)
    (radius angle a : ℝ) (matrix : Matrix (Fin 2) (Fin 2) ℝ)
    (tilt : Fin 2 → ℝ) : Prop :=
  ∀ (disk : Fin 2 → ℝ) (toroidal : ℝ),
    fderiv ℝ chart coordinatePoint (coordinateDirection disk toroidal) =
      (a * (matrix *ᵥ disk) 0) • axisRadial angle +
      (a * (matrix *ᵥ disk) 1) • axisVertical +
      (tilt ⬝ᵥ disk + radius * toroidal) • axisTangent angle

theorem physical_normal_vector_preimage
    (chart : Vec → Vec) (coordinatePoint : Vec)
    (radius angle a : ℝ) (matrix : Matrix (Fin 2) (Fin 2) ℝ)
    (tilt normal : Fin 2 → ℝ)
    (radiusNonzero : radius ≠ 0) (aNonzero : a ≠ 0)
    (matrixInvertible : IsUnit matrix.det)
    (axisDerivative : HasAxisDerivative chart coordinatePoint radius angle a matrix tilt) :
    fderiv ℝ chart coordinatePoint
        (coordinateNormalPreimage radius a matrix tilt normal) =
      physicalNormalVector angle normal := by
  let disk := a⁻¹ • (matrix⁻¹ *ᵥ normal)
  have diskIdentity : matrix *ᵥ disk = a⁻¹ • normal := by
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv matrix matrixInvertible, Matrix.one_mulVec]
  rw [coordinateNormalPreimage]
  change fderiv ℝ chart coordinatePoint
      (coordinateDirection disk (-(tilt ⬝ᵥ disk) / radius)) = _
  rw [axisDerivative, diskIdentity]
  simp only [Pi.smul_apply, smul_eq_mul]
  have firstIdentity : a * (a⁻¹ * normal 0) = normal 0 := by
    field_simp
  have secondIdentity : a * (a⁻¹ * normal 1) = normal 1 := by
    field_simp
  have tangentIdentity :
      tilt ⬝ᵥ disk + radius * (-(tilt ⬝ᵥ disk) / radius) = 0 := by
    field_simp
    ring
  rw [firstIdentity, secondIdentity, tangentIdentity, zero_smul, add_zero]
  rfl

def coordinatePressure (potential : ℝ) (point : Vec) : ℝ :=
  potential - (point 0) ^ 2 - (point 1) ^ 2

def coordinateCLM (coordinate : Fin 3) : Vec →L[ℝ] ℝ :=
  PiLp.proj 2 (fun _ : Fin 3 => ℝ) coordinate

@[simp] theorem coordinateCLM_apply (coordinate : Fin 3) (point : Vec) :
    coordinateCLM coordinate point = point coordinate := rfl

theorem coordinatePressure_fderiv (potential : ℝ) (point : Vec) :
    fderiv ℝ (coordinatePressure potential) point =
      (-2 * point 0) • coordinateCLM 0 +
        (-2 * point 1) • coordinateCLM 1 := by
  have firstCoordinate :
      HasFDerivAt (fun argument : Vec => argument 0) (coordinateCLM 0) point :=
    (coordinateCLM 0).hasFDerivAt
  have secondCoordinate :
      HasFDerivAt (fun argument : Vec => argument 1) (coordinateCLM 1) point :=
    (coordinateCLM 1).hasFDerivAt
  have derivative := ((hasFDerivAt_const (x := point) (c := potential)).sub
    (firstCoordinate.mul firstCoordinate)).sub
      (secondCoordinate.mul secondCoordinate)
  unfold coordinatePressure
  simp only [pow_two]
  change fderiv ℝ
    (((fun _ : Vec => potential) -
      (fun argument : Vec => argument 0) * (fun argument : Vec => argument 0)) -
      (fun argument : Vec => argument 1) * (fun argument : Vec => argument 1))
      point = _
  rw [derivative.fderiv]
  ext direction
  simp [coordinateCLM_apply]
  ring

theorem coordinatePressure_secondDerivative
    (potential : ℝ) (point : Vec) (directions : Fin 2 → Vec) :
    iteratedFDeriv ℝ 2 (coordinatePressure potential) point directions =
      -2 * (directions 0 0 * directions 1 0 +
        directions 0 1 * directions 1 1) := by
  rw [iteratedFDeriv_two_apply]
  rw [show fderiv ℝ (coordinatePressure potential) = fun argument =>
      (-2 * argument 0) • coordinateCLM 0 +
        (-2 * argument 1) • coordinateCLM 1 from
    funext (coordinatePressure_fderiv potential)]
  have firstCoordinate : HasFDerivAt (coordinateCLM 0) (coordinateCLM 0) point :=
    (coordinateCLM 0).hasFDerivAt
  have secondCoordinate : HasFDerivAt (coordinateCLM 1) (coordinateCLM 1) point :=
    (coordinateCLM 1).hasFDerivAt
  have firstScalar :
      HasFDerivAt (fun argument : Vec => -2 * coordinateCLM 0 argument)
        ((-2 : ℝ) • coordinateCLM 0) point :=
    firstCoordinate.const_mul (-2 : ℝ)
  have secondScalar :
      HasFDerivAt (fun argument : Vec => -2 * coordinateCLM 1 argument)
        ((-2 : ℝ) • coordinateCLM 1) point :=
    secondCoordinate.const_mul (-2 : ℝ)
  have derivative := (firstScalar.smul_const (coordinateCLM 0)).add
    (secondScalar.smul_const (coordinateCLM 1))
  change (fderiv ℝ
    ((fun argument : Vec => (-2 * coordinateCLM 0 argument) • coordinateCLM 0) +
      fun argument : Vec => (-2 * coordinateCLM 1 argument) • coordinateCLM 1) point
        (directions 0)) (directions 1) = _
  rw [derivative.fderiv]
  simp [ContinuousLinearMap.smulRight_apply, coordinateCLM_apply]
  ring

def planeBasis (index : Fin 2) : Fin 2 → ℝ :=
  Pi.single index 1

theorem physicalNormalVector_planeBasis (angle : ℝ) (index : Fin 2) :
    physicalNormalVector angle (planeBasis index) = normalFrame angle index := by
  fin_cases index <;>
    simp [physicalNormalVector, planeBasis, normalFrame]

theorem physical_normal_hessian_formula
    (pressure : Vec → ℝ) (chart : Vec → Vec) (coordinatePoint : Vec)
    (potential radius angle a : ℝ)
    (matrix : Matrix (Fin 2) (Fin 2) ℝ) (tilt : Fin 2 → ℝ)
    (radiusNonzero : radius ≠ 0) (aNonzero : a ≠ 0)
    (matrixInvertible : IsUnit matrix.det)
    (chartPoint : chart coordinatePoint = radius • axisRadial angle)
    (pressureSmooth : ContDiffAt ℝ 2 pressure (chart coordinatePoint))
    (chartSmooth : ContDiffAt ℝ 2 chart coordinatePoint)
    (critical : fderiv ℝ pressure (chart coordinatePoint) = 0)
    (pullback : (pressure ∘ chart) =ᶠ[nhds coordinatePoint]
      coordinatePressure potential)
    (axisDerivative : HasAxisDerivative chart coordinatePoint radius angle a matrix tilt) :
    normalHessianMatrix pressure radius angle =
      algebraicNormalHessian a matrix := by
  have chainRule := second_comp_at_critical pressure chart coordinatePoint
    pressureSmooth chartSmooth critical
  have pullbackSecond :
      iteratedFDeriv ℝ 2 (pressure ∘ chart) coordinatePoint =
        iteratedFDeriv ℝ 2 (coordinatePressure potential) coordinatePoint :=
    (pullback.iteratedFDeriv ℝ 2).eq_of_nhds
  funext row column
  let rowPreimage := coordinateNormalPreimage radius a matrix tilt (planeBasis row)
  let columnPreimage := coordinateNormalPreimage radius a matrix tilt (planeBasis column)
  have rowMaps :
      fderiv ℝ chart coordinatePoint rowPreimage = normalFrame angle row := by
    rw [physical_normal_vector_preimage chart coordinatePoint radius angle a matrix
      tilt (planeBasis row) radiusNonzero aNonzero matrixInvertible axisDerivative,
      physicalNormalVector_planeBasis]
  have columnMaps :
      fderiv ℝ chart coordinatePoint columnPreimage = normalFrame angle column := by
    rw [physical_normal_vector_preimage chart coordinatePoint radius angle a matrix
      tilt (planeBasis column) radiusNonzero aNonzero matrixInvertible axisDerivative,
      physicalNormalVector_planeBasis]
  have evaluated := congrArg
    (fun tensor : Vec [×2]→L[ℝ] ℝ =>
      tensor ![rowPreimage, columnPreimage]) chainRule
  rw [pullbackSecond] at evaluated
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply] at evaluated
  have mappedPair :
      (fun index => fderiv ℝ chart coordinatePoint
        (![rowPreimage, columnPreimage] index)) =
      ![fderiv ℝ chart coordinatePoint rowPreimage,
        fderiv ℝ chart coordinatePoint columnPreimage] := by
    funext index
    fin_cases index <;> rfl
  rw [mappedPair] at evaluated
  rw [rowMaps, columnMaps] at evaluated
  rw [coordinatePressure_secondDerivative] at evaluated
  rw [normalHessianMatrix, pressureHessian, ← chartPoint]
  change iteratedFDeriv ℝ 2 pressure (chart coordinatePoint)
      ![normalFrame angle row, normalFrame angle column] = _
  rw [← evaluated]
  dsimp only [rowPreimage, columnPreimage]
  fin_cases row <;> fin_cases column <;>
    simp [coordinateNormalPreimage, coordinateDirection, planeBasis,
      algebraicNormalHessian, Matrix.mul_apply,
      Fin.sum_univ_two, vector, smul_eq_mul] <;>
    field_simp

end Grad.MainAssembly.PhysicalNormalHessian
