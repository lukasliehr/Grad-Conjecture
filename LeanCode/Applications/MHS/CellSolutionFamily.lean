import MainStatement
import Grad.GeometryClosure.Seed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

noncomputable section

open Set
open scoped ContDiff Interval

namespace Grad.PhysicalFamily

open Grad.MainTarget
open Grad.GeometryClosure
open Matrix

abbrev CellArgument := ℝ × (ℝ × Vec)
abbrev CircleArgument := ℝ × (ℝ × ℝ)

def planeQuarterTurn (point : Plane) : Plane :=
  WithLp.toLp 2 ![-point 1, point 0]

def planeRotationAction (angle : ℝ) (point : Plane) : Plane :=
  WithLp.toLp 2 (planarRotation angle *ᵥ fun coordinate => point coordinate)

def planeEmbedding (point : Plane) : Vec :=
  vector (point 0) 0 (point 1)

/-- The disk variables in the Euclidean coordinate order `(y₁, ζ, y₂)`. -/
def coordinateDisk (point : Vec) : Plane :=
  WithLp.toLp 2 ![point 0, point 2]

def coordinatePoint (point : Plane) (time : ℝ) : Vec :=
  vector (point 0) time (point 1)

def coordinateCollar (radius : ℝ) : Set Vec :=
  {point | ‖coordinateDisk point‖ < radius}

def tangentGenerator (point : Vec) : Vec :=
  vector (-point 1) (point 0) 0

def tangentDirection : Vec := basisVector 1

def planeDot (first second : Plane) : ℝ :=
  ∑ coordinate : Fin 2, first coordinate * second coordinate

def diskEuler {Target : Type*} [NormedAddCommGroup Target]
    [NormedSpace ℝ Target] (mapping : Plane → ℝ → Target)
    (point : Plane) (time : ℝ) : Target :=
  fderiv ℝ (fun argument => mapping argument time) point point

def diskAngular {Target : Type*} [NormedAddCommGroup Target]
    [NormedSpace ℝ Target] (mapping : Plane → ℝ → Target)
    (point : Plane) (time : ℝ) : Target :=
  fderiv ℝ (fun argument => mapping argument time) point
    (planeQuarterTurn point)

def cellDerivative {Target : Type*} [NormedAddCommGroup Target]
    [NormedSpace ℝ Target] (mapping : Plane → ℝ → Target)
    (point : Plane) (time : ℝ) : Target :=
  fderiv ℝ (mapping point) time 1

def angularAverage (mapping : Plane → ℝ → ℝ)
    (point : Plane) (time : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ *
    ∫ angle in (0 : ℝ)..2 * Real.pi,
      mapping (planeRotationAction angle point) time

def removeAngularAverage (mapping : Plane → ℝ → ℝ)
    (point : Plane) (time : ℝ) : ℝ :=
  mapping point time - angularAverage mapping point time

def tripleDeterminant (first second third : Vec) : ℝ :=
  Matrix.det fun row column => (![first, second, third] column) row

def affineStateDerivative (cellLength epsilon : ℝ)
    (mapping : Plane → ℝ → Vec) (point : Plane) (time : ℝ) : Vec :=
  cellDerivative mapping point time +
    epsilon • tangentGenerator (mapping point time) +
    cellLength • tangentDirection

def firstCellRow (mapping : Plane → ℝ → Vec)
    (potential : Plane → ℝ → ℝ) (point : Plane) (time : ℝ) : ℝ :=
  diskAngular potential point time - ‖diskAngular mapping point time‖ ^ 2 +
    ‖point‖ ^ 2

def secondCellRow (mapping : Plane → ℝ → Vec)
    (potential : Plane → ℝ → ℝ) (point : Plane) (time : ℝ) : ℝ :=
  removeAngularAverage
    (fun argument cellTime =>
      diskEuler potential argument cellTime -
        inner ℝ (diskEuler mapping argument cellTime)
          (diskAngular mapping argument cellTime)) point time

def thirdCellRow (cellLength epsilon : ℝ)
    (mapping : Plane → ℝ → Vec) (potential : Plane → ℝ → ℝ)
    (point : Plane) (time : ℝ) : ℝ :=
  removeAngularAverage
    (fun argument cellTime =>
      inner ℝ (diskAngular mapping argument cellTime)
          (affineStateDerivative cellLength epsilon mapping argument cellTime) -
        cellDerivative potential argument cellTime) point time

def fourthCellRow (cellLength epsilon : ℝ)
    (mapping : Plane → ℝ → Vec) (point : Plane) (time : ℝ) : ℝ :=
  removeAngularAverage
    (fun argument cellTime =>
      tripleDeterminant (diskEuler mapping argument cellTime)
        (diskAngular mapping argument cellTime)
        (affineStateDerivative cellLength epsilon mapping argument cellTime))
    point time

def cellC2Seminorm {Target : Type*} [NormedAddCommGroup Target]
    [NormedSpace ℝ Target] (mapping : Plane → ℝ → Target) : ℝ :=
  sSup {value : ℝ |
    ∃ (order : Fin 3) (point : Plane) (time : ℝ),
      ‖point‖ ≤ 1 ∧ time ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
      value = ‖iteratedFDeriv ℝ order.val
        (fun argument : Vec => mapping (coordinateDisk argument) (argument 1))
        (coordinatePoint point time)‖}

def circleC2Seminorm {Target : Type*} [NormedAddCommGroup Target]
    [NormedSpace ℝ Target] (mapping : ℝ → Target) : ℝ :=
  sSup {value : ℝ |
    ∃ (order : Fin 3) (time : ℝ),
      time ∈ Set.Icc (0 : ℝ) (2 * Real.pi) ∧
      value = ‖iteratedFDeriv ℝ order.val mapping time‖}

def normalizedFactor (tilt : Plane) : ℝ :=
  Real.sqrt (1 - ‖tilt‖ ^ 2 / 2)

def seedAction (rho alpha delta parameter time : ℝ)
    (point : Plane) : Plane :=
  WithLp.toLp 2
    (harmonicSeedMatrix rho alpha delta parameter time *ᵥ
      fun coordinate => point coordinate)

def uncurriedCell {Target : Type*}
    (mapping : ℝ → ℝ → Plane → ℝ → Target) : CellArgument → Target :=
  fun argument => mapping argument.1 argument.2.1
    (coordinateDisk argument.2.2) (argument.2.2 1)

def uncurriedCircle {Target : Type*}
    (mapping : ℝ → ℝ → ℝ → Target) : CircleArgument → Target :=
  fun argument => mapping argument.1 argument.2.1 argument.2.2

/-- Exact D03 downstream contract.  It stores the actual functions before
their laws and deliberately contains no existence, inverse, embedding,
stabilizer, or moduli field. -/
structure CellSolutionFamily (cellLength : ℝ) where
  rho : ℝ
  delta : ℝ
  alpha : ℝ
  lower : ℝ
  upper : ℝ
  parameterLower : ℝ
  parameterUpper : ℝ
  epsilonZero : ℝ
  collarRadius : ℝ
  bound : ℝ
  v : ℝ → ℝ → Plane → ℝ → Vec
  w : ℝ → ℝ → Plane → ℝ → ℝ
  remainder : ℝ → ℝ → Plane → ℝ → Vec
  tilt : ℝ → ℝ → ℝ → Plane
  rhoPositive : 0 < rho
  rhoSmall : rho < 1 / 4
  deltaNonzero : delta ≠ 0
  alphaNonresonant : ∀ multiple : ℤ,
    alpha ≠ (Real.pi / 2) * (multiple : ℝ)
  lowerPositive : 0 < lower
  intervalNontrivial : lower < upper
  upperSmall : upper < 1 / 2
  parameterContains : parameterLower < lower ∧ upper < parameterUpper
  epsilonPositive : 0 < epsilonZero
  collarLarge : 1 < collarRadius
  boundAtLeastOne : 1 ≤ bound
  vSmooth : ContDiffOn ℝ ∞ (uncurriedCell v)
    (Set.Ioo (-epsilonZero) epsilonZero ×ˢ
      (Set.Ioo parameterLower parameterUpper ×ˢ
        coordinateCollar collarRadius))
  wSmooth : ContDiffOn ℝ ∞ (uncurriedCell w)
    (Set.Ioo (-epsilonZero) epsilonZero ×ˢ
      (Set.Ioo parameterLower parameterUpper ×ˢ
        coordinateCollar collarRadius))
  remainderSmooth : ContDiffOn ℝ ∞ (uncurriedCell remainder)
    (Set.Ioo (-epsilonZero) epsilonZero ×ˢ
      (Set.Ioo parameterLower parameterUpper ×ˢ
        coordinateCollar collarRadius))
  tiltSmooth : ContDiffOn ℝ ∞ (uncurriedCircle tilt)
    (Set.Ioo (-epsilonZero) epsilonZero ×ˢ
      (Set.Ioo parameterLower parameterUpper ×ˢ Set.univ))
  vPeriodic : ∀ epsilon ∈ Set.Ioo (-epsilonZero) epsilonZero,
    ∀ parameter ∈ Set.Ioo parameterLower parameterUpper,
      ∀ point ∈ Metric.ball (0 : Plane) collarRadius, ∀ time,
        v epsilon parameter point (time + 2 * Real.pi) =
          v epsilon parameter point time
  wPeriodic : ∀ epsilon ∈ Set.Ioo (-epsilonZero) epsilonZero,
    ∀ parameter ∈ Set.Ioo parameterLower parameterUpper,
      ∀ point ∈ Metric.ball (0 : Plane) collarRadius, ∀ time,
        w epsilon parameter point (time + 2 * Real.pi) =
          w epsilon parameter point time
  remainderPeriodic : ∀ epsilon ∈ Set.Ioo (-epsilonZero) epsilonZero,
    ∀ parameter ∈ Set.Ioo parameterLower parameterUpper,
      ∀ point ∈ Metric.ball (0 : Plane) collarRadius, ∀ time,
        remainder epsilon parameter point (time + 2 * Real.pi) =
          remainder epsilon parameter point time
  tiltPeriodic : ∀ epsilon ∈ Set.Ioo (-epsilonZero) epsilonZero,
    ∀ parameter ∈ Set.Ioo parameterLower parameterUpper, ∀ time,
      tilt epsilon parameter (time + 2 * Real.pi) =
        tilt epsilon parameter time
  tiltBound : ∀ epsilon ∈ Set.Ioo (-epsilonZero) epsilonZero,
    ∀ parameter ∈ Set.Icc lower upper, ∀ time,
      ‖tilt epsilon parameter time‖ ^ 2 < 2
  normalizedChart : ∀ epsilon ∈ Set.Ioo (-epsilonZero) epsilonZero,
    ∀ parameter ∈ Set.Icc lower upper,
      ∀ point, ‖point‖ ≤ 1 → ∀ time,
        v epsilon parameter point time =
          normalizedFactor (tilt epsilon parameter time) •
              planeEmbedding (seedAction rho alpha delta parameter time point) +
            planeDot (tilt epsilon parameter time) point • tangentDirection +
          remainder epsilon parameter point time
  remainderValueZero : ∀ epsilon ∈ Set.Ioo (-epsilonZero) epsilonZero,
    ∀ parameter ∈ Set.Icc lower upper, ∀ time,
      remainder epsilon parameter 0 time = 0
  remainderDerivativeZero : ∀ epsilon ∈ Set.Ioo (-epsilonZero) epsilonZero,
    ∀ parameter ∈ Set.Icc lower upper, ∀ time,
      fderiv ℝ (fun point => remainder epsilon parameter point time) 0 = 0
  firstRowZero : ∀ epsilon ∈ Set.Ioo (-epsilonZero) epsilonZero,
    ∀ parameter ∈ Set.Icc lower upper,
      ∀ point, ‖point‖ ≤ 1 → ∀ time,
        firstCellRow (v epsilon parameter) (w epsilon parameter) point time = 0
  secondRowZero : ∀ epsilon ∈ Set.Ioo (-epsilonZero) epsilonZero,
    ∀ parameter ∈ Set.Icc lower upper,
      ∀ point, ‖point‖ ≤ 1 → ∀ time,
        secondCellRow (v epsilon parameter) (w epsilon parameter) point time = 0
  thirdRowZero : ∀ epsilon ∈ Set.Ioo (-epsilonZero) epsilonZero,
    ∀ parameter ∈ Set.Icc lower upper,
      ∀ point, ‖point‖ ≤ 1 → ∀ time,
        thirdCellRow cellLength epsilon (v epsilon parameter)
          (w epsilon parameter) point time = 0
  fourthRowZero : ∀ epsilon ∈ Set.Ioo (-epsilonZero) epsilonZero,
    ∀ parameter ∈ Set.Icc lower upper,
      ∀ point, ‖point‖ ≤ 1 → ∀ time,
        fourthCellRow cellLength epsilon (v epsilon parameter) point time = 0
  physicalC2Estimate : ∀ epsilon ∈ Set.Ioo (-epsilonZero) epsilonZero,
    ∀ parameter ∈ Set.Icc lower upper,
      circleC2Seminorm (tilt epsilon parameter) +
          cellC2Seminorm (remainder epsilon parameter) ≤
        bound * |epsilon|

end Grad.PhysicalFamily
