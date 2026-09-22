import CellSolutionFamily
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

noncomputable section

open Set MeasureTheory
open scoped ContDiff Interval

namespace Grad.NonlinearQuotient

open Grad.MainTarget Grad.PhysicalFamily

abbrev ComplexVec := EuclideanSpace ℂ (Fin 3)

def diskBasis (coordinate : Fin 2) : Plane := EuclideanSpace.single coordinate 1

/-- The literal integral O8; its continuous kernel includes the endpoint zero. -/
def radialIntegral {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (field : Plane → Target) (point : Plane) : Target :=
  ∫ scale in (0 : ℝ)..1, Real.negMulLog scale • field (scale • point)

def diskLaplacian {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℝ Target]
    (field : Plane → Target) (point : Plane) : Target :=
  ∑ coordinate : Fin 2,
    fderiv ℝ (fderiv ℝ field) point (diskBasis coordinate) (diskBasis coordinate)

def complexAngularAverage (field : Plane → ℝ → ℂ) (point : Plane) (time : ℝ) : ℂ :=
  (2 * Real.pi)⁻¹ •
    ∫ angle in (0 : ℝ)..2 * Real.pi, field (planeRotationAction angle point) time

def complexRemoveAngularAverage (field : Plane → ℝ → ℂ) (point : Plane) (time : ℝ) : ℂ :=
  field point time - complexAngularAverage field point time

/-- Complex multilinear physical product, deliberately not the Hermitian product. -/
def complexDot (first second : ComplexVec) : ℂ :=
  ∑ coordinate : Fin 3, first coordinate * second coordinate

def complexDeterminant (first second third : ComplexVec) : ℂ :=
  Matrix.det fun row column => (![first, second, third] column) row

def complexTangentGenerator (point : ComplexVec) : ComplexVec :=
  WithLp.toLp 2 ![-point 1, point 0, 0]

def complexAffineStateDerivative (cellLength epsilon : ℝ)
    (mapping : Plane → ℝ → ComplexVec) (point : Plane) (time : ℝ) : ComplexVec :=
  cellDerivative mapping point time + epsilon • complexTangentGenerator (mapping point time) +
    cellLength • EuclideanSpace.single 1 1

def partialPlus {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]
    (field : Plane → Target) (point : Plane) : Target :=
  fderiv ℝ field point (diskBasis 0) + Complex.I • fderiv ℝ field point (diskBasis 1)

def partialMinus {Target : Type*} [NormedAddCommGroup Target] [NormedSpace ℂ Target]
    (field : Plane → Target) (point : Plane) : Target :=
  fderiv ℝ field point (diskBasis 0) - Complex.I • fderiv ℝ field point (diskBasis 1)

def complexDiskCoordinate (point : Plane) : ℂ := ⟨point 0, point 1⟩

def meanEulerAngularProduct (mapping : Plane → ℝ → ComplexVec) : Plane → ℝ → ℂ :=
  complexAngularAverage (fun point time =>
    complexDot (diskEuler mapping point time) (diskAngular mapping point time))

/-- Literal O13 radial quotient; no chosen division witness is stored. -/
def nonlinearRadialQuotient (mapping : Plane → ℝ → ComplexVec)
    (point : Plane) (time : ℝ) : ℂ :=
  radialIntegral (diskLaplacian (fun argument => meanEulerAngularProduct mapping argument time)) point

def quotientFields (cellLength epsilon : ℝ) (mapping : Plane → ℝ → ComplexVec)
    (potential : Plane → ℝ → ℂ) (point : Plane) (time : ℝ) : Fin 4 → ℂ :=
  let z := complexDiskCoordinate point
  let correction := nonlinearRadialQuotient mapping point time
  ![partialPlus (fun argument => potential argument time) point -
      complexDot (partialPlus (fun argument => mapping argument time) point)
        (diskAngular mapping point time) + Complex.I * z + z * correction,
    partialMinus (fun argument => potential argument time) point -
      complexDot (partialMinus (fun argument => mapping argument time) point)
        (diskAngular mapping point time) - Complex.I * star z + star z * correction,
    complexRemoveAngularAverage (fun argument cellTime =>
      complexDeterminant (fderiv ℝ (fun y => mapping y cellTime) argument (diskBasis 0))
        (fderiv ℝ (fun y => mapping y cellTime) argument (diskBasis 1))
        (complexAffineStateDerivative cellLength epsilon mapping argument cellTime)) point time,
    complexRemoveAngularAverage (fun argument cellTime =>
      complexDot (diskAngular mapping argument cellTime)
        (complexAffineStateDerivative cellLength epsilon mapping argument cellTime) -
      cellDerivative potential argument cellTime) point time]

def encodeQuotient (point : Plane) (quotients : Fin 4 → ℂ) : Fin 4 → ℂ :=
  let z := complexDiskCoordinate point
  ![(star z * quotients 0 - z * quotients 1) / (2 * Complex.I),
    (star z * quotients 0 + z * quotients 1) / 2,
    quotients 3, (‖point‖ ^ 2 : ℝ) • quotients 2]

def complexRawRows (cellLength epsilon : ℝ) (mapping : Plane → ℝ → ComplexVec)
    (potential : Plane → ℝ → ℂ) (point : Plane) (time : ℝ) : Fin 4 → ℂ :=
  ![diskAngular potential point time -
      complexDot (diskAngular mapping point time) (diskAngular mapping point time) +
      (‖point‖ ^ 2 : ℝ),
    complexRemoveAngularAverage (fun argument cellTime =>
      diskEuler potential argument cellTime -
        complexDot (diskEuler mapping argument cellTime)
          (diskAngular mapping argument cellTime)) point time,
    complexRemoveAngularAverage (fun argument cellTime =>
      complexDot (diskAngular mapping argument cellTime)
        (complexAffineStateDerivative cellLength epsilon mapping argument cellTime) -
      cellDerivative potential argument cellTime) point time,
    complexRemoveAngularAverage (fun argument cellTime =>
      complexDeterminant (diskEuler mapping argument cellTime)
        (diskAngular mapping argument cellTime)
        (complexAffineStateDerivative cellLength epsilon mapping argument cellTime)) point time]

/-- Exact radial division target, including the axis, before any proof dispatch. -/
def RadialDivisionGoal : Prop :=
  ∀ (field : Plane → ℂ) (radius : ℝ), 0 < radius →
    ContDiffOn ℝ ∞ field (Metric.ball 0 radius) →
    (∀ angle point, point ∈ Metric.ball (0 : Plane) radius →
      field (planeRotationAction angle point) = field point) →
    field 0 = 0 → ∀ point ∈ Metric.ball (0 : Plane) radius,
      field point = (‖point‖ ^ 2 : ℝ) • radialIntegral (diskLaplacian field) point

/-- Exact literal O13--O17 target on a smooth collar. This proposition stores
neither an assumed radial identity nor an assumed projected-row equality. -/
def LiteralRowsGoal : Prop :=
  ∀ (cellLength epsilon radius : ℝ) (mapping : Plane → ℝ → ComplexVec)
    (potential : Plane → ℝ → ℂ), 1 < radius →
    ContDiffOn ℝ ∞ (Function.uncurry mapping) (Metric.ball 0 radius ×ˢ Set.univ) →
    ContDiffOn ℝ ∞ (Function.uncurry potential) (Metric.ball 0 radius ×ˢ Set.univ) →
    (∀ point ∈ Metric.ball (0 : Plane) radius, ∀ time,
      complexAngularAverage potential point time = 0) →
    ∀ point, ‖point‖ ≤ 1 → ∀ time,
      encodeQuotient point (quotientFields cellLength epsilon mapping potential point time) =
        complexRawRows cellLength epsilon mapping potential point time

end Grad.NonlinearQuotient
