import AKBK4LiteralForceCellAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.BoundaryTrace
open Grad.SourceCollarCoefficients Grad.ActualCartesianEquations Grad.PDEBootstrap Grad.SourceCollarFullSource
open Grad.Constraints
open Grad.GaugeCoefficients.Physical.Ledger Grad.Constraints.Gauges Grad.PhysicalFamily Grad.CartesianStartup

def nativePlanarForceCell (xi : Spatial → ComplexEuclidean 1) (covariant correction : Spatial → ComplexEuclidean 3)
    (point : Spatial) : ComplexEuclidean 2 :=
  planarPartMap (nativeScalarGradient xi point - fderiv ℝ covariant point (planeQuarterTurn point) -
    polarQuarter (covariant point) + correction point)

/-- All Fourier and derivative premises refer to the SAME native cells.
Only the two force coordinates of the fully multiplied correction are used. -/
theorem nativePlanarForceCell_fourier (xi : Spatial → ComplexEuclidean 1)
    (covariant correction : Spatial → ComplexEuclidean 3) (point : Spatial) (cell : ℤ)
    (gradient rotation fullCovariant fullCorrection : ℝ → ComplexEuclidean 3)
    (gradientContinuous : Continuous gradient) (rotationContinuous : Continuous rotation)
    (covariantContinuous : Continuous fullCovariant) (correctionContinuous : Continuous fullCorrection)
    (sameGradient : angularCoefficient gradient cell = nativeScalarGradient xi point)
    (sameRotation : angularCoefficient rotation cell = fderiv ℝ covariant point (planeQuarterTurn point))
    (sameCovariant : angularCoefficient fullCovariant cell = covariant point)
    (sameCorrection : planarPartMap (angularCoefficient fullCorrection cell) = planarPartMap (correction point)) :
    angularCoefficient (fun axial => planarPartMap (cartesianForceValue
      (gradient axial) (rotation axial) (fullCovariant axial) (fullCorrection axial))) cell =
      nativePlanarForceCell xi covariant correction point := by
  rw [originalForceValue_axialCell gradient rotation fullCovariant fullCorrection gradientContinuous rotationContinuous
    covariantContinuous correctionContinuous cell,sameGradient,sameRotation,sameCovariant,nativePlanarForceCell,
    map_add,map_add,sameCorrection]

/-- The literal native cell differential expression is exactly the original
force flux divergence minus Ja plus the original correction. -/
theorem nativePlanarForceCell_flux (xi : Spatial → ComplexEuclidean 1)
    (covariant correction : Spatial → ComplexEuclidean 3) (point : Spatial)
    (xiDifferentiable : DifferentiableAt ℝ xi point) (covariantDifferentiable : DifferentiableAt ℝ covariant point) :
    nativePlanarForceCell xi covariant correction point =
      originalPlanarDivergence (originalForceFlux (fun current => xi current 0)
        (fun current => planarPartMap (covariant current))) point -
      quarterValueMap (planarPartMap (covariant point)) + planarPartMap (correction point) := by
  let scalarProjection := (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin 1 => ℂ) 0).restrictScalars ℝ
  have scalarDerivative : HasFDerivAt (fun current => xi current 0)
      (scalarProjection.comp (fderiv ℝ xi point)) point :=
    scalarProjection.hasFDerivAt.comp point xiDifferentiable.hasFDerivAt
  have planarDerivative : HasFDerivAt (fun current => planarPartMap (covariant current))
      ((planarPartMap.restrictScalars ℝ).comp (fderiv ℝ covariant point)) point :=
    (planarPartMap.restrictScalars ℝ).hasFDerivAt.comp point covariantDifferentiable.hasFDerivAt
  rw [originalForceFlux_divergence _ _ point scalarDerivative.differentiableAt planarDerivative.differentiableAt,
    originalPlanarGradient,scalarDerivative.fderiv,planarDerivative.fderiv]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;>
    simp [nativePlanarForceCell,nativeScalarGradient,planarPartMap,
      polarQuarter,quarterValueMap,quarterValueLinear,matrixUnit_apply,operatorBasis,scalarProjection,
      spatialBasis,spatialDirection]

end Grad.ActualCartesianWeakEquations
