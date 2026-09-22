import AKAO28LiteralSameRV

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.BoundaryTrace Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceCollarFullSource Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualBoundaryPrimitives Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar Grad.BoundaryLift Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation Grad.ActualForceMatrixFidelity

variable (parameters : PhaseParameters) (length compact : ℝ)
    (state : RetainedInverseState parameters length compact)

def originalRetainedForceValue (r : RadialPoint) (source : ℝ × ℝ → ComplexEuclidean 3) (angles : ℝ × ℝ) : ComplexEuclidean 1 :=
  ∑ component : Fin 3,originalRetainedForceRow parameters length state.val.val.epsilon state.val.val.field angles.2 angles.1
    (polarClosedPoint r.val angles.1 r.property.1 r.property.2) component • matrixUnit (0 : Fin 1) component (source angles)

def originalForceZeroValue (r : RadialPoint) (source : ℝ × ℝ → ComplexEuclidean 3) (angles : ℝ × ℝ) : ComplexEuclidean 1 :=
  forceMatrixProduct parameters length state.val.val.epsilon state.val.val.field 0 r.val r.property.1 r.property.2 source angles -
    (2 : ℂ) • matrixUnit (0 : Fin 1) (0 : Fin 3) (source angles)

def originalKVValue (r : RadialPoint) (source : ℝ × ℝ → ComplexEuclidean 3) (angles : ℝ × ℝ) : ComplexEuclidean 1 :=
  (originalCofactorJetRowProduct parameters length compact state 1 0 1 r source angles +
  originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field 1 angles.2 angles.1
    (polarClosedPoint r.val angles.1 r.property.1 r.property.2) 0 •
      removePolarMean (originalRetainedForceValue parameters length compact state r source) angles) +
  originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field 1 angles.2 angles.1
    (polarClosedPoint r.val angles.1 r.property.1 r.property.2) 1 • originalForceZeroValue parameters length compact state r source angles -
  originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field 1 angles.2 angles.1
    (polarClosedPoint r.val angles.1 r.property.1 r.property.2) 2 •
      removePolarMean (forceMatrixProduct parameters length state.val.val.epsilon state.val.val.field 1 r.val r.property.1 r.property.2 source) angles

/-- The literal normalized AH23 expression, formed solely from the original coefficients and the same fields. -/
def originalRVValue (r : RadialPoint) (seven : ℝ × ℝ → ComplexEuclidean 7)
    (covariant : ℝ × ℝ → ComplexEuclidean 3) (angles : ℝ × ℝ) : ComplexEuclidean 1 :=
  removePolarMean (fun query =>
    (originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field 1 query.2 query.1
      (polarClosedPoint r.val query.1 r.property.1 r.property.2) 1 • matrixUnit (0 : Fin 1) (1 : Fin 7) (seven query) +
      originalKVValue parameters length compact state r covariant query) -
    (r.val : ℂ) • (originalCofactorJetSeries parameters length compact state 1 0 1 0 r query •
      matrixUnit (0 : Fin 1) (3 : Fin 7) (seven query)) -
    ((r.val : ℂ) * (length : ℂ)⁻¹) • (originalCofactorJetSeries parameters length compact state 1 2 0 2 r query •
      matrixUnit (0 : Fin 1) (3 : Fin 7) (seven query))) angles

variable (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

theorem fullField_retainedForceValue (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.retainedForce parameters length compact lower positive bounded state).fullField bounded (radius,angles) =
      originalRetainedForceValue parameters length compact state (collarRadius lower positive bounded.le radius)
        (fun query => curves.fullField bounded (radius,query)) angles := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simpa [originalRetainedForceValue,collarRadius_literal lower positive bounded.le radius inside,matrixUnit_apply,operatorBasis] using
    fullField_originalRetainedForce parameters length compact lower positive bounded state curves radius inside angles

theorem fullField_forceZeroValue (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.forceZero parameters length compact lower positive bounded state).fullField bounded (radius,angles) =
      originalForceZeroValue parameters length compact state (collarRadius lower positive bounded.le radius)
        (fun query => curves.fullField bounded (radius,query)) angles := by
  have law := fullField_originalForceZero parameters length compact lower positive bounded state curves radius inside angles
  rw [fullField_forceMatrixProduct parameters length compact lower positive bounded state.val 0 curves radius inside angles] at law
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simpa [originalForceZeroValue,collarRadius_literal lower positive bounded.le radius inside,matrixUnit_apply,operatorBasis] using law

/-- Exact K_v physical consumer with no completed coefficient action left in its formula. -/
theorem fullField_literalKV (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.physicalKV parameters length compact lower positive bounded state).fullField bounded (radius,angles) =
      originalKVValue parameters length compact state (collarRadius lower positive bounded.le radius)
        (fun query => curves.fullField bounded (radius,query)) angles := by
  have forceTransport :
      forceMatrixProduct parameters length state.val.val.epsilon state.val.val.field 1
        (collarRadius lower positive bounded.le radius).val
        (collarRadius lower positive bounded.le radius).property.1 (collarRadius lower positive bounded.le radius).property.2
        (fun query => curves.fullField bounded (radius,query)) =
      forceMatrixProduct parameters length state.val.val.epsilon state.val.val.field 1 radius
        (positive.le.trans inside.1) inside.2 (fun query => curves.fullField bounded (radius,query)) := by
    funext query
    simp only [forceMatrixProduct,forceAngleEntry,collarRadius_literal lower positive bounded.le radius inside]
  rw [fullField_originalKV parameters length compact lower positive bounded state curves radius inside angles]
  simp only [fullField_retainedForceValue (inside := inside) parameters length compact state lower positive bounded curves,
    fullField_forceZeroValue (inside := inside) parameters length compact state lower positive bounded curves,
    fullField_forceMatrixProduct (inside := inside) parameters length compact lower positive bounded state.val 1 curves]
  simp only [originalKVValue,forceTransport,collarRadius_literal lower positive bounded.le radius inside]

theorem fullField_literalRV {seven : DivisionRow 7 lower}
    (input : SmoothLowPhysicalRow parameters lower positive seven)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (input.lowPhysicalCurves parameters length compact lower positive bounded state 2).fullField bounded (radius,angles) =
      originalRVValue parameters length compact state (collarRadius lower positive bounded.le radius)
        (fun query => input.fullField bounded (radius,query))
        (fun query => (input.covariant parameters length compact lower positive bounded state.val).fullField bounded (radius,query)) angles := by
  rw [fullField_originalRV parameters length compact lower positive bounded state input radius inside angles]
  simp only [fullField_literalKV (inside := inside) parameters length compact state lower positive bounded
    (input.covariant parameters length compact lower positive bounded state.val)]
  simp only [originalRVValue,collarRadius_literal lower positive bounded.le radius inside]

end Grad.ActualPolarFlux
