import AKAO31SameCorrectedPAngularDerivative

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
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)

theorem originalSignedCofactorRow_symmetric (cofactorRow component : Fin 3)
    (angles : ℝ × ℝ) (point : ClosedDisk) :
    originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field cofactorRow angles.2 angles.1 point component =
      originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field component angles.2 angles.1 point cofactorRow :=
  polarMatrixEntry_symmetric cofactorRow component angles.1 _
    (originalPhysicalSignedCofactor_symmetric parameters length state.val.val.epsilon state.val.val.field angles.2 point)

theorem fullField_signedCofactorRow_vector {row : DivisionRow 3 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (cofactorRow : Fin 3)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.signedCofactorRow parameters length compact lower positive bounded state cofactorRow).fullField bounded (radius,angles) =
      ∑ component : Fin 3,originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
        cofactorRow angles.2 angles.1 (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) component •
          matrixUnit (0 : Fin 1) component (curves.fullField bounded (radius,angles)) := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  simpa [matrixUnit_apply,operatorBasis] using
    fullField_signedCofactorRow parameters length compact lower positive bounded state cofactorRow curves radius inside angles

variable {row : DivisionRow 7 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

theorem fullField_unprojectedP (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.action parameters lower positive bounded
      (originalUnprojectedPKernel parameters length compact state)
      (originalUnprojectedPKernel_regular parameters length compact state)
      (originalUnprojectedPKernel_smooth parameters length compact lower positive bounded state)).fullField bounded (radius,angles) =
    (∑ component : Fin 3,originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
        0 angles.2 angles.1 (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) component •
          matrixUnit (0 : Fin 1) component ((curves.covariant parameters length compact lower positive bounded state.val).fullField bounded (radius,angles))) +
      originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
        1 angles.2 angles.1 (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) 0 •
          matrixUnit (0 : Fin 1) (3 : Fin 7) (curves.fullField bounded (radius,angles)) := by
  let cofactor := radialSignedCofactorRowKernel parameters length compact state 0
  let covariant := fun r => radialNormalizedCovariantKernel parameters length compact state.val.val r state.val.property
  let component := radialSignedCofactorComponentKernel parameters length compact state 0 1
  let projection := fun r : RadialPoint => coordinateProjectionKernel (radialKernelParameters parameters r) 7 3
  have cofactorRegular := radialSignedCofactorRowKernel_regular parameters length compact state 0
  have covariantRegular := radialNormalizedCovariantKernel_regular parameters length compact state.val
  have componentRegular := radialSignedCofactorComponentKernel_regular parameters length compact state 0 1
  have projectionRegular : RegularKernelFamily projection := constantMatrixRadialKernel_regular parameters _ _ _
  have cofactorSmooth := actualSignedCofactorRow_conjugated_smooth parameters length compact state lower positive bounded 0
  have covariantSmooth := radialNormalizedCovariantKernel_conjugated_smooth parameters length compact state.val lower positive bounded
  have componentSmooth := actualSignedCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 0 1
  have projectionSmooth : SmoothConjugatedFamily parameters lower positive bounded.le projection :=
    smoothConjugatedFamily_fixed parameters lower positive bounded
      (fun p => coordinateProjectionKernel p 7 3) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  have decomposition := fullField_action_add parameters lower positive bounded curves
    (fun r => fullKernelComposition (cofactor r) (covariant r))
    (fun r => fullKernelComposition (component r) (projection r))
    (cofactorRegular.comp covariantRegular) (componentRegular.comp projectionRegular)
    (cofactorSmooth.comp covariantSmooth) (componentSmooth.comp projectionSmooth) radius inside angles
  rw [fullField_action_comp parameters lower positive bounded curves cofactor covariant cofactorRegular covariantRegular
      cofactorSmooth covariantSmooth radius inside angles,
    fullField_action_comp parameters lower positive bounded curves component projection componentRegular projectionRegular
      componentSmooth projectionSmooth radius inside angles] at decomposition
  change (curves.action parameters lower positive bounded
      (originalUnprojectedPKernel parameters length compact state)
      (originalUnprojectedPKernel_regular parameters length compact state)
      (originalUnprojectedPKernel_smooth parameters length compact lower positive bounded state)).fullField bounded (radius,angles) =
    ((curves.covariant parameters length compact lower positive bounded state.val).signedCofactorRow parameters length compact lower positive bounded state 0).fullField bounded (radius,angles) +
    ((curves.action parameters lower positive bounded projection projectionRegular projectionSmooth).signedCofactorComponent parameters length compact lower positive bounded state 0 1).fullField bounded (radius,angles) at decomposition
  rw [decomposition,
    fullField_signedCofactorRow_vector parameters length compact lower positive bounded state
      (curves.covariant parameters length compact lower positive bounded state.val) 0 radius inside angles,
    fullField_signedCofactorComponent parameters length compact lower positive bounded state 0
      (curves.action parameters lower positive bounded projection projectionRegular projectionSmooth) 1 radius inside angles,
    fullField_action_projection parameters lower positive bounded curves 3 radius inside angles,
    curves.fullField_bulkUnit bounded (0 : Fin 1) 3 radius inside angles,
    originalSignedCofactorRow_symmetric parameters length compact state 0 1 angles]

/-- The exact original p = P(B_0·a + kappa_1 xi/r), with the outer P explicit. -/
theorem fullField_originalCorrectedP (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.correctedP parameters length compact lower positive bounded state).fullField bounded (radius,angles) =
    removePolarMean (fun query =>
      (∑ component : Fin 3,originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
        0 query.2 query.1 (polarClosedPoint radius query.1 (positive.le.trans inside.1) inside.2) component •
          matrixUnit (0 : Fin 1) component ((curves.covariant parameters length compact lower positive bounded state.val).fullField bounded (radius,query))) +
      originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
        1 query.2 query.1 (polarClosedPoint radius query.1 (positive.le.trans inside.1) inside.2) 0 •
          matrixUnit (0 : Fin 1) (3 : Fin 7) (curves.fullField bounded (radius,query))) angles := by
  let raw := originalUnprojectedPKernel parameters length compact state
  have rawRegular := originalUnprojectedPKernel_regular parameters length compact state
  have rawSmooth := originalUnprojectedPKernel_smooth parameters length compact lower positive bounded state
  let free := fun r : RadialPoint => angularMeanFreeKernel (radialKernelParameters parameters r) 1
  have freeRegular : RegularKernelFamily free := scalarModeRadialKernel_regular parameters _ _ _ _
  have freeSmooth : SmoothConjugatedFamily parameters lower positive bounded.le free :=
    smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => angularMeanFreeKernel p 1)
      (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have projected := fullField_action_comp parameters lower positive bounded curves free raw
    freeRegular rawRegular freeSmooth rawSmooth radius inside angles
  rw [fullField_action_meanFree parameters lower positive bounded
    (curves.action parameters lower positive bounded raw rawRegular rawSmooth) radius inside angles] at projected
  have rawSame := funext (fun query => fullField_unprojectedP parameters length compact lower positive bounded state curves radius inside query)
  change (fun query => (curves.action parameters lower positive bounded raw rawRegular rawSmooth).fullField bounded (radius,query)) = _ at rawSame
  rw [rawSame] at projected
  exact projected

end Grad.ActualPolarFlux
