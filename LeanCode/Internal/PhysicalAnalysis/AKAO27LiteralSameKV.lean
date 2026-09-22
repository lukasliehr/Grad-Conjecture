import AKAO26SameOriginalForceZero

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
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
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

/-- Literal AD14/15 on the SAME full fields. Both internal P factors remain inside their cofactor products. -/
theorem fullField_originalKV (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.physicalKV parameters length compact lower positive bounded state).fullField bounded (radius,angles) =
      (originalCofactorJetRowProduct parameters length compact state 1 0 1 (collarRadius lower positive bounded.le radius)
        (fun query => curves.fullField bounded (radius,query)) angles +
      originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
        1 angles.2 angles.1 (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) 0 •
          removePolarMean (fun query => (curves.retainedForce parameters length compact lower positive bounded state).fullField bounded (radius,query)) angles) +
      originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
        1 angles.2 angles.1 (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) 1 •
          (curves.forceZero parameters length compact lower positive bounded state).fullField bounded (radius,angles) -
      originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
        1 angles.2 angles.1 (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) 2 •
          removePolarMean (fun query => (physicalForceCurves parameters length compact lower positive bounded state.val 1 curves).fullField bounded (radius,query)) angles := by
  let angular := radialCofactorJetRowKernel parameters length compact state 1 0 1
  let kappa := fun component => radialSignedCofactorComponentKernel parameters length compact state 1 component
  let free := fun r : RadialPoint => angularMeanFreeKernel (radialKernelParameters parameters r) 1
  let retained := fun r => radialRetainedForceKernel parameters length compact state.val.val r
  let forceZero := radialOriginalForceZeroKernel parameters length compact state
  let forceOne := fun r => radialForceKernel parameters length compact state.val.val r 1 0
  have angularRegular := radialCofactorJetRowKernel_regular parameters length compact state 1 0 1
  have kappaRegular := fun component => radialSignedCofactorComponentKernel_regular parameters length compact state 1 component
  have freeRegular : RegularKernelFamily free := scalarModeRadialKernel_regular parameters _ _ _ _
  have retainedRegular := radialRetainedForceKernel_regular parameters length compact state.val
  have zeroRegular := radialOriginalForceZeroKernel_regular parameters length compact state
  have oneRegular := radialForceKernel_regular parameters length compact state.val.val 1 0
  have angularSmooth := actualCofactorRow_conjugated_smooth parameters length compact state lower positive bounded 1 0 1
  have kappaSmooth := fun component => actualSignedCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 1 component
  have freeSmooth : SmoothConjugatedFamily parameters lower positive bounded.le free :=
    smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => angularMeanFreeKernel p 1)
      (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have retainedSmooth := actualRetainedForce_conjugated_smooth parameters length compact state lower positive bounded
  have zeroSmooth := actualOriginalForceZero_conjugated_smooth parameters length compact state lower positive bounded
  have oneSmooth := radialForceKernel_conjugated_smooth parameters length compact state.val.val lower positive bounded 1 0
  let first := fun r => fullKernelComposition (kappa 0 r) (fullKernelComposition (free r) (retained r))
  let second := fun r => fullKernelComposition (kappa 1 r) (forceZero r)
  let third := fun r => fullKernelComposition (kappa 2 r) (fullKernelComposition (free r) (forceOne r))
  have firstRegular := (kappaRegular 0).comp (freeRegular.comp retainedRegular)
  have secondRegular := (kappaRegular 1).comp zeroRegular
  have thirdRegular := (kappaRegular 2).comp (freeRegular.comp oneRegular)
  have firstSmooth := (kappaSmooth 0).comp (freeSmooth.comp retainedSmooth)
  have secondSmooth := (kappaSmooth 1).comp zeroSmooth
  have thirdSmooth := (kappaSmooth 2).comp (freeSmooth.comp oneSmooth)
  have decomposition := fullField_action_sub parameters lower positive bounded curves
    (fun r => fullKernelAdd (fullKernelAdd (angular r) (first r)) (second r)) third
    ((angularRegular.add firstRegular).add secondRegular) thirdRegular
    ((angularSmooth.add firstSmooth).add secondSmooth) thirdSmooth radius inside angles
  rw [fullField_action_add parameters lower positive bounded curves
      (fun r => fullKernelAdd (angular r) (first r)) second (angularRegular.add firstRegular) secondRegular
      (angularSmooth.add firstSmooth) secondSmooth radius inside angles,
    fullField_action_add parameters lower positive bounded curves angular first angularRegular firstRegular angularSmooth firstSmooth radius inside angles] at decomposition
  let firstInner := curves.action parameters lower positive bounded
    (fun r => fullKernelComposition (free r) (retained r)) (freeRegular.comp retainedRegular) (freeSmooth.comp retainedSmooth)
  have firstSame := fullField_action_comp parameters lower positive bounded curves (kappa 0)
    (fun r => fullKernelComposition (free r) (retained r)) (kappaRegular 0) (freeRegular.comp retainedRegular)
    (kappaSmooth 0) (freeSmooth.comp retainedSmooth) radius inside angles
  change (curves.action parameters lower positive bounded first firstRegular firstSmooth).fullField bounded (radius,angles) =
    (firstInner.signedCofactorComponent parameters length compact lower positive bounded state 1 0).fullField bounded (radius,angles) at firstSame
  rw [fullField_signedCofactorComponent parameters length compact lower positive bounded state 1 firstInner 0 radius inside angles,
    fullField_action_comp parameters lower positive bounded curves free retained freeRegular retainedRegular freeSmooth retainedSmooth radius inside angles,
    fullField_action_meanFree parameters lower positive bounded (curves.action parameters lower positive bounded retained retainedRegular retainedSmooth) radius inside angles] at firstSame
  let thirdInner := curves.action parameters lower positive bounded
    (fun r => fullKernelComposition (free r) (forceOne r)) (freeRegular.comp oneRegular) (freeSmooth.comp oneSmooth)
  have thirdSame := fullField_action_comp parameters lower positive bounded curves (kappa 2)
    (fun r => fullKernelComposition (free r) (forceOne r)) (kappaRegular 2) (freeRegular.comp oneRegular)
    (kappaSmooth 2) (freeSmooth.comp oneSmooth) radius inside angles
  change (curves.action parameters lower positive bounded third thirdRegular thirdSmooth).fullField bounded (radius,angles) =
    (thirdInner.signedCofactorComponent parameters length compact lower positive bounded state 1 2).fullField bounded (radius,angles) at thirdSame
  rw [fullField_signedCofactorComponent parameters length compact lower positive bounded state 1 thirdInner 2 radius inside angles,
    fullField_action_comp parameters lower positive bounded curves free forceOne freeRegular oneRegular freeSmooth oneSmooth radius inside angles,
    fullField_action_meanFree parameters lower positive bounded (curves.action parameters lower positive bounded forceOne oneRegular oneSmooth) radius inside angles] at thirdSame
  have secondSame := fullField_action_comp parameters lower positive bounded curves (kappa 1) forceZero
    (kappaRegular 1) zeroRegular (kappaSmooth 1) zeroSmooth radius inside angles
  change (curves.action parameters lower positive bounded second secondRegular secondSmooth).fullField bounded (radius,angles) =
    ((curves.action parameters lower positive bounded forceZero zeroRegular zeroSmooth).signedCofactorComponent parameters length compact lower positive bounded state 1 1).fullField bounded (radius,angles) at secondSame
  rw [fullField_signedCofactorComponent parameters length compact lower positive bounded state 1
    (curves.action parameters lower positive bounded forceZero zeroRegular zeroSmooth) 1 radius inside angles] at secondSame
  have angularSame := fullField_cofactorJetRowProduct parameters length compact lower positive bounded state 1 0 1 curves radius inside angles
  change (curves.action parameters lower positive bounded angular angularRegular angularSmooth).fullField bounded (radius,angles) =
    originalCofactorJetRowProduct parameters length compact state 1 0 1 (collarRadius lower positive bounded.le radius)
      (fun query => curves.fullField bounded (radius,query)) angles at angularSame
  rw [firstSame,secondSame,thirdSame,angularSame] at decomposition
  exact decomposition

end Grad.ActualPolarFlux
