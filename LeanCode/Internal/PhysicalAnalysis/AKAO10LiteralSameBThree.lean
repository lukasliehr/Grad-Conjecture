import AKAO9SameOffDiagonalCofactor

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualPolarFlux
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.AnnularReconstruction
open Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations Grad.BoundaryKernelAction Grad.AnnularKernelL2
open Grad.AnnularKernelContinuity Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.SourceCollar

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact)
    {row : DivisionRow 7 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

/-- Literal b3 = rho_b*a + kappa3*(xi/r), on the SAME reconstructed full field. -/
theorem fullField_originalBThree (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.bThree parameters length compact lower positive bounded state).fullField bounded (radius,angles) 0 =
      (∑ component : Fin 3, originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
        2 angles.2 angles.1 (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) component *
          (curves.covariant parameters length compact lower positive bounded state.val).fullField bounded (radius,angles) component) +
      originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
        1 angles.2 angles.1 (polarClosedPoint radius angles.1 (positive.le.trans inside.1) inside.2) 2 *
          curves.fullField bounded (radius,angles) 3 := by
  let cofactor := radialSignedCofactorRowKernel parameters length compact state 2
  let covariant := fun r => radialNormalizedCovariantKernel parameters length compact state.val.val r state.val.property
  let component := radialSignedCofactorComponentKernel parameters length compact state 1 2
  let projection := fun r : RadialPoint => coordinateProjectionKernel (radialKernelParameters parameters r) 7 3
  have cofactorRegular := radialSignedCofactorRowKernel_regular parameters length compact state 2
  have covariantRegular := radialNormalizedCovariantKernel_regular parameters length compact state.val
  have componentRegular := radialSignedCofactorComponentKernel_regular parameters length compact state 1 2
  have projectionRegular : RegularKernelFamily projection := constantMatrixRadialKernel_regular parameters _ _ _
  have cofactorSmooth := actualSignedCofactorRow_conjugated_smooth parameters length compact state lower positive bounded 2
  have covariantSmooth := radialNormalizedCovariantKernel_conjugated_smooth parameters length compact state.val lower positive bounded
  have componentSmooth := actualSignedCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 1 2
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
  change (curves.bThree parameters length compact lower positive bounded state).fullField bounded (radius,angles) =
    ((curves.covariant parameters length compact lower positive bounded state.val).signedCofactorRow parameters length compact lower positive bounded state 2).fullField bounded (radius,angles) +
    ((curves.action parameters lower positive bounded projection projectionRegular projectionSmooth).signedCofactorComponent parameters length compact lower positive bounded state 1 2).fullField bounded (radius,angles) at decomposition
  rw [decomposition,PiLp.add_apply,
    fullField_signedCofactorRow parameters length compact lower positive bounded state 2
      (curves.covariant parameters length compact lower positive bounded state.val) radius inside angles,
    fullField_signedCofactorComponent_offDiagonal parameters length compact lower positive bounded state 1 2
      (curves.action parameters lower positive bounded projection projectionRegular projectionSmooth) (by decide) radius inside angles,
    fullField_action_projection parameters lower positive bounded curves 3 radius inside angles,
    curves.fullField_bulkUnit bounded (0 : Fin 1) 3 radius inside angles]
  simp [matrixUnit_apply,operatorBasis]

end Grad.ActualPolarFlux
