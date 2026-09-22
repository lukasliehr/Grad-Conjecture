import AKAO27LiteralSameKV

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
    {row : DivisionRow 7 lower} (curves : SmoothLowPhysicalRow parameters lower positive row)

/-- Literal AH23 on the SAME full reconstructed field. All coefficient jets are actual derivatives by AKAO25. -/
theorem fullField_originalRV (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (curves.lowPhysicalCurves parameters length compact lower positive bounded state 2).fullField bounded (radius,angles) =
      removePolarMean (fun query =>
        (originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
          1 query.2 query.1 (polarClosedPoint radius query.1 (positive.le.trans inside.1) inside.2) 1 •
            matrixUnit (0 : Fin 1) (1 : Fin 7) (curves.fullField bounded (radius,query)) +
        ((curves.covariant parameters length compact lower positive bounded state.val).physicalKV parameters length compact lower positive bounded state).fullField bounded (radius,query)) -
        (radius : ℂ) • (originalCofactorJetSeries parameters length compact state 1 0 1 0 (collarRadius lower positive bounded.le radius) query •
          matrixUnit (0 : Fin 1) (3 : Fin 7) (curves.fullField bounded (radius,query))) -
        ((radius : ℂ) * (length : ℂ)⁻¹) • (originalCofactorJetSeries parameters length compact state 1 2 0 2 (collarRadius lower positive bounded.le radius) query •
          matrixUnit (0 : Fin 1) (3 : Fin 7) (curves.fullField bounded (radius,query)))) angles := by
  let slot := fun r : RadialPoint => coordinateProjectionKernel (radialKernelParameters parameters r) 7 3
  have slotRegular : RegularKernelFamily slot := constantMatrixRadialKernel_regular parameters _ _ _
  have slotSmooth : SmoothConjugatedFamily parameters lower positive bounded.le slot :=
    smoothConjugatedFamily_fixed parameters lower positive bounded
      (fun p => coordinateProjectionKernel p 7 3) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  let radialKernel := fun r => fullKernelComposition (radialCofactorJetComponentKernel parameters length compact state 1 0 1 0 r) (slot r)
  let axialKernel := fun r => fullKernelComposition (radialCofactorJetComponentKernel parameters length compact state 1 2 0 2 r) (slot r)
  have radialRegular : RegularKernelFamily radialKernel :=
    (radialCofactorJetComponentKernel_regular parameters length compact state 1 0 1 0).comp slotRegular
  have axialRegular : RegularKernelFamily axialKernel :=
    (radialCofactorJetComponentKernel_regular parameters length compact state 1 2 0 2).comp slotRegular
  have radialSmooth : SmoothConjugatedFamily parameters lower positive bounded.le radialKernel :=
    (actualCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 1 0 1 0).comp slotSmooth
  have axialSmooth : SmoothConjugatedFamily parameters lower positive bounded.le axialKernel :=
    (actualCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 1 2 0 2).comp slotSmooth
  have radiusSmooth : ContDiffOn ℝ ∞ (fun location : ℝ => (location : ℂ)) (Icc lower 1) := Complex.ofRealCLM.contDiff.contDiffOn
  have radialScaledRegular := RegularKernelFamily.radial_smul radialRegular (fun r => (r.val : ℂ))
    (Complex.continuous_ofReal.comp continuous_subtype_val) 1 (by norm_num) radialPoint_norm_le_one
  have axialScaledRegular := RegularKernelFamily.radial_smul axialRegular (fun r => (r.val : ℂ) * (length : ℂ)⁻¹)
    ((Complex.continuous_ofReal.comp continuous_subtype_val).mul continuous_const) ‖(length : ℂ)⁻¹‖ (norm_nonneg _) (fun r => by
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (radialPoint_norm_le_one r) (norm_nonneg _)).trans_eq (one_mul _))
  have radialScaledSmooth := SmoothConjugatedFamily.smul radialSmooth (fun location : ℝ => (location : ℂ)) radiusSmooth
  have axialScaledSmooth := SmoothConjugatedFamily.smul axialSmooth (fun location : ℝ => (location : ℂ) * (length : ℂ)⁻¹) (radiusSmooth.mul contDiffOn_const)
  have radialSame := fun query => fullField_action_radial_smul parameters lower positive bounded curves
    (fun location : ℝ => (location : ℂ)) radiusSmooth.continuousOn radialKernel radialRegular radialSmooth
    radialScaledRegular radialScaledSmooth radius inside query
  have axialSame := fun query => fullField_action_radial_smul parameters lower positive bounded curves
    (fun location : ℝ => (location : ℂ) * (length : ℂ)⁻¹) (radiusSmooth.mul contDiffOn_const).continuousOn axialKernel axialRegular axialSmooth
    axialScaledRegular axialScaledSmooth radius inside query
  let slotOne := fun r : RadialPoint => coordinateProjectionKernel (radialKernelParameters parameters r) 7 1
  have slotOneRegular : RegularKernelFamily slotOne := constantMatrixRadialKernel_regular parameters _ _ _
  have slotOneSmooth : SmoothConjugatedFamily parameters lower positive bounded.le slotOne :=
    smoothConjugatedFamily_fixed parameters lower positive bounded
      (fun p => coordinateProjectionKernel p 7 1) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)
  let kappa := radialSignedCofactorComponentKernel parameters length compact state 1 1
  have kappaRegular := radialSignedCofactorComponentKernel_regular parameters length compact state 1 1
  have kappaSmooth := actualSignedCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 1 1
  let covariant := fun r => radialNormalizedCovariantKernel parameters length compact state.val.val r state.val.property
  have covariantRegular := radialNormalizedCovariantKernel_regular parameters length compact state.val
  have covariantSmooth := radialNormalizedCovariantKernel_conjugated_smooth parameters length compact state.val lower positive bounded
  let kv := radialKVKernel parameters length compact state
  have kvRegular := radialKVKernel_regular parameters length compact state
  have kvSmooth := actualKV_conjugated_smooth parameters length compact state lower positive bounded
  let first := fun r => fullKernelComposition (kappa r) (slotOne r)
  let second := fun r => fullKernelComposition (kv r) (covariant r)
  let radialScaled := fun r => fullKernelSmul (r.val : ℂ) (radialKernel r)
  let axialScaled := fun r => fullKernelSmul ((r.val : ℂ) * (length : ℂ)⁻¹) (axialKernel r)
  have firstRegular := kappaRegular.comp slotOneRegular
  have secondRegular := kvRegular.comp covariantRegular
  have firstSmooth := kappaSmooth.comp slotOneSmooth
  have secondSmooth := kvSmooth.comp covariantSmooth
  let raw := fun r => fullKernelSub (fullKernelSub (fullKernelAdd (first r) (second r)) (radialScaled r)) (axialScaled r)
  have rawRegular := ((firstRegular.add secondRegular).sub radialScaledRegular).sub axialScaledRegular
  have rawSmooth := ((firstSmooth.add secondSmooth).sub radialScaledSmooth).sub axialScaledSmooth
  have rawSame (query : ℝ × ℝ) := fullField_action_sub parameters lower positive bounded curves
    (fun r => fullKernelSub (fullKernelAdd (first r) (second r)) (radialScaled r)) axialScaled
    ((firstRegular.add secondRegular).sub radialScaledRegular) axialScaledRegular
    ((firstSmooth.add secondSmooth).sub radialScaledSmooth) axialScaledSmooth radius inside query
  have rawExpanded (query : ℝ × ℝ) := rawSame query
  have rawLiteral (query : ℝ × ℝ) :
      (curves.action parameters lower positive bounded raw rawRegular rawSmooth).fullField bounded (radius,query) =
        (originalSignedCofactorRow parameters length state.val.val.epsilon state.val.val.field
          1 query.2 query.1 (polarClosedPoint radius query.1 (positive.le.trans inside.1) inside.2) 1 •
            matrixUnit (0 : Fin 1) (1 : Fin 7) (curves.fullField bounded (radius,query)) +
        ((curves.covariant parameters length compact lower positive bounded state.val).physicalKV parameters length compact lower positive bounded state).fullField bounded (radius,query)) -
        (radius : ℂ) • (originalCofactorJetSeries parameters length compact state 1 0 1 0 (collarRadius lower positive bounded.le radius) query •
          matrixUnit (0 : Fin 1) (3 : Fin 7) (curves.fullField bounded (radius,query))) -
        ((radius : ℂ) * (length : ℂ)⁻¹) • (originalCofactorJetSeries parameters length compact state 1 2 0 2 (collarRadius lower positive bounded.le radius) query •
          matrixUnit (0 : Fin 1) (3 : Fin 7) (curves.fullField bounded (radius,query))) := by
    have law := rawExpanded query
    rw [fullField_action_sub parameters lower positive bounded curves
        (fun r => fullKernelAdd (first r) (second r)) radialScaled (firstRegular.add secondRegular) radialScaledRegular
        (firstSmooth.add secondSmooth) radialScaledSmooth radius inside query,
      fullField_action_add parameters lower positive bounded curves first second firstRegular secondRegular firstSmooth secondSmooth radius inside query,
      radialSame query,axialSame query] at law
    have firstSame := fullField_action_comp parameters lower positive bounded curves kappa slotOne
      kappaRegular slotOneRegular kappaSmooth slotOneSmooth radius inside query
    change (curves.action parameters lower positive bounded first firstRegular firstSmooth).fullField bounded (radius,query) =
      ((curves.action parameters lower positive bounded slotOne slotOneRegular slotOneSmooth).signedCofactorComponent
        parameters length compact lower positive bounded state 1 1).fullField bounded (radius,query) at firstSame
    rw [fullField_signedCofactorComponent parameters length compact lower positive bounded state 1
        (curves.action parameters lower positive bounded slotOne slotOneRegular slotOneSmooth) 1 radius inside query,
      fullField_action_projection parameters lower positive bounded curves 1 radius inside query,
      SmoothLowPhysicalRow.fullField_bulkUnit curves bounded 0 1 radius inside query] at firstSame
    have secondSame := fullField_action_comp parameters lower positive bounded curves kv covariant
      kvRegular covariantRegular kvSmooth covariantSmooth radius inside query
    have radialProduct := fullField_action_comp parameters lower positive bounded curves
      (radialCofactorJetComponentKernel parameters length compact state 1 0 1 0) slot
      (radialCofactorJetComponentKernel_regular parameters length compact state 1 0 1 0) slotRegular
      (actualCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 1 0 1 0) slotSmooth radius inside query
    change (curves.action parameters lower positive bounded radialKernel radialRegular radialSmooth).fullField bounded (radius,query) =
      ((curves.action parameters lower positive bounded slot slotRegular slotSmooth).cofactorJetComponent
        parameters length compact lower positive bounded state 1 0 1 0).fullField bounded (radius,query) at radialProduct
    rw [fullField_cofactorJetComponentProduct parameters length compact lower positive bounded state 1 0 1 0
        (curves.action parameters lower positive bounded slot slotRegular slotSmooth) radius inside query,
      fullField_action_projection parameters lower positive bounded curves 3 radius inside query,
      SmoothLowPhysicalRow.fullField_bulkUnit curves bounded 0 3 radius inside query] at radialProduct
    have axialProduct := fullField_action_comp parameters lower positive bounded curves
      (radialCofactorJetComponentKernel parameters length compact state 1 2 0 2) slot
      (radialCofactorJetComponentKernel_regular parameters length compact state 1 2 0 2) slotRegular
      (actualCofactorComponent_conjugated_smooth parameters length compact state lower positive bounded 1 2 0 2) slotSmooth radius inside query
    change (curves.action parameters lower positive bounded axialKernel axialRegular axialSmooth).fullField bounded (radius,query) =
      ((curves.action parameters lower positive bounded slot slotRegular slotSmooth).cofactorJetComponent
        parameters length compact lower positive bounded state 1 2 0 2).fullField bounded (radius,query) at axialProduct
    rw [fullField_cofactorJetComponentProduct parameters length compact lower positive bounded state 1 2 0 2
        (curves.action parameters lower positive bounded slot slotRegular slotSmooth) radius inside query,
      fullField_action_projection parameters lower positive bounded curves 3 radius inside query,
      SmoothLowPhysicalRow.fullField_bulkUnit curves bounded 0 3 radius inside query] at axialProduct
    rw [firstSame,secondSame,radialProduct,axialProduct] at law
    exact law
  let free := fun r : RadialPoint => angularMeanFreeKernel (radialKernelParameters parameters r) 1
  have freeRegular : RegularKernelFamily free := scalarModeRadialKernel_regular parameters _ _ _ _
  have freeSmooth : SmoothConjugatedFamily parameters lower positive bounded.le free :=
    smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => angularMeanFreeKernel p 1)
      (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have projected := fullField_action_comp parameters lower positive bounded curves free raw
    freeRegular rawRegular freeSmooth rawSmooth radius inside angles
  rw [fullField_action_meanFree parameters lower positive bounded
    (curves.action parameters lower positive bounded raw rawRegular rawSmooth) radius inside angles] at projected
  simp only [rawLiteral] at projected
  exact projected

end Grad.ActualPolarFlux
