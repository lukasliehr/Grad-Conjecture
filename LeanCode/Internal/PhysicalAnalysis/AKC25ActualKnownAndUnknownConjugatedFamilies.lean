import AKC24SameGaugeAndFirstConjugatedInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Set
open scoped BigOperators ContDiff
namespace Grad.AnnularWeightedSmoothness
open Grad.AnnularRadialSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularKernelContinuity
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem radialKnownEncodedDataKernel_conjugated_smooth :
    SmoothConjugatedFamily (source := 7) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialKnownEncodedDataKernel parameters L compact state.val r state.gaugeSmall) := by
  have i0 := smoothConjugatedFamily_fixed parameters lower positive bounded firstCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have i1 := smoothConjugatedFamily_fixed parameters lower positive bounded secondCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have i2 := smoothConjugatedFamily_fixed parameters lower positive bounded thirdCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have slot (component : Fin 7) := smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => sevenInputSlotKernel p component) (fun p q => sameConstantMatrixKernel p q _ _ _)
  have scaledSlot := smoothConjugatedFamily_fixed parameters lower positive bounded
    (fun p => fullKernelSmul (L : ℂ)⁻¹ (sevenInputSlotKernel p 2))
    (fun _ _ _ _ => rfl)
  have mean := smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => angularMeanKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have free := smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have qstar := (radialGaugeQKernel_conjugated_smooth parameters L compact state.val lower positive bounded state.gaugeSmall).comp (i1.comp (slot 3))
  have rqstar := i1.comp (slot 1)
  have f0 := radialForceKernel_conjugated_smooth parameters L compact state.val lower positive bounded 0 0
  have f2 := radialForceKernel_conjugated_smooth parameters L compact state.val lower positive bounded 1 0
  have rf0 := radialRotatedForceKernel_conjugated_smooth parameters L compact state.val lower positive bounded 0 0
  exact (i0.comp ((mean.comp (slot 4)).sub (mean.comp (f0.comp qstar)))).add
    ((i1.comp ((slot 5).sub (free.comp ((rf0.comp qstar).add (f0.comp rqstar))))).add
      (i2.comp (((slot 6).add scaledSlot).sub (free.comp (f2.comp qstar)))))

theorem radialKnownWKernel_conjugated_smooth :
    SmoothConjugatedFamily (source := 7) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialKnownWKernel parameters L compact state.val r state.firstSmall) :=
  (radialEncodedFirstInverseKernel_conjugated_smooth parameters L compact state.val lower positive bounded state.firstSmall).comp
    (radialKnownEncodedDataKernel_conjugated_smooth parameters L compact state lower positive bounded)

theorem radialKnownAStarKernel_conjugated_smooth :
    SmoothConjugatedFamily (source := 7) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialKnownAStarKernel parameters L compact state.val r state.firstSmall) := by
  have j := smoothConjugatedFamily_fixed parameters lower positive bounded encodedJKernel sameEncodedJKernel
  have i1 := smoothConjugatedFamily_fixed parameters lower positive bounded secondCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have slot := smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => sevenInputSlotKernel p 3) (fun p q => sameConstantMatrixKernel p q _ _ _)
  exact (radialGaugeQKernel_conjugated_smooth parameters L compact state.val lower positive bounded state.gaugeSmall).comp
    ((j.comp (radialKnownWKernel_conjugated_smooth parameters L compact state lower positive bounded)).add (i1.comp slot))

theorem radialKnownRAStarKernel_conjugated_smooth :
    SmoothConjugatedFamily (source := 7) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialKnownRAStarKernel parameters L compact state.val r state.firstSmall) := by
  have rotation := smoothConjugatedFamily_fixed parameters lower positive bounded encodedRotationKernel sameEncodedRotationKernel
  have i1 := smoothConjugatedFamily_fixed parameters lower positive bounded secondCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have slot := smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => sevenInputSlotKernel p 1) (fun p q => sameConstantMatrixKernel p q _ _ _)
  exact (rotation.comp (radialKnownWKernel_conjugated_smooth parameters L compact state lower positive bounded)).add (i1.comp slot)

theorem radialUnknownNKernel_conjugated_smooth :
    SmoothConjugatedFamily (source := 1) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialUnknownNKernel parameters L compact state.val r state.firstSmall) := by
  have i0 := smoothConjugatedFamily_fixed parameters lower positive bounded firstCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have i1 := smoothConjugatedFamily_fixed parameters lower positive bounded secondCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have i2 := smoothConjugatedFamily_fixed parameters lower positive bounded thirdCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have twice := smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => fullKernelSmul 2 (fullIdentityKernel p 1)) (fun _ _ _ _ => rfl)
  have mean := smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => angularMeanKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have free := smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have qa := (radialGaugeQKernel_conjugated_smooth parameters L compact state.val lower positive bounded state.gaugeSmall).comp
    (smoothConjugatedFamily_fixed parameters lower positive bounded actualUnknownQAKernel sameUnknownQAKernel)
  have f0 := radialForceKernel_conjugated_smooth parameters L compact state.val lower positive bounded 0 0
  have f2 := radialForceKernel_conjugated_smooth parameters L compact state.val lower positive bounded 1 0
  have rf0 := radialRotatedForceKernel_conjugated_smooth parameters L compact state.val lower positive bounded 0 0
  exact (i0.comp (mean.comp (f0.comp qa)).neg).add
    ((i1.comp (twice.sub ((rf0.comp qa).add (f0.comp i0)))).add
      (i2.comp (free.comp (f2.comp qa)).neg))

theorem radialUnknownWKernel_conjugated_smooth :
    SmoothConjugatedFamily (source := 1) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialUnknownWKernel parameters L compact state.val r state.firstSmall) :=
  (radialEncodedFirstInverseKernel_conjugated_smooth parameters L compact state.val lower positive bounded state.firstSmall).comp
    (radialUnknownNKernel_conjugated_smooth parameters L compact state lower positive bounded)

theorem radialUnknownUKernel_conjugated_smooth :
    SmoothConjugatedFamily (source := 1) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialUnknownUKernel parameters L compact state.val r state.firstSmall) := by
  have j := smoothConjugatedFamily_fixed parameters lower positive bounded encodedJKernel sameEncodedJKernel
  have qa := smoothConjugatedFamily_fixed parameters lower positive bounded actualUnknownQAKernel sameUnknownQAKernel
  exact (radialGaugeQKernel_conjugated_smooth parameters L compact state.val lower positive bounded state.gaugeSmall).comp
    ((j.comp (radialUnknownWKernel_conjugated_smooth parameters L compact state lower positive bounded)).add qa)

theorem radialUnknownVKernel_conjugated_smooth :
    SmoothConjugatedFamily (source := 1) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialUnknownVKernel parameters L compact state.val r state.firstSmall) := by
  have rotation := smoothConjugatedFamily_fixed parameters lower positive bounded encodedRotationKernel sameEncodedRotationKernel
  have i0 := smoothConjugatedFamily_fixed parameters lower positive bounded firstCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  exact (rotation.comp (radialUnknownWKernel_conjugated_smooth parameters L compact state lower positive bounded)).add i0

end Grad.AnnularWeightedSmoothness
