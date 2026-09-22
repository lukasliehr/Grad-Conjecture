import AKC25ActualKnownAndUnknownConjugatedFamilies

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

theorem radialKnownJStarKernel_conjugated_smooth :
    SmoothConjugatedFamily (source := 7) (target := 1) parameters lower positive bounded.le (fun r : RadialPoint => radialKnownJStarKernel parameters L compact state.val r state.firstSmall) := by
  have free := smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have slot (component : Fin 7) := smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => sevenInputSlotKernel p component) (fun p q => sameConstantMatrixKernel p q _ _ _)
  have first := ((radialRotatedSigmaKernel_conjugated_smooth parameters L compact state.val lower positive bounded 0).comp
    (radialKnownAStarKernel_conjugated_smooth parameters L compact state lower positive bounded)).add
    ((radialSigmaKernel_conjugated_smooth parameters L compact state.val lower positive bounded 0).comp
      (radialKnownRAStarKernel_conjugated_smooth parameters L compact state lower positive bounded))
  have second := ((radialRotatedSigmaComponentKernel_conjugated_smooth parameters L compact state.val lower positive bounded 1).comp (slot 3)).add
    ((radialSigmaComponentKernel_conjugated_smooth parameters L compact state.val lower positive bounded 1).comp (slot 1))
  exact free.comp (first.add second)

theorem radialMassPerturbationKernel_conjugated_smooth :
    SmoothConjugatedFamily (source := 1) (target := 1) parameters lower positive bounded.le (fun r : RadialPoint => radialMassPerturbationKernel parameters L compact state.val r state.firstSmall) := by
  have free := smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  exact free.comp
    (((radialRotatedSigmaKernel_conjugated_smooth parameters L compact state.val lower positive bounded 0).comp
      (radialUnknownUKernel_conjugated_smooth parameters L compact state lower positive bounded)).add
      ((radialSigmaKernel_conjugated_smooth parameters L compact state.val lower positive bounded 0).comp
        (radialUnknownVKernel_conjugated_smooth parameters L compact state lower positive bounded)))

theorem radialMassInverseKernel_conjugated_smooth :
    SmoothConjugatedFamily (source := 1) (target := 1) parameters lower positive bounded.le (fun r : RadialPoint => radialMassInverseKernel parameters L compact state.val r state.property) :=
  (radialMassPerturbationKernel_conjugated_smooth parameters L compact state lower positive bounded).negativeInverse
    bounded (radialMassPerturbationKernel_regular parameters L compact state)
    (1 / 2) (by norm_num) (by norm_num)
    (fun r => radialMassPerturbationKernel_small parameters L compact state.val r state.property)

theorem radialRecoveredMassKernel_conjugated_smooth :
    SmoothConjugatedFamily (source := 7) (target := 1) parameters lower positive bounded.le (fun r : RadialPoint => radialRecoveredMassKernel parameters L compact state.val r state.property) := by
  have slot := smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => sevenInputSlotKernel p 0) (fun p q => sameConstantMatrixKernel p q _ _ _)
  exact (radialMassInverseKernel_conjugated_smooth parameters L compact state lower positive bounded).comp
    (slot.sub (radialKnownJStarKernel_conjugated_smooth parameters L compact state lower positive bounded))

/-- The SAME normalized AH20 kernel has every finite radial order at the original analytic width, with a finite polynomial input reserve. -/
theorem radialNormalizedCovariantKernel_conjugated_smooth :
    SmoothConjugatedFamily (source := 7) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialNormalizedCovariantKernel parameters L compact state.val r state.property) :=
  ((radialUnknownUKernel_conjugated_smooth parameters L compact state lower positive bounded).comp
    (radialRecoveredMassKernel_conjugated_smooth parameters L compact state lower positive bounded)).add
    (radialKnownAStarKernel_conjugated_smooth parameters L compact state lower positive bounded)

theorem radialNormalizedRotatedCovariantKernel_conjugated_smooth :
    SmoothConjugatedFamily (source := 7) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialNormalizedRotatedCovariantKernel parameters L compact state.val r state.property) :=
  ((radialUnknownVKernel_conjugated_smooth parameters L compact state lower positive bounded).comp
    (radialRecoveredMassKernel_conjugated_smooth parameters L compact state lower positive bounded)).add
    (radialKnownRAStarKernel_conjugated_smooth parameters L compact state lower positive bounded)

end Grad.AnnularWeightedSmoothness
