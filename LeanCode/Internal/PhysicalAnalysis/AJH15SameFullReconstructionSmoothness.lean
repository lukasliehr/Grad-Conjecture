import AJH14ActualKnownAndUnknownSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped BigOperators ContDiff
namespace Grad.AnnularRadialSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularKernelContinuity
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem radialKnownJStarKernel_smooth :
    SmoothPolynomialFamily (source := 7) (target := 1) parameters lower positive bounded.le (fun r : RadialPoint => radialKnownJStarKernel parameters L compact state.val r state.firstSmall) := by
  have free := smoothPolynomialFamily_fixed parameters lower positive bounded.le (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have slot (component : Fin 7) := smoothPolynomialFamily_fixed parameters lower positive bounded.le (fun p => sevenInputSlotKernel p component) (fun p q => sameConstantMatrixKernel p q _ _ _)
  have first := ((radialRotatedSigmaKernel_smooth parameters L compact state.val lower positive bounded 0).comp
    (radialKnownAStarKernel_smooth parameters L compact state lower positive bounded)).add
    ((radialSigmaKernel_smooth parameters L compact state.val lower positive bounded 0).comp
      (radialKnownRAStarKernel_smooth parameters L compact state lower positive bounded))
  have second := ((radialRotatedSigmaComponentKernel_smooth parameters L compact state.val lower positive bounded 1).comp (slot 3)).add
    ((radialSigmaComponentKernel_smooth parameters L compact state.val lower positive bounded 1).comp (slot 1))
  exact free.comp (first.add second)

theorem radialMassPerturbationKernel_smooth :
    SmoothPolynomialFamily (source := 1) (target := 1) parameters lower positive bounded.le (fun r : RadialPoint => radialMassPerturbationKernel parameters L compact state.val r state.firstSmall) := by
  have free := smoothPolynomialFamily_fixed parameters lower positive bounded.le (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  exact free.comp
    (((radialRotatedSigmaKernel_smooth parameters L compact state.val lower positive bounded 0).comp
      (radialUnknownUKernel_smooth parameters L compact state lower positive bounded)).add
      ((radialSigmaKernel_smooth parameters L compact state.val lower positive bounded 0).comp
        (radialUnknownVKernel_smooth parameters L compact state lower positive bounded)))

theorem radialMassInverseKernel_smooth :
    SmoothPolynomialFamily (source := 1) (target := 1) parameters lower positive bounded.le (fun r : RadialPoint => radialMassInverseKernel parameters L compact state.val r state.property) :=
  (radialMassPerturbationKernel_smooth parameters L compact state lower positive bounded).negativeInverse
    (1 / 2) (by norm_num)
    (fun r => radialMassPerturbationKernel_small parameters L compact state.val r state.property)

theorem radialRecoveredMassKernel_smooth :
    SmoothPolynomialFamily (source := 7) (target := 1) parameters lower positive bounded.le (fun r : RadialPoint => radialRecoveredMassKernel parameters L compact state.val r state.property) := by
  have slot := smoothPolynomialFamily_fixed parameters lower positive bounded.le (fun p => sevenInputSlotKernel p 0) (fun p q => sameConstantMatrixKernel p q _ _ _)
  exact (radialMassInverseKernel_smooth parameters L compact state lower positive bounded).comp
    (slot.sub (radialKnownJStarKernel_smooth parameters L compact state lower positive bounded))

/-- The same normalized AH20 kernels, on every radius of the closed unit
interval, act smoothly on each closed positive collar in every polynomial Fourier Hilbert grade. -/
theorem radialNormalizedCovariantKernel_smooth :
    SmoothPolynomialFamily (source := 7) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialNormalizedCovariantKernel parameters L compact state.val r state.property) :=
  ((radialUnknownUKernel_smooth parameters L compact state lower positive bounded).comp
    (radialRecoveredMassKernel_smooth parameters L compact state lower positive bounded)).add
    (radialKnownAStarKernel_smooth parameters L compact state lower positive bounded)

theorem radialNormalizedRotatedCovariantKernel_smooth :
    SmoothPolynomialFamily (source := 7) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialNormalizedRotatedCovariantKernel parameters L compact state.val r state.property) :=
  ((radialUnknownVKernel_smooth parameters L compact state lower positive bounded).comp
    (radialRecoveredMassKernel_smooth parameters L compact state lower positive bounded)).add
    (radialKnownRAStarKernel_smooth parameters L compact state lower positive bounded)

end Grad.AnnularRadialSmoothness
