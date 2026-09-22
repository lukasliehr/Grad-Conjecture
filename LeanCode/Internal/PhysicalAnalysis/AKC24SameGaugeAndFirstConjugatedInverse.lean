import AKC23ActualSigmaConjugatedFamilies
import AKC21SameOriginalConjugatedInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Set
open scoped BigOperators ContDiff
namespace Grad.AnnularWeightedSmoothness
open Grad.AnnularRadialSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularKernelContinuity
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem radialNegativeGammaInverseKernel_conjugated_smooth
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialGaugeLowRadius parameters L compact) :
    SmoothConjugatedFamily (source := 2) (target := 2) parameters lower positive bounded.le (fun r : RadialPoint => radialNegativeGammaInverseKernel parameters L compact state r small) := by
  exact (radialGammaDeviationKernel_conjugated_smooth parameters L compact state lower positive bounded).neg.negativeInverse
    bounded (radialGammaDeviationKernel_regular parameters L compact state).neg
    (1 / 2) (by norm_num) (by norm_num)
    (fun r => radialGammaDeviationKernel_small parameters L compact state r small)

theorem radialGaugeQKernel_conjugated_smooth
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialGaugeLowRadius parameters L compact) :
    SmoothConjugatedFamily (source := 3) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialGaugeQKernel parameters L compact state r small) := by
  have tail := smoothConjugatedFamily_fixed parameters lower positive bounded tailInjectionKernel
    (fun first second => sameConstantMatrixKernel first second _ _ _)
  have mean := smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => angularMeanKernel p 2)
    (fun first second => sameScalarModeDiagonalKernel first second 2 _ _ _)
  exact (smoothConjugatedFamily_identity parameters lower positive bounded.le 3).add
    (tail.comp ((radialNegativeGammaInverseKernel_conjugated_smooth parameters L compact state lower positive bounded small).comp
      (mean.comp (radialGaugeRowsKernel_conjugated_smooth parameters L compact state lower positive bounded 0))))

theorem radialEncodedPerturbationKernel_conjugated_smooth
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialGaugeLowRadius parameters L compact) :
    SmoothConjugatedFamily (source := 3) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialEncodedPerturbationKernel parameters L compact state r small) := by
  have j := smoothConjugatedFamily_fixed parameters lower positive bounded encodedJKernel sameEncodedJKernel
  have rotation := smoothConjugatedFamily_fixed parameters lower positive bounded encodedRotationKernel sameEncodedRotationKernel
  have i0 := smoothConjugatedFamily_fixed parameters lower positive bounded firstCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have i1 := smoothConjugatedFamily_fixed parameters lower positive bounded secondCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have i2 := smoothConjugatedFamily_fixed parameters lower positive bounded thirdCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have mean := smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => angularMeanKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have free := smoothConjugatedFamily_fixed parameters lower positive bounded (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have qj := (radialGaugeQKernel_conjugated_smooth parameters L compact state lower positive bounded small).comp j
  have f0 := radialForceKernel_conjugated_smooth parameters L compact state lower positive bounded 0 0
  have f2 := radialForceKernel_conjugated_smooth parameters L compact state lower positive bounded 1 0
  have rf0 := radialRotatedForceKernel_conjugated_smooth parameters L compact state lower positive bounded 0 0
  exact (i0.comp (mean.comp (f0.comp qj))).add
    ((i1.comp (free.comp ((rf0.comp qj).add (f0.comp rotation)))).add
      (i2.comp (free.comp (f2.comp qj))))

theorem radialPreconditionedEncodedKernel_conjugated_smooth
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialGaugeLowRadius parameters L compact) :
    SmoothConjugatedFamily (source := 3) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialPreconditionedEncodedKernel parameters L compact state r small) :=
  (smoothConjugatedFamily_fixed parameters lower positive bounded encodedD0InverseKernel (fun p q => sameConstantMatrixKernel p q _ _ _)).comp
    (radialEncodedPerturbationKernel_conjugated_smooth parameters L compact state lower positive bounded small)

/-- The exact radius-dependent first-system inverse has continuous entries
and every radius-uniform kernel moment on its original B7 low ball. -/
theorem radialEncodedFirstInverseKernel_conjugated_smooth
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialFirstLowRadius parameters L compact) :
    SmoothConjugatedFamily (source := 3) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialEncodedFirstInverseKernel parameters L compact state r small) := by
  have inverse := (radialPreconditionedEncodedKernel_conjugated_smooth parameters L compact state lower positive bounded (small.trans (min_le_left _ _))).neg.negativeInverse
    bounded (radialPreconditionedEncodedKernel_regular parameters L compact state (small.trans (min_le_left _ _))).neg
    (1 / 2) (by norm_num) (by norm_num)
    (fun r => radialPreconditionedEncodedKernel_small parameters L compact state r small)
  exact inverse.neg.comp
    (smoothConjugatedFamily_fixed parameters lower positive bounded encodedD0InverseKernel (fun p q => sameConstantMatrixKernel p q _ _ _))

end Grad.AnnularWeightedSmoothness
