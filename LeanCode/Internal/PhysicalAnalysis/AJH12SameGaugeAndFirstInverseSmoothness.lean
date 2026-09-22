import AJH11ActualGammaRadialJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
open scoped BigOperators ContDiff
namespace Grad.AnnularRadialSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularKernelContinuity
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
    (state : RadialCoefficientState parameters L compact)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)

theorem radialNegativeGammaInverseKernel_smooth
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialGaugeLowRadius parameters L compact) :
    SmoothPolynomialFamily (source := 2) (target := 2) parameters lower positive bounded.le (fun r : RadialPoint => radialNegativeGammaInverseKernel parameters L compact state r small) := by
  exact (radialGammaDeviationKernel_smooth parameters L compact state lower positive bounded).neg.negativeInverse
    (1 / 2) (by norm_num)
    (fun r => radialGammaDeviationKernel_small parameters L compact state r small)

theorem radialGaugeQKernel_smooth
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialGaugeLowRadius parameters L compact) :
    SmoothPolynomialFamily (source := 3) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialGaugeQKernel parameters L compact state r small) := by
  have tail := smoothPolynomialFamily_fixed parameters lower positive bounded.le tailInjectionKernel
    (fun first second => sameConstantMatrixKernel first second _ _ _)
  have mean := smoothPolynomialFamily_fixed parameters lower positive bounded.le (fun p => angularMeanKernel p 2)
    (fun first second => sameScalarModeDiagonalKernel first second 2 _ _ _)
  exact (smoothPolynomialFamily_identity parameters lower positive bounded.le 3).add
    (tail.comp ((radialNegativeGammaInverseKernel_smooth parameters L compact state lower positive bounded small).comp
      (mean.comp (radialGaugeRowsKernel_smooth parameters L compact state lower positive bounded 0))))

theorem radialEncodedPerturbationKernel_smooth
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialGaugeLowRadius parameters L compact) :
    SmoothPolynomialFamily (source := 3) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialEncodedPerturbationKernel parameters L compact state r small) := by
  have j := smoothPolynomialFamily_fixed parameters lower positive bounded.le encodedJKernel sameEncodedJKernel
  have rotation := smoothPolynomialFamily_fixed parameters lower positive bounded.le encodedRotationKernel sameEncodedRotationKernel
  have i0 := smoothPolynomialFamily_fixed parameters lower positive bounded.le firstCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have i1 := smoothPolynomialFamily_fixed parameters lower positive bounded.le secondCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have i2 := smoothPolynomialFamily_fixed parameters lower positive bounded.le thirdCoordinateInjectionKernel (fun p q => sameConstantMatrixKernel p q _ _ _)
  have mean := smoothPolynomialFamily_fixed parameters lower positive bounded.le (fun p => angularMeanKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have free := smoothPolynomialFamily_fixed parameters lower positive bounded.le (fun p => angularMeanFreeKernel p 1) (fun p q => sameScalarModeDiagonalKernel p q _ _ _ _)
  have qj := (radialGaugeQKernel_smooth parameters L compact state lower positive bounded small).comp j
  have f0 := radialForceKernel_smooth parameters L compact state lower positive bounded 0 0
  have f2 := radialForceKernel_smooth parameters L compact state lower positive bounded 1 0
  have rf0 := radialRotatedForceKernel_smooth parameters L compact state lower positive bounded 0 0
  exact (i0.comp (mean.comp (f0.comp qj))).add
    ((i1.comp (free.comp ((rf0.comp qj).add (f0.comp rotation)))).add
      (i2.comp (free.comp (f2.comp qj))))

theorem radialPreconditionedEncodedKernel_smooth
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialGaugeLowRadius parameters L compact) :
    SmoothPolynomialFamily (source := 3) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialPreconditionedEncodedKernel parameters L compact state r small) :=
  (smoothPolynomialFamily_fixed parameters lower positive bounded.le encodedD0InverseKernel (fun p q => sameConstantMatrixKernel p q _ _ _)).comp
    (radialEncodedPerturbationKernel_smooth parameters L compact state lower positive bounded small)

/-- The exact radius-dependent first-system inverse has continuous entries
and every radius-uniform kernel moment on its original B7 low ball. -/
theorem radialEncodedFirstInverseKernel_smooth
    (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤ radialFirstLowRadius parameters L compact) :
    SmoothPolynomialFamily (source := 3) (target := 3) parameters lower positive bounded.le (fun r : RadialPoint => radialEncodedFirstInverseKernel parameters L compact state r small) := by
  have inverse := (radialPreconditionedEncodedKernel_smooth parameters L compact state lower positive bounded (small.trans (min_le_left _ _))).neg.negativeInverse
    (1 / 2) (by norm_num)
    (fun r => radialPreconditionedEncodedKernel_small parameters L compact state r small)
  exact inverse.neg.comp
    (smoothPolynomialFamily_fixed parameters lower positive bounded.le encodedD0InverseKernel (fun p q => sameConstantMatrixKernel p q _ _ _))

end Grad.AnnularRadialSmoothness
