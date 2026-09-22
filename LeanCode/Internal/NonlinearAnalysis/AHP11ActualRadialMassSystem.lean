import AHP10ActualRadialFirstInverse

noncomputable section
set_option maxHeartbeats 1400000

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualCurrentPrimitives
open Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialFirstLowRadius parameters L compact)

def radialKnownWKernel : RadialKernel parameters r 7 3 :=
  fullKernelComposition (radialEncodedFirstInverseKernel parameters L compact state r small)
    (radialKnownEncodedDataKernel parameters L compact state r (small.trans (min_le_left _ _)))

def radialKnownAStarKernel : RadialKernel parameters r 7 3 :=
  fullKernelComposition
    (radialGaugeQKernel parameters L compact state r (small.trans (min_le_left _ _)))
    (fullKernelAdd
      (fullKernelComposition (encodedJKernel (radialKernelParameters parameters r))
        (radialKnownWKernel parameters L compact state r small))
      (fullKernelComposition (secondCoordinateInjectionKernel (radialKernelParameters parameters r))
        (sevenInputSlotKernel (radialKernelParameters parameters r) 3)))

def radialKnownRAStarKernel : RadialKernel parameters r 7 3 :=
  fullKernelAdd
    (fullKernelComposition (encodedRotationKernel (radialKernelParameters parameters r))
      (radialKnownWKernel parameters L compact state r small))
    (radialKnownRotatedQStarKernel parameters r)

def radialUnknownGaugeQAKernel : RadialKernel parameters r 1 3 :=
  fullKernelComposition
    (radialGaugeQKernel parameters L compact state r (small.trans (min_le_left _ _)))
    (actualUnknownQAKernel (radialKernelParameters parameters r))

def radialUnknownN0Kernel : RadialKernel parameters r 1 3 :=
  fullKernelComposition (firstCoordinateInjectionKernel (radialKernelParameters parameters r))
    (fullKernelNeg
      (fullKernelComposition (angularMeanKernel (radialKernelParameters parameters r) 1)
        (fullKernelComposition (radialForceKernel parameters L compact state r 0 0)
          (radialUnknownGaugeQAKernel parameters L compact state r small))))

def radialUnknownN1Kernel : RadialKernel parameters r 1 3 :=
  fullKernelComposition (secondCoordinateInjectionKernel (radialKernelParameters parameters r))
    (fullKernelSub (fullKernelSmul 2 (fullIdentityKernel (radialKernelParameters parameters r) 1))
      (fullKernelAdd
        (fullKernelComposition (radialRotatedForceKernel parameters L compact state r 0 0)
          (radialUnknownGaugeQAKernel parameters L compact state r small))
        (fullKernelComposition (radialForceKernel parameters L compact state r 0 0)
          (firstCoordinateInjectionKernel (radialKernelParameters parameters r)))))

def radialUnknownN2Kernel : RadialKernel parameters r 1 3 :=
  fullKernelComposition (thirdCoordinateInjectionKernel (radialKernelParameters parameters r))
    (fullKernelNeg
      (fullKernelComposition (angularMeanFreeKernel (radialKernelParameters parameters r) 1)
        (fullKernelComposition (radialForceKernel parameters L compact state r 1 0)
          (radialUnknownGaugeQAKernel parameters L compact state r small))))

def radialUnknownNKernel : RadialKernel parameters r 1 3 :=
  fullKernelAdd (radialUnknownN0Kernel parameters L compact state r small)
    (fullKernelAdd (radialUnknownN1Kernel parameters L compact state r small)
      (radialUnknownN2Kernel parameters L compact state r small))

def radialUnknownWKernel : RadialKernel parameters r 1 3 :=
  fullKernelComposition (radialEncodedFirstInverseKernel parameters L compact state r small)
    (radialUnknownNKernel parameters L compact state r small)

def radialUnknownUKernel : RadialKernel parameters r 1 3 :=
  fullKernelComposition
    (radialGaugeQKernel parameters L compact state r (small.trans (min_le_left _ _)))
    (fullKernelAdd
      (fullKernelComposition (encodedJKernel (radialKernelParameters parameters r))
        (radialUnknownWKernel parameters L compact state r small))
      (actualUnknownQAKernel (radialKernelParameters parameters r)))

def radialUnknownVKernel : RadialKernel parameters r 1 3 :=
  fullKernelAdd
    (fullKernelComposition (encodedRotationKernel (radialKernelParameters parameters r))
      (radialUnknownWKernel parameters L compact state r small))
    (firstCoordinateInjectionKernel (radialKernelParameters parameters r))

def radialSigmaComponentKernel (component : Fin 3) : RadialKernel parameters r 1 1 :=
  radialScalarKernel parameters r 1
    (radialSigmaCoefficients parameters L compact state r component 0)
    (radialSigmaCoefficients_moments parameters L compact state r component 0)

def radialRotatedSigmaComponentKernel (component : Fin 3) : RadialKernel parameters r 1 1 :=
  radialScalarKernel parameters r 1
    (angularCoefficientSequence (radialSigmaCoefficients parameters L compact state r component 0))
    (fun moment => angularCoefficientSequence_moment_summable parameters moment r.val _
      (radialSigmaCoefficients_moments parameters L compact state r component 0 (moment + 1)))

/-- The complete AF12 known term on the normalized seven slots. All four
products remain present, including the two kappa1 terms. -/
def radialKnownJStarKernel : RadialKernel parameters r 7 1 :=
  fullKernelComposition (angularMeanFreeKernel (radialKernelParameters parameters r) 1)
    (fullKernelAdd
      (fullKernelAdd
        (fullKernelComposition (radialRotatedSigmaKernel parameters L compact state r 0)
          (radialKnownAStarKernel parameters L compact state r small))
        (fullKernelComposition (radialSigmaKernel parameters L compact state r 0)
          (radialKnownRAStarKernel parameters L compact state r small)))
      (fullKernelAdd
        (fullKernelComposition (radialRotatedSigmaComponentKernel parameters L compact state r 1)
          (sevenInputSlotKernel (radialKernelParameters parameters r) 3))
        (fullKernelComposition (radialSigmaComponentKernel parameters L compact state r 1)
          (sevenInputSlotKernel (radialKernelParameters parameters r) 1))))

def radialMassPerturbationKernel : RadialKernel parameters r 1 1 :=
  fullKernelComposition (angularMeanFreeKernel (radialKernelParameters parameters r) 1)
    (fullKernelAdd
      (fullKernelComposition (radialRotatedSigmaKernel parameters L compact state r 0)
        (radialUnknownUKernel parameters L compact state r small))
      (fullKernelComposition (radialSigmaKernel parameters L compact state r 0)
        (radialUnknownVKernel parameters L compact state r small)))

end Grad.AnnularReconstruction
