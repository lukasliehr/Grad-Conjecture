import AHP7UniformRadialGaugeBound

noncomputable section
set_option maxHeartbeats 1400000

namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

variable (parameters : PhaseParameters) (L compact : ℝ)
variable (state : RadialCoefficientState parameters L compact) (r : RadialPoint)
variable (small : physicalBudget parameters state.data.field state.data.rho state.data.epsilon 7 ≤
  radialGaugeLowRadius parameters L compact)

/-- AE16's actual gauge-corrected decoding at the current radius. -/
def radialGaugeDecodedKernel : RadialKernel parameters r 3 3 :=
  fullKernelComposition (radialGaugeQKernel parameters L compact state r small)
    (encodedJKernel (radialKernelParameters parameters r))

def radialEncodedE0Kernel : RadialKernel parameters r 3 3 :=
  fullKernelComposition (firstCoordinateInjectionKernel (radialKernelParameters parameters r))
    (fullKernelComposition (angularMeanKernel (radialKernelParameters parameters r) 1)
      (fullKernelComposition (radialForceKernel parameters L compact state r 0 0)
        (radialGaugeDecodedKernel parameters L compact state r small)))

def radialEncodedE1Kernel : RadialKernel parameters r 3 3 :=
  fullKernelComposition (secondCoordinateInjectionKernel (radialKernelParameters parameters r))
    (fullKernelComposition (angularMeanFreeKernel (radialKernelParameters parameters r) 1)
      (fullKernelAdd
        (fullKernelComposition (radialRotatedForceKernel parameters L compact state r 0 0)
          (radialGaugeDecodedKernel parameters L compact state r small))
        (fullKernelComposition (radialForceKernel parameters L compact state r 0 0)
          (encodedRotationKernel (radialKernelParameters parameters r)))))

def radialEncodedE2Kernel : RadialKernel parameters r 3 3 :=
  fullKernelComposition (thirdCoordinateInjectionKernel (radialKernelParameters parameters r))
    (fullKernelComposition (angularMeanFreeKernel (radialKernelParameters parameters r) 1)
      (fullKernelComposition (radialForceKernel parameters L compact state r 1 0)
        (radialGaugeDecodedKernel parameters L compact state r small)))

def radialEncodedPerturbationKernel : RadialKernel parameters r 3 3 :=
  fullKernelAdd (radialEncodedE0Kernel parameters L compact state r small)
    (fullKernelAdd (radialEncodedE1Kernel parameters L compact state r small)
      (radialEncodedE2Kernel parameters L compact state r small))

def radialPreconditionedEncodedKernel : RadialKernel parameters r 3 3 :=
  fullKernelComposition (encodedD0InverseKernel (radialKernelParameters parameters r))
    (radialEncodedPerturbationKernel parameters L compact state r small)

/-- Internal seven-slot normalization is `(x,Rxi/r,xi_zeta,xi/r,F0,RF0,F2)`.
The external AH20 map supplies the two explicit reciprocal-radius factors. -/
def radialKnownQStarKernel : RadialKernel parameters r 7 3 :=
  fullKernelComposition (radialGaugeQKernel parameters L compact state r small)
    (fullKernelComposition (secondCoordinateInjectionKernel (radialKernelParameters parameters r))
      (sevenInputSlotKernel (radialKernelParameters parameters r) 3))

def radialKnownRotatedQStarKernel : RadialKernel parameters r 7 3 :=
  fullKernelComposition (secondCoordinateInjectionKernel (radialKernelParameters parameters r))
    (sevenInputSlotKernel (radialKernelParameters parameters r) 1)

def radialKnownD0Kernel : RadialKernel parameters r 7 3 :=
  fullKernelComposition (firstCoordinateInjectionKernel (radialKernelParameters parameters r))
    (fullKernelSub
      (fullKernelComposition (angularMeanKernel (radialKernelParameters parameters r) 1)
        (sevenInputSlotKernel (radialKernelParameters parameters r) 4))
      (fullKernelComposition (angularMeanKernel (radialKernelParameters parameters r) 1)
        (fullKernelComposition (radialForceKernel parameters L compact state r 0 0)
          (radialKnownQStarKernel parameters L compact state r small))))

def radialKnownD1Kernel : RadialKernel parameters r 7 3 :=
  fullKernelComposition (secondCoordinateInjectionKernel (radialKernelParameters parameters r))
    (fullKernelSub (sevenInputSlotKernel (radialKernelParameters parameters r) 5)
      (fullKernelComposition (angularMeanFreeKernel (radialKernelParameters parameters r) 1)
        (fullKernelAdd
          (fullKernelComposition (radialRotatedForceKernel parameters L compact state r 0 0)
            (radialKnownQStarKernel parameters L compact state r small))
          (fullKernelComposition (radialForceKernel parameters L compact state r 0 0)
            (radialKnownRotatedQStarKernel parameters r)))))

def radialKnownD2Kernel : RadialKernel parameters r 7 3 :=
  fullKernelComposition (thirdCoordinateInjectionKernel (radialKernelParameters parameters r))
    (fullKernelSub
      (fullKernelAdd (sevenInputSlotKernel (radialKernelParameters parameters r) 6)
        (fullKernelSmul (L : ℂ)⁻¹ (sevenInputSlotKernel (radialKernelParameters parameters r) 2)))
      (fullKernelComposition (angularMeanFreeKernel (radialKernelParameters parameters r) 1)
        (fullKernelComposition (radialForceKernel parameters L compact state r 1 0)
          (radialKnownQStarKernel parameters L compact state r small))))

def radialKnownEncodedDataKernel : RadialKernel parameters r 7 3 :=
  fullKernelAdd (radialKnownD0Kernel parameters L compact state r small)
    (fullKernelAdd (radialKnownD1Kernel parameters L compact state r small)
      (radialKnownD2Kernel parameters L compact state r small))

end Grad.AnnularReconstruction
