import AHW12ScalarFactorsAndCofactorContinuity

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives

/-- Original AD9 r0, including its circular -2e_radial contribution. -/
def radialOriginalForceZeroKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 3 1 :=
  fullKernelAdd (fullKernelSmul (-2) (coordinateProjectionKernel (radialKernelParameters parameters r) 3 0))
    (radialForceKernel parameters L compact state.val.val r 0 0)

/-- Exact AD14/15 finite angular-moment operator. Both P factors remain inside kappa multiplication. -/
def radialKVKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 3 1 :=
  fullKernelSub
    (fullKernelAdd
      (fullKernelAdd (radialCofactorJetRowKernel parameters L compact state 1 0 1 r)
        (fullKernelComposition (radialSignedCofactorComponentKernel parameters L compact state 1 0 r)
          (fullKernelComposition (angularMeanFreeKernel (radialKernelParameters parameters r) 1)
            (radialRetainedForceKernel parameters L compact state.val.val r))))
      (fullKernelComposition (radialSignedCofactorComponentKernel parameters L compact state 1 1 r)
        (radialOriginalForceZeroKernel parameters L compact state r)))
    (fullKernelComposition (radialSignedCofactorComponentKernel parameters L compact state 1 2 r)
      (fullKernelComposition (angularMeanFreeKernel (radialKernelParameters parameters r) 1)
        (radialForceKernel parameters L compact state.val.val r 1 0)))

/-- Exact AH25 on the original normalized seven inputs: c=Q Rb3. -/
def radialNormalizedCKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 7 1 :=
  fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
    (fullKernelAdd
      (fullKernelAdd
        (fullKernelAdd
          (fullKernelComposition (radialCofactorJetRowKernel parameters L compact state 2 0 1 r)
            (radialNormalizedCovariantKernel parameters L compact state.val.val r state.val.property))
          (fullKernelComposition (radialSignedCofactorRowKernel parameters L compact state 2 r)
            (radialNormalizedRotatedCovariantKernel parameters L compact state.val.val r state.val.property)))
        (fullKernelComposition (radialCofactorJetComponentKernel parameters L compact state 1 2 0 1 r)
          (sevenInputSlotKernel (radialKernelParameters parameters r) 3)))
      (fullKernelComposition (radialSignedCofactorComponentKernel parameters L compact state 1 2 r)
        (sevenInputSlotKernel (radialKernelParameters parameters r) 1)))

/-- Exact AH23/ARad5: rV has no inverse-radius coefficient on these normalized inputs. -/
def radialNormalizedRVKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 7 1 :=
  fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
    (fullKernelSub
      (fullKernelSub
        (fullKernelAdd
          (fullKernelComposition (radialSignedCofactorComponentKernel parameters L compact state 1 1 r)
            (sevenInputSlotKernel (radialKernelParameters parameters r) 1))
          (fullKernelComposition (radialKVKernel parameters L compact state r)
            (radialNormalizedCovariantKernel parameters L compact state.val.val r state.val.property)))
        (fullKernelSmul (r.val : ℂ)
          (fullKernelComposition (radialCofactorJetComponentKernel parameters L compact state 1 0 1 0 r)
            (sevenInputSlotKernel (radialKernelParameters parameters r) 3))))
      (fullKernelSmul ((r.val : ℂ) * (L : ℂ)⁻¹)
        (fullKernelComposition (radialCofactorJetComponentKernel parameters L compact state 1 2 0 2 r)
          (sevenInputSlotKernel (radialKernelParameters parameters r) 3))))

def circularNormalizedCKernel (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 7 1 :=
  fullKernelComposition (highAngularKernel parameters 1)
    (fullKernelComposition (fullKernelNeg (coordinateProjectionKernel parameters 3 2))
      (circularNormalizedRotatedCovariantKernel parameters L))

def circularNormalizedRVKernel (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 7 1 :=
  fullKernelComposition (highAngularKernel parameters 1)
    (fullKernelAdd (fullKernelNeg (sevenInputSlotKernel parameters 1))
      (fullKernelComposition (fullKernelSmul 2 (coordinateProjectionKernel parameters 3 0))
        (circularNormalizedCovariantKernel parameters L)))

/-- AI12 after the exact same first-row elimination. -/
def radialEliminatedCKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 8 1 :=
  fullKernelComposition (radialNormalizedCKernel parameters L compact state r)
    (radialEliminatedSevenKernel parameters L compact state r)

def radialEliminatedRVKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 8 1 :=
  fullKernelComposition (radialNormalizedRVKernel parameters L compact state r)
    (radialEliminatedSevenKernel parameters L compact state r)

def circularEliminatedCKernel (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 8 1 :=
  fullKernelComposition (circularNormalizedCKernel parameters L) (circularEliminatedSevenKernel parameters L)

def circularEliminatedRVKernel (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 8 1 :=
  fullKernelComposition (circularNormalizedRVKernel parameters L) (circularEliminatedSevenKernel parameters L)

/-- Canonical BF bulk output order (x,c,rV), paired with (psi_r,psi_zeta/L,Rpsi/r). -/
def radialEliminatedBulkKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 8 3 :=
  fullKernelAdd
    (fullKernelAdd
      (fullKernelComposition (coordinateInjectionKernel (radialKernelParameters parameters r) 3 0)
        (radialEliminatedXKernel parameters L compact state r))
      (fullKernelComposition (coordinateInjectionKernel (radialKernelParameters parameters r) 3 1)
        (radialEliminatedCKernel parameters L compact state r)))
    (fullKernelComposition (coordinateInjectionKernel (radialKernelParameters parameters r) 3 2)
      (radialEliminatedRVKernel parameters L compact state r))

def circularEliminatedBulkKernel (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 8 3 :=
  fullKernelAdd
    (fullKernelAdd (fullKernelComposition (coordinateInjectionKernel parameters 3 0) (circularEliminatedXKernel parameters L))
      (fullKernelComposition (coordinateInjectionKernel parameters 3 1) (circularEliminatedCKernel parameters L)))
    (fullKernelComposition (coordinateInjectionKernel parameters 3 2) (circularEliminatedRVKernel parameters L))

end Grad.AnnularReconstruction
