import AHW2RetainedReferenceAlgebra

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse
open Grad.GaugeCoefficients.Physical.Ledger

/-- Shared physical order: (xi_r,Rxi/r,xi_zeta,xi/r,F0,RF0,F2,f).
The first coordinate is eliminated x's radial-equation datum, not x itself. -/
def eightInputSlotKernel (parameters : PhaseParameters) (slot : Fin 8) : FullTwoFrequencyKernel parameters 8 1 :=
  coordinateProjectionKernel parameters 8 slot

/-- The known six entries keep their literal original normalized positions. -/
def knownEightToSevenMap : ComplexEuclidean 8 →L[ℂ] ComplexEuclidean 7 :=
  matrixUnit 1 1 + matrixUnit 2 2 + matrixUnit 3 3 + matrixUnit 4 4 + matrixUnit 5 5 + matrixUnit 6 6

def knownEightToSevenKernel (parameters : PhaseParameters) : FullTwoFrequencyKernel parameters 8 7 :=
  constantMatrixKernel parameters 8 7 knownEightToSevenMap

theorem knownEightToSevenMap_apply (input : ComplexEuclidean 8) (component : Fin 7) :
    knownEightToSevenMap input component = if component = 0 then 0 else input component.castSucc := by
  fin_cases component <;> simp [knownEightToSevenMap, matrixUnit_apply, operatorBasis]

/-- Q(xi_r-Jz-Ss-f), with J and S from the actual same seven-slot reconstruction. -/
def radialEliminationRightHandKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 8 1 :=
  fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
    (fullKernelSub
      (fullKernelSub (eightInputSlotKernel (radialKernelParameters parameters r) 0)
        (fullKernelComposition (radialNormalizedRetainedFirstRowKernel parameters L compact state.val r)
          (knownEightToSevenKernel (radialKernelParameters parameters r))))
      (eightInputSlotKernel (radialKernelParameters parameters r) 7))

def circularEliminationRightHandKernel (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 8 1 :=
  fullKernelComposition (highAngularKernel parameters 1)
    (fullKernelSub
      (fullKernelSub (eightInputSlotKernel parameters 0)
        (fullKernelComposition (circularRetainedFirstRowKernel parameters L) (knownEightToSevenKernel parameters)))
      (eightInputSlotKernel parameters 7))

/-- AI8's same actual inverse, now acting on the eight explicit normalized inputs. -/
def radialEliminatedXKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 8 1 :=
  fullKernelComposition (radialRetainedHighInverse parameters L compact state r)
    (radialEliminationRightHandKernel parameters L compact state r)

def circularEliminatedXKernel (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 8 1 :=
  fullKernelComposition (fullKernelNeg (retainedBInverseKernel parameters))
    (circularEliminationRightHandKernel parameters L)

/-- Canonical output order: (x,Rxi/r,xi_zeta,xi/r,F0,RF0,F2). -/
def radialEliminatedSevenKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) : RadialKernel parameters r 8 7 :=
  fullKernelAdd
    (fullKernelComposition (coordinateInjectionKernel (radialKernelParameters parameters r) 7 0)
      (radialEliminatedXKernel parameters L compact state r))
    (knownEightToSevenKernel (radialKernelParameters parameters r))

def circularEliminatedSevenKernel (parameters : PhaseParameters) (L : ℝ) : FullTwoFrequencyKernel parameters 8 7 :=
  fullKernelAdd (fullKernelComposition (coordinateInjectionKernel parameters 7 0) (circularEliminatedXKernel parameters L))
    (knownEightToSevenKernel parameters)

theorem radialNormalizedRetainedFirstRowKernel_high_left (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (r : RadialPoint) :
    fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
      (radialNormalizedRetainedFirstRowKernel parameters L compact state r) =
      radialNormalizedRetainedFirstRowKernel parameters L compact state r := by
  unfold radialNormalizedRetainedFirstRowKernel
  rw [← fullKernelComposition_assoc, highAngularKernel_idempotent]

theorem radialEliminationRightHandKernel_high_left (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
    fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
      (radialEliminationRightHandKernel parameters L compact state r) =
      radialEliminationRightHandKernel parameters L compact state r := by
  unfold radialEliminationRightHandKernel
  rw [← fullKernelComposition_assoc, highAngularKernel_idempotent]

theorem radialEliminatedXKernel_high_left (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
    fullKernelComposition (highAngularKernel (radialKernelParameters parameters r) 1)
      (radialEliminatedXKernel parameters L compact state r) =
      radialEliminatedXKernel parameters L compact state r := by
  unfold radialEliminatedXKernel
  rw [← fullKernelComposition_assoc, radialRetainedHighInverse_high_left]

/-- The same actual eliminated x solves the first high row on the whole ambient eight-slot input. -/
theorem radialEliminatedXKernel_solves (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) :
    fullKernelComposition (radialRetainedHighAKernel parameters L compact state.val r)
      (radialEliminatedXKernel parameters L compact state r) =
      radialEliminationRightHandKernel parameters L compact state r := by
  unfold radialEliminatedXKernel
  rw [← fullKernelComposition_assoc, radialRetainedHighInverse_right, radialEliminationRightHandKernel_high_left]

end Grad.AnnularReconstruction
