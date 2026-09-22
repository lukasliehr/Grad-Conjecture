import BCI5ExactKnownSlotIndependence

noncomputable section
set_option maxHeartbeats 1200000
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

namespace Grad.ActualBoundaryPrimitives.PhysicalBoundaryState
open Grad.ActualBoundaryInverse
variable {parameters : PhaseParameters} {L compact : ℝ}
abbrev budget (state : PhysicalBoundaryState parameters L compact) (moment : ℕ) : ℝ :=
  physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment + 7)
abbrev deltaRow (state : PhysicalBoundaryState parameters L compact) :=
  boundaryDeviationMultiplier parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall
    state.val.parameterSmall state.coefficientSmall
abbrev rotatedDeltaRow (state : PhysicalBoundaryState parameters L compact) :=
  boundaryRotatedDeviationMultiplier parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.compactNonnegative state.val.alphaSmall state.val.deltaSmall
    state.val.parameterSmall state.coefficientSmall
abbrev unknownU (state : PhysicalBoundaryState parameters L compact) :=
  actualUnknownUKernel parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.firstSmall state.val.compactNonnegative state.val.alphaSmall
    state.val.deltaSmall state.val.parameterSmall
abbrev unknownV (state : PhysicalBoundaryState parameters L compact) :=
  actualUnknownVKernel parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.firstSmall state.val.compactNonnegative state.val.alphaSmall
    state.val.deltaSmall state.val.parameterSmall
abbrev knownA (state : PhysicalBoundaryState parameters L compact) :=
  actualKnownAStarKernel parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.firstSmall state.val.compactNonnegative state.val.alphaSmall
    state.val.deltaSmall state.val.parameterSmall
abbrev knownRA (state : PhysicalBoundaryState parameters L compact) :=
  actualKnownRAStarKernel parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.firstSmall state.val.compactNonnegative state.val.alphaSmall
    state.val.deltaSmall state.val.parameterSmall
abbrev knownJ (state : PhysicalBoundaryState parameters L compact) :=
  actualKnownJStarKernel parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.firstSmall state.val.compactNonnegative state.val.alphaSmall
    state.val.deltaSmall state.val.parameterSmall
abbrev massPerturbation (state : PhysicalBoundaryState parameters L compact) :=
  actualMassPerturbationKernel parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.firstSmall state.val.compactNonnegative state.val.alphaSmall
    state.val.deltaSmall state.val.parameterSmall
abbrev massInverse (state : PhysicalBoundaryState parameters L compact) :=
  actualMassInverseKernel parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.small state.val.compactNonnegative state.val.alphaSmall
    state.val.deltaSmall state.val.parameterSmall
abbrev covariant (state : PhysicalBoundaryState parameters L compact) :=
  actualCovariantKernel parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.small state.val.compactNonnegative state.val.alphaSmall
    state.val.deltaSmall state.val.parameterSmall
abbrev rotatedCovariant (state : PhysicalBoundaryState parameters L compact) :=
  actualRotatedCovariantKernel parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.val.small state.val.compactNonnegative state.val.alphaSmall
    state.val.deltaSmall state.val.parameterSmall
abbrev physicalRow (state : PhysicalBoundaryState parameters L compact) :=
  actualDifferentiatedPhysicalBoundaryKernel parameters L state.val.rho state.val.alpha state.val.delta state.val.parameter
    state.val.epsilon compact state.val.field state.property state.val.compactNonnegative state.val.alphaSmall
    state.val.deltaSmall state.val.parameterSmall

/-- The two literal boundary-covector deviations acting on the unknown reconstruction. -/
def rowCorrection (state : PhysicalBoundaryState parameters L compact) :=
  fullKernelAdd (fullKernelComposition state.rotatedDeltaRow state.unknownU)
    (fullKernelComposition state.deltaRow state.unknownV)

/-- AI9's actual x block, by the stipulated high-slot insertion. -/
def boundaryT (state : PhysicalBoundaryState parameters L compact) :=
  fullKernelComposition state.physicalRow
    (fullKernelComposition (coordinateInjectionKernel parameters 7 0) (highAngularKernel parameters 1))

/-- This ordered expression vanishes at the reference. Both exterior high
projections are fixed and retain every axial Fourier cell. -/
def boundaryE (state : PhysicalBoundaryState parameters L compact) :=
  fullKernelComposition (highAngularKernel parameters 1)
    (fullKernelComposition
      (fullKernelComposition (fullKernelAdd state.massPerturbation state.rowCorrection) state.massInverse)
      (highAngularKernel parameters 1))
end Grad.ActualBoundaryPrimitives.PhysicalBoundaryState
