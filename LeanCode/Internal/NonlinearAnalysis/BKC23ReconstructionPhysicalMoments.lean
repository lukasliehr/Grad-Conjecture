import BKC22FirstInversePhysicalMoments

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.BoundaryKernelAction

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.GaugeCoefficients.Physical.Allocation

theorem actualKnownEncodedDataKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualKnownEncodedDataKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field
        state.gaugeSmall state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualKnownEncodedDataKernel actualKnownEncodedD0Kernel actualKnownEncodedD1Kernel actualKnownEncodedD2Kernel actualKnownQStarKernel actualKnownRotatedQStarKernel
  with_reducible repeat' first
    | exact actualGaugeQKernelOnBall_physicalMoments parameters L compactRadius 
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 1
    | exact actualRotatedForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualEncodedFirstInverseKernel_physicalMoments parameters L compactRadius 
    | exact PhysicalKernelMoments.fixed parameters L compactRadius _
    | apply UniformKernelMoments.add
    | apply UniformKernelMoments.sub
    | apply PhysicalKernelMoments.comp

theorem actualKnownEncodedWKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualKnownEncodedWKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field
        state.firstSmall state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualKnownEncodedWKernel
  with_reducible repeat' first
    | exact actualGaugeQKernelOnBall_physicalMoments parameters L compactRadius 
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 1
    | exact actualRotatedForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualEncodedFirstInverseKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownEncodedDataKernel_physicalMoments parameters L compactRadius 
    | exact PhysicalKernelMoments.fixed parameters L compactRadius _
    | apply UniformKernelMoments.add
    | apply UniformKernelMoments.sub
    | apply PhysicalKernelMoments.comp

theorem actualKnownAStarKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualKnownAStarKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field
        state.firstSmall state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualKnownAStarKernel
  with_reducible repeat' first
    | exact actualGaugeQKernelOnBall_physicalMoments parameters L compactRadius 
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 1
    | exact actualRotatedForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualEncodedFirstInverseKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownEncodedDataKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownEncodedWKernel_physicalMoments parameters L compactRadius 
    | exact PhysicalKernelMoments.fixed parameters L compactRadius _
    | apply UniformKernelMoments.add
    | apply UniformKernelMoments.sub
    | apply PhysicalKernelMoments.comp

theorem actualKnownRAStarKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualKnownRAStarKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field
        state.firstSmall state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualKnownRAStarKernel actualKnownRotatedQStarKernel
  with_reducible repeat' first
    | exact actualGaugeQKernelOnBall_physicalMoments parameters L compactRadius 
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 1
    | exact actualRotatedForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualEncodedFirstInverseKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownEncodedDataKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownEncodedWKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownAStarKernel_physicalMoments parameters L compactRadius 
    | exact PhysicalKernelMoments.fixed parameters L compactRadius _
    | apply UniformKernelMoments.add
    | apply UniformKernelMoments.sub
    | apply PhysicalKernelMoments.comp

theorem actualUnknownNKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualUnknownNKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field
        state.firstSmall state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualUnknownNKernel actualUnknownN0Kernel actualUnknownN1Kernel actualUnknownN2Kernel
  with_reducible repeat' first
    | exact actualGaugeQKernelOnBall_physicalMoments parameters L compactRadius 
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 1
    | exact actualRotatedForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualEncodedFirstInverseKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownEncodedDataKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownEncodedWKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownAStarKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownRAStarKernel_physicalMoments parameters L compactRadius 
    | exact PhysicalKernelMoments.fixed parameters L compactRadius _
    | apply UniformKernelMoments.add
    | apply UniformKernelMoments.sub
    | apply PhysicalKernelMoments.comp
    | apply UniformKernelMoments.neg

theorem actualUnknownWKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualUnknownWKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field
        state.firstSmall state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualUnknownWKernel
  with_reducible repeat' first
    | exact actualGaugeQKernelOnBall_physicalMoments parameters L compactRadius 
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 1
    | exact actualRotatedForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualEncodedFirstInverseKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownEncodedDataKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownEncodedWKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownAStarKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownRAStarKernel_physicalMoments parameters L compactRadius 
    | exact actualUnknownNKernel_physicalMoments parameters L compactRadius 
    | exact PhysicalKernelMoments.fixed parameters L compactRadius _
    | apply UniformKernelMoments.add
    | apply UniformKernelMoments.sub
    | apply PhysicalKernelMoments.comp

theorem actualUnknownUKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualUnknownUKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field
        state.firstSmall state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualUnknownUKernel
  with_reducible repeat' first
    | exact actualGaugeQKernelOnBall_physicalMoments parameters L compactRadius 
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 1
    | exact actualRotatedForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualEncodedFirstInverseKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownEncodedDataKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownEncodedWKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownAStarKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownRAStarKernel_physicalMoments parameters L compactRadius 
    | exact actualUnknownNKernel_physicalMoments parameters L compactRadius 
    | exact actualUnknownWKernel_physicalMoments parameters L compactRadius 
    | exact PhysicalKernelMoments.fixed parameters L compactRadius _
    | apply UniformKernelMoments.add
    | apply UniformKernelMoments.sub
    | apply PhysicalKernelMoments.comp

theorem actualUnknownVKernel_physicalMoments
    (parameters : PhaseParameters) (L compactRadius : ℝ) :
    PhysicalKernelMoments parameters L compactRadius
      (fun state => actualUnknownVKernel parameters L state.rho state.alpha state.delta state.parameter state.epsilon compactRadius state.field
        state.firstSmall state.compactNonnegative state.alphaSmall state.deltaSmall state.parameterSmall) := by
  unfold actualUnknownVKernel
  with_reducible repeat' first
    | exact actualGaugeQKernelOnBall_physicalMoments parameters L compactRadius 
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualForceBoundaryKernel_physicalMoments parameters L compactRadius 1
    | exact actualRotatedForceBoundaryKernel_physicalMoments parameters L compactRadius 0
    | exact actualEncodedFirstInverseKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownEncodedDataKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownEncodedWKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownAStarKernel_physicalMoments parameters L compactRadius 
    | exact actualKnownRAStarKernel_physicalMoments parameters L compactRadius 
    | exact actualUnknownNKernel_physicalMoments parameters L compactRadius 
    | exact actualUnknownWKernel_physicalMoments parameters L compactRadius 
    | exact actualUnknownUKernel_physicalMoments parameters L compactRadius 
    | exact PhysicalKernelMoments.fixed parameters L compactRadius _
    | apply UniformKernelMoments.add
    | apply UniformKernelMoments.sub
    | apply PhysicalKernelMoments.comp

end Grad.BoundaryKernelAction
