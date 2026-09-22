import AHP28RadialSigmaPhysicalMoments

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

theorem radialFixedFirstMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => (firstCoordinateInjectionKernel) (radialKernelParameters parameters r)) :=
  RadialPhysicalMoments.fixed parameters L compact (firstCoordinateInjectionKernel) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)

theorem radialFixedSecondMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => (secondCoordinateInjectionKernel) (radialKernelParameters parameters r)) :=
  RadialPhysicalMoments.fixed parameters L compact (secondCoordinateInjectionKernel) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)

theorem radialFixedThirdMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => (thirdCoordinateInjectionKernel) (radialKernelParameters parameters r)) :=
  RadialPhysicalMoments.fixed parameters L compact (thirdCoordinateInjectionKernel) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)

theorem radialFixedJMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => (encodedJKernel) (radialKernelParameters parameters r)) :=
  RadialPhysicalMoments.fixed parameters L compact (encodedJKernel) (fun _ _ => sameEncodedJKernel _ _)

theorem radialFixedRJMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => (encodedRotationKernel) (radialKernelParameters parameters r)) :=
  RadialPhysicalMoments.fixed parameters L compact (encodedRotationKernel) (fun _ _ => sameEncodedRotationKernel _ _)

theorem radialFixedQAMoments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => (actualUnknownQAKernel) (radialKernelParameters parameters r)) :=
  RadialPhysicalMoments.fixed parameters L compact (actualUnknownQAKernel) (fun _ _ => sameUnknownQAKernel _ _)

theorem radialFixedD0Moments (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => (encodedD0InverseKernel) (radialKernelParameters parameters r)) :=
  RadialPhysicalMoments.fixed parameters L compact (encodedD0InverseKernel) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)

theorem radialFixedMeanMoments (parameters : PhaseParameters) (L compact : ℝ) (dimension : Nat) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => (fun p => angularMeanKernel p dimension) (radialKernelParameters parameters r)) :=
  RadialPhysicalMoments.fixed parameters L compact (fun p => angularMeanKernel p dimension) (fun _ _ => sameScalarModeDiagonalKernel _ _ _ _ _ _)

theorem radialFixedMeanFreeMoments (parameters : PhaseParameters) (L compact : ℝ) (dimension : Nat) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => (fun p => angularMeanFreeKernel p dimension) (radialKernelParameters parameters r)) :=
  RadialPhysicalMoments.fixed parameters L compact (fun p => angularMeanFreeKernel p dimension) (fun _ _ => sameScalarModeDiagonalKernel _ _ _ _ _ _)

theorem radialFixedSlotMoments (parameters : PhaseParameters) (L compact : ℝ) (slot : Fin 7) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => (fun p => sevenInputSlotKernel p slot) (radialKernelParameters parameters r)) :=
  RadialPhysicalMoments.fixed parameters L compact (fun p => sevenInputSlotKernel p slot) (fun _ _ => sameConstantMatrixKernel _ _ _ _ _)

theorem radialFixedTwiceMoments (parameters : PhaseParameters) (L compact : ℝ) (dimension : Nat) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => (fun p => fullKernelSmul 2 (fullIdentityKernel p dimension)) (radialKernelParameters parameters r)) :=
  RadialPhysicalMoments.fixed parameters L compact (fun p => fullKernelSmul 2 (fullIdentityKernel p dimension)) (fun _ _ => (sameFullIdentityKernel _ _ _).smul _)

theorem radialFixedScaledSlotMoments (parameters : PhaseParameters) (L compact : ℝ) (slot : Fin 7) :
    RadialPhysicalMoments parameters L compact
      (fun _ r => (fun p => fullKernelSmul (L : ℂ)⁻¹ (sevenInputSlotKernel p slot)) (radialKernelParameters parameters r)) :=
  RadialPhysicalMoments.fixed parameters L compact (fun p => fullKernelSmul (L : ℂ)⁻¹ (sevenInputSlotKernel p slot)) (fun _ _ => (sameConstantMatrixKernel _ _ _ _ _).smul _)

theorem radialEncodedPerturbationKernel_physicalMoments
    (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialEncodedPerturbationKernel parameters L compact state.val r state.gaugeSmall) := by
  unfold radialEncodedPerturbationKernel radialEncodedE0Kernel radialEncodedE1Kernel
    radialEncodedE2Kernel radialGaugeDecodedKernel
  with_reducible repeat' first
    | exact radialGaugeQKernel_physicalMoments parameters L compact
    | exact radialForceKernel_physicalMoments parameters L compact 0
    | exact radialForceKernel_physicalMoments parameters L compact 1
    | exact radialRotatedForceKernel_physicalMoments parameters L compact 0
    | exact radialFixedFirstMoments parameters L compact
    | exact radialFixedSecondMoments parameters L compact
    | exact radialFixedThirdMoments parameters L compact
    | exact radialFixedJMoments parameters L compact
    | exact radialFixedRJMoments parameters L compact
    | exact radialFixedQAMoments parameters L compact
    | exact radialFixedD0Moments parameters L compact
    | exact radialFixedMeanMoments parameters L compact _
    | exact radialFixedMeanFreeMoments parameters L compact _
    | exact radialFixedSlotMoments parameters L compact _
    | exact radialFixedTwiceMoments parameters L compact _
    | exact radialFixedScaledSlotMoments parameters L compact _
    | apply UniformRadialKernelMoments.add
    | apply RadialPhysicalMoments.comp

theorem radialPreconditionedEncodedKernel_physicalMoments
    (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialPreconditionedEncodedKernel parameters L compact state.val r state.gaugeSmall) := by
  unfold radialPreconditionedEncodedKernel
  apply RadialPhysicalMoments.comp
  · exact radialFixedD0Moments parameters L compact
  · exact radialEncodedPerturbationKernel_physicalMoments parameters L compact

theorem radialEncodedIdentityInverseKernel_physicalMoments
    (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialEncodedIdentityInverseKernel parameters L compact state.val r state.firstSmall) := by
  unfold radialEncodedIdentityInverseKernel
  apply UniformRadialKernelMoments.neg
  apply UniformRadialKernelMoments.negativeIdentityInverse (fun state => state.val.one_le_size)
  exact (radialPreconditionedEncodedKernel_physicalMoments parameters L compact).neg

theorem radialEncodedFirstInverseKernel_physicalMoments
    (parameters : PhaseParameters) (L compact : ℝ) :
    RadialPhysicalMoments parameters L compact
      (fun state r => radialEncodedFirstInverseKernel parameters L compact state.val r state.firstSmall) := by
  unfold radialEncodedFirstInverseKernel
  apply RadialPhysicalMoments.comp
  · exact radialEncodedIdentityInverseKernel_physicalMoments parameters L compact
  · exact radialFixedD0Moments parameters L compact

end Grad.AnnularReconstruction
