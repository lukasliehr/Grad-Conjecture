import AKDH1ActualPolarRowEulerAssembly

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives Grad.GaugeCoefficients.Physical.Allocation

def actualCofactorRawScalar (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (row column : Fin 3)
    (radial : Fin 2) (direction : Fin 3) (raw : ℕ) (point : ℝ) : (ℤ × ℤ) → ℂ :=
  cofactorJetSequence direction (polarEntryScalar parameters
    (originalCofactorDeviation parameters L state.val.epsilon state.val.field)
    (originalCofactorDeviation_coherent parameters L state.val.rho state.val.epsilon state.val.field state.val.low)
    row column (radial.val+raw) point)

theorem actualCofactorRawScalar_derivative (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (row column : Fin 3)
    (radial : Fin 2) (direction : Fin 3) (raw : ℕ) (point : ℝ) (shift : ℤ × ℤ) :
    HasDerivAt (fun radius => actualCofactorRawScalar parameters L compact state row column radial direction raw radius shift)
      (actualCofactorRawScalar parameters L compact state row column radial direction (raw+1) point shift) point := by
  have derivative := (polarEntryScalar_hasDerivAt parameters
    (originalCofactorDeviation parameters L state.val.epsilon state.val.field)
    (originalCofactorDeviation_coherent parameters L state.val.rho state.val.epsilon state.val.field state.val.low)
    row column (radial.val+raw) point shift).const_mul (cofactorJetMultiplier direction shift)
  rw [Nat.add_assoc] at derivative
  exact derivative

theorem actualCofactorRawScalar_summable (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (row column : Fin 3)
    (radial : Fin 2) (direction : Fin 3) (raw : ℕ) (radius : RadialPoint) (moment : ℕ) :
    Summable (productMoment parameters moment radius.val
      (actualCofactorRawScalar parameters L compact state row column radial direction raw radius.val)) :=
  cofactorJetSequence_moment_summable parameters moment radius.val direction _
    (polarEntryScalarMoment_summable parameters _ _ row column (moment+1) (radial.val+raw) radius.val radius.property.1 radius.property.2)

theorem actualCofactorRawScalar_bound (parameters : PhaseParameters) (L compact : ℝ)
    (state : AnnularReconstructionState parameters L compact) (row column : Fin 3)
    (radial : Fin 2) (direction : Fin 3) (raw : ℕ) (radius : RadialPoint) (moment : ℕ) :
    (∑' shift, productMoment parameters moment radius.val
      (actualCofactorRawScalar parameters L compact state row column radial direction raw radius.val) shift) ≤
      physicalPolarEntryConstant (originalCofactorProfile parameters L).deviation row column (moment+1) (radial.val+raw) *
        physicalBudget parameters state.val.field state.val.rho state.val.epsilon (moment+raw+7) := by
  have summable := polarEntryScalarMoment_summable parameters
    (originalCofactorDeviation parameters L state.val.epsilon state.val.field)
    (originalCofactorDeviation_coherent parameters L state.val.rho state.val.epsilon state.val.field state.val.low)
    row column (moment+1) (radial.val+raw) radius.val radius.property.1 radius.property.2
  apply ((actualCofactorRawScalar_summable parameters L compact state row column radial direction raw radius moment).tsum_le_tsum
    (cofactorJetSequence_moment_le parameters moment radius.val direction _) summable).trans
  apply (physicalPolarEntryScalarMoment_bound parameters _ _ state.val.field state.val.rho state.val.epsilon
    (originalCofactorProfile parameters L).deviation
    (originalCofactorDeviation_bound parameters L state.val.rho state.val.epsilon state.val.field state.val.low)
    row column (moment+1) (radial.val+raw) radius.val radius.property.1 radius.property.2).trans
  exact mul_le_mul_of_nonneg_left (physicalBudget_monotone parameters state.val.field state.val.rho state.val.epsilon
    (by have := radial.isLt; omega)) (physicalPolarEntryConstant_nonnegative _ _ _ _ _)

def actualCofactorRowEulerFamily (parameters : PhaseParameters) (L compact : ℝ)
    (row : Fin 3) (radial : Fin 2) (direction : Fin 3) :=
  rowPrimitiveEulerFamily parameters L compact
    (fun state raw point column => actualCofactorRawScalar parameters L compact state row column radial direction raw point)
    (fun state raw point column shift => actualCofactorRawScalar_derivative parameters L compact state row column radial direction raw point shift)
    (fun state raw radius column moment => actualCofactorRawScalar_summable parameters L compact state row column radial direction raw radius moment)
    7 (by omega)
    (fun column raw moment => physicalPolarEntryConstant (originalCofactorProfile parameters L).deviation row column (moment+1) (radial.val+raw))
    (fun _ _ _ => physicalPolarEntryConstant_nonnegative _ _ _ _ _)
    (fun state raw radius column moment => actualCofactorRawScalar_bound parameters L compact state row column radial direction raw radius moment)

def actualCofactorComponentEulerFamily (parameters : PhaseParameters) (L compact : ℝ)
    (row column : Fin 3) (radial : Fin 2) (direction : Fin 3) :=
  scalarPrimitiveEulerFamily parameters L compact
    (fun state raw point => actualCofactorRawScalar parameters L compact state row column radial direction raw point)
    (fun state raw point shift => actualCofactorRawScalar_derivative parameters L compact state row column radial direction raw point shift)
    (fun state raw radius moment => actualCofactorRawScalar_summable parameters L compact state row column radial direction raw radius moment)
    7 (by omega)
    (fun raw moment => physicalPolarEntryConstant (originalCofactorProfile parameters L).deviation row column (moment+1) (radial.val+raw))
    (fun _ _ => physicalPolarEntryConstant_nonnegative _ _ _ _ _)
    (fun state raw radius moment => actualCofactorRawScalar_bound parameters L compact state row column radial direction raw radius moment)

theorem actualCofactorRowEulerFamily_same (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row : Fin 3) (radial : Fin 2) (direction : Fin 3) (radius : RadialPoint) :
    (actualCofactorRowEulerFamily parameters L compact row radial direction).kernels state.val 0 radius =
      radialCofactorJetRowKernel parameters L compact state row radial direction radius := rfl

theorem actualCofactorComponentEulerFamily_same (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row column : Fin 3) (radial : Fin 2) (direction : Fin 3) (radius : RadialPoint) :
    (actualCofactorComponentEulerFamily parameters L compact row column radial direction).kernels state.val 0 radius =
      radialCofactorJetComponentKernel parameters L compact state row column radial direction radius := rfl

end Grad.OriginalCartesianTameEstimate
