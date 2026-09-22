import AHW10ActualCofactorJetCoefficients

noncomputable section
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.SourceCollarCoefficients Grad.ActualCurrentPrimitives Grad.ActualGaugeSigmaPrimitives
open Grad.ActualBoundaryPrimitives Grad.AnnularKernelContinuity
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.SourceCollar Grad.BoundaryTrace

/-- Literal physical signed cofactor row, in the original polar frame. -/
def originalSignedCofactorRow (parameters : PhaseParameters) (L epsilon : ℝ) (field : ACore parameters 3)
    (row : Fin 3) (axialAngle polarAngle : ℝ) (point : ClosedDisk) (column : Fin 3) : ℂ :=
  polarMatrixEntry row column polarAngle (originalPhysicalSignedCofactor parameters L epsilon field axialAngle point)

theorem radialCofactorJetScalar_physical (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row column : Fin 3) (r : RadialPoint) (mode : ℤ × ℤ) :
    angularCoefficient (fun angle => angularCoefficient (fun axialAngle =>
      originalSignedCofactorRow parameters L state.val.val.epsilon state.val.val.field row axialAngle angle
        (polarClosedPoint r.val angle r.property.1 r.property.2) column +
        if row = column then 1 else 0) mode.2) mode.1 =
      radialCofactorJetScalar parameters L compact state row column 0 0 r mode := by
  have exactCoefficient := polarEntry_doubleCoefficient parameters
    (originalCofactorDeviation parameters L state.val.val.epsilon state.val.val.field)
    (originalCofactorDeviation_coherent parameters L state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low)
    row column r.val r.property.1 r.property.2 mode
  simp_rw [originalCofactorDeviation_matrix parameters L state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low,
    polarMatrixEntry_add, polarMatrixEntry_one] at exactCoefficient
  simpa [radialCofactorJetScalar, cofactorJetSequence, cofactorJetMultiplier, originalSignedCofactorRow, polarEntryScalar] using exactCoefficient

def radialCofactorJetRowKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row : Fin 3) (radial : Fin 2) (direction : Fin 3)
    (r : RadialPoint) : RadialKernel parameters r 3 1 :=
  radialRowKernel parameters r 3 (fun column => radialCofactorJetScalar parameters L compact state row column radial direction r)
    (fun column moment => radialCofactorJetScalar_moments parameters L compact state row column radial direction r moment)

def radialCofactorJetComponentKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row column : Fin 3) (radial : Fin 2) (direction : Fin 3)
    (r : RadialPoint) : RadialKernel parameters r 1 1 :=
  radialScalarKernel parameters r 1 (radialCofactorJetScalar parameters L compact state row column radial direction r)
    (radialCofactorJetScalar_moments parameters L compact state row column radial direction r)

theorem radialCofactorJetRowKernel_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ)
    (row : Fin 3) (radial : Fin 2) (direction : Fin 3) :
    RetainedDeviationMoments parameters L compact (fun state r => radialCofactorJetRowKernel parameters L compact state row radial direction r) := by
  intro moment
  let constant := Real.exp (parameters.sigma0 + 2 * parameters.gamma) *
    ∑ column : Fin 3, cofactorJetConstant parameters L row column radial moment
  refine ⟨constant, mul_nonneg (Real.exp_pos _).le
    (Finset.sum_nonneg fun column _ => cofactorJetConstant_nonnegative parameters L row column radial moment), ?_⟩
  intro state r
  apply (radialRowKernel_moment_le parameters r 3 moment _ _).trans
  have summed := Finset.sum_le_sum (s := Finset.univ) fun column _ =>
    radialCofactorJetScalar_moment_bound parameters L compact state row column radial direction r moment
  exact (mul_le_mul_of_nonneg_left summed (Real.exp_pos _).le).trans_eq (by
    dsimp only [constant]
    rw [← Finset.sum_mul]
    ring)

theorem radialCofactorJetComponentKernel_vanishingMoments (parameters : PhaseParameters) (L compact : ℝ)
    (row column : Fin 3) (radial : Fin 2) (direction : Fin 3) :
    RetainedDeviationMoments parameters L compact
      (fun state r => radialCofactorJetComponentKernel parameters L compact state row column radial direction r) := by
  intro moment
  refine ⟨Real.exp (parameters.sigma0 + 2 * parameters.gamma) * cofactorJetConstant parameters L row column radial moment,
    mul_nonneg (Real.exp_pos _).le (cofactorJetConstant_nonnegative parameters L row column radial moment), ?_⟩
  intro state r
  apply (radialScalarKernel_moment_le parameters r 1 moment _ _).trans
  exact (mul_le_mul_of_nonneg_left
    (radialCofactorJetScalar_moment_bound parameters L compact state row column radial direction r moment)
    (Real.exp_pos _).le).trans_eq (mul_assoc _ _ _).symm

def radialSignedCofactorRowKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row : Fin 3) (r : RadialPoint) : RadialKernel parameters r 3 1 :=
  fullKernelAdd (fullKernelNeg (coordinateProjectionKernel (radialKernelParameters parameters r) 3 row))
    (radialCofactorJetRowKernel parameters L compact state row 0 0 r)

def circularCofactorComponentKernel (parameters : PhaseParameters) (row column : Fin 3) : FullTwoFrequencyKernel parameters 1 1 :=
  if row = column then fullKernelNeg (fullIdentityKernel parameters 1) else fullZeroKernel parameters 1 1

def radialSignedCofactorComponentKernel (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row column : Fin 3) (r : RadialPoint) : RadialKernel parameters r 1 1 :=
  fullKernelAdd (circularCofactorComponentKernel (radialKernelParameters parameters r) row column)
    (radialCofactorJetComponentKernel parameters L compact state row column 0 0 r)

theorem radialSignedCofactorRowKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) (row : Fin 3) :
    RetainedReferenceDifference parameters L compact (fun state r => radialSignedCofactorRowKernel parameters L compact state row r)
      (fun _ r => fullKernelNeg (coordinateProjectionKernel (radialKernelParameters parameters r) 3 row)) :=
  RetainedReferenceDifference.add_right _ (radialCofactorJetRowKernel_vanishingMoments parameters L compact row 0 0)

theorem radialSignedCofactorComponentKernel_referenceDifference (parameters : PhaseParameters) (L compact : ℝ) (row column : Fin 3) :
    RetainedReferenceDifference parameters L compact (fun state r => radialSignedCofactorComponentKernel parameters L compact state row column r)
      (fun _ r => circularCofactorComponentKernel (radialKernelParameters parameters r) row column) :=
  RetainedReferenceDifference.add_right _ (radialCofactorJetComponentKernel_vanishingMoments parameters L compact row column 0 0)

theorem sameCircularCofactorComponentKernel (first second : PhaseParameters) (row column : Fin 3) :
    SameKernelEntries (circularCofactorComponentKernel first row column) (circularCofactorComponentKernel second row column) := by
  unfold circularCofactorComponentKernel
  split_ifs
  · exact (sameFullIdentityKernel _ _ _).neg
  · intro shift mode
    rfl

theorem radialSignedCofactorRowKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) (row : Fin 3) :
    RetainedPhysicalMoments parameters L compact (fun state r => radialSignedCofactorRowKernel parameters L compact state row r) :=
  (radialSignedCofactorRowKernel_referenceDifference parameters L compact row).actual_regular
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => (sameConstantMatrixKernel _ _ _ _ _).neg))

theorem radialSignedCofactorComponentKernel_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) (row column : Fin 3) :
    RetainedPhysicalMoments parameters L compact (fun state r => radialSignedCofactorComponentKernel parameters L compact state row column r) :=
  (radialSignedCofactorComponentKernel_referenceDifference parameters L compact row column).actual_regular
    (RetainedPhysicalMoments.fixed parameters L compact _ (fun _ _ => sameCircularCofactorComponentKernel _ _ row column))

end Grad.AnnularReconstruction
