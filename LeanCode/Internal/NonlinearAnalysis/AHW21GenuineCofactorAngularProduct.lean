import AHW20CompletedEliminatedBulkAction

noncomputable section
set_option maxHeartbeats 1600000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.SourceCollarCoefficients
open Grad.ActualCurrentPrimitives

theorem radialCofactorJetRowKernel_angular_entry (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row : Fin 3) (r : RadialPoint) (shift mode : ℤ × ℤ) :
    (radialCofactorJetRowKernel parameters L compact state row 0 1 r).entry shift mode =
      (Complex.I * (shift.1 : ℂ)) • (radialCofactorJetRowKernel parameters L compact state row 0 0 r).entry shift mode := by
  apply ContinuousLinearMap.ext
  intro value
  simp only [radialCofactorJetRowKernel, radialRowKernel, boundaryRowMultiplicationKernel_entry_apply,
    smul_apply, smul_smul]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro column _
  simp [radialCofactorJetScalar, cofactorJetSequence, cofactorJetMultiplier]
  ring

theorem radialCofactorJetComponentKernel_angular_entry (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row column : Fin 3) (r : RadialPoint) (shift mode : ℤ × ℤ) :
    (radialCofactorJetComponentKernel parameters L compact state row column 0 1 r).entry shift mode =
      (Complex.I * (shift.1 : ℂ)) • (radialCofactorJetComponentKernel parameters L compact state row column 0 0 r).entry shift mode := by
  simp only [radialCofactorJetComponentKernel, radialScalarKernel, boundaryScalarMultiplicationKernel_entry, smul_smul]
  congr 1
  simp [radialCofactorJetScalar, cofactorJetSequence, cofactorJetMultiplier]

theorem zeroShiftKernel_angular_entry {parameters : PhaseParameters} {input output : ℕ}
    (kernel : FullTwoFrequencyKernel parameters input output) (diagonal : ZeroShiftKernel kernel)
    (shift mode : ℤ × ℤ) : (Complex.I * (shift.1 : ℂ)) • kernel.entry shift mode = 0 := by
  by_cases zero : shift = (0, 0)
  · subst shift
    apply ContinuousLinearMap.ext
    intro value
    simp
  · rw [diagonal shift zero mode]
    apply ContinuousLinearMap.ext
    intro value
    simp

theorem radialSignedCofactorRowKernel_angular_entry (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row : Fin 3) (r : RadialPoint) (shift mode : ℤ × ℤ) :
    (radialCofactorJetRowKernel parameters L compact state row 0 1 r).entry shift mode =
      (Complex.I * (shift.1 : ℂ)) • (radialSignedCofactorRowKernel parameters L compact state row r).entry shift mode := by
  have diagonal : ZeroShiftKernel (fullKernelNeg (coordinateProjectionKernel (radialKernelParameters parameters r) 3 row)) :=
    by
      intro displacement nonzero frequency
      simp [coordinateProjectionKernel, constantMatrixKernel_entry, nonzero]
  rw [radialSignedCofactorRowKernel, fullKernelAdd_entry, smul_add,
    zeroShiftKernel_angular_entry _ diagonal, zero_add]
  exact radialCofactorJetRowKernel_angular_entry parameters L compact state row r shift mode

theorem radialSignedCofactorComponentKernel_angular_entry (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row column : Fin 3) (r : RadialPoint) (shift mode : ℤ × ℤ) :
    (radialCofactorJetComponentKernel parameters L compact state row column 0 1 r).entry shift mode =
      (Complex.I * (shift.1 : ℂ)) • (radialSignedCofactorComponentKernel parameters L compact state row column r).entry shift mode := by
  have diagonal : ZeroShiftKernel (circularCofactorComponentKernel (radialKernelParameters parameters r) row column) := by
    unfold circularCofactorComponentKernel
    split_ifs
    · exact (zeroShift_identity _ _).neg
    · intro shift nonzero mode
      rfl
  rw [radialSignedCofactorComponentKernel, fullKernelAdd_entry, smul_add,
    zeroShiftKernel_angular_entry _ diagonal, zero_add]
  exact radialCofactorJetComponentKernel_angular_entry parameters L compact state row column r shift mode

theorem radialSignedCofactorRowKernel_derivative (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row : Fin 3) (r : RadialPoint) (angular cell : ℕ)
    (field derivative : NegativeTrace (radialKernelParameters parameters r) angular cell 3)
    (differentiated : IsAngularDerivative (radialKernelParameters parameters r) angular cell field derivative) :
    IsAngularDerivative (radialKernelParameters parameters r) angular cell
      (fullNegativeKernelAction _ angular cell (radialSignedCofactorRowKernel parameters L compact state row r) field)
      (fullNegativeKernelAction _ angular cell (radialCofactorJetRowKernel parameters L compact state row 0 1 r) field +
        fullNegativeKernelAction _ angular cell (radialSignedCofactorRowKernel parameters L compact state row r) derivative) :=
  fullNegativeKernelAction_derivative _ angular cell _ _
    (radialSignedCofactorRowKernel_angular_entry parameters L compact state row r) field derivative differentiated

theorem radialSignedCofactorComponentKernel_derivative (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row column : Fin 3) (r : RadialPoint) (angular cell : ℕ)
    (field derivative : NegativeTrace (radialKernelParameters parameters r) angular cell 1)
    (differentiated : IsAngularDerivative (radialKernelParameters parameters r) angular cell field derivative) :
    IsAngularDerivative (radialKernelParameters parameters r) angular cell
      (fullNegativeKernelAction _ angular cell (radialSignedCofactorComponentKernel parameters L compact state row column r) field)
      (fullNegativeKernelAction _ angular cell (radialCofactorJetComponentKernel parameters L compact state row column 0 1 r) field +
        fullNegativeKernelAction _ angular cell (radialSignedCofactorComponentKernel parameters L compact state row column r) derivative) :=
  fullNegativeKernelAction_derivative _ angular cell _ _
    (radialSignedCofactorComponentKernel_angular_entry parameters L compact state row column r) field derivative differentiated

end Grad.AnnularReconstruction
