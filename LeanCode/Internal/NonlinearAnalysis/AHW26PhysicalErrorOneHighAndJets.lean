import AHW25LiteralEliminatedCircularFlux

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

/-- The evaluated eliminated bulk error allocates exactly B8 to the high input
and B_(grade+8) to the low input, uniformly in radius. -/
theorem eliminatedBulkError_oneHigh_bound
    {parameters : PhaseParameters} {L compact : ℝ}
     (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : RetainedInverseState parameters L compact) (r : RadialPoint) (high : NegativeTotalTrace (radialKernelParameters parameters r) grade 8)
        (low : NegativeTotalTrace (radialKernelParameters parameters r) 0 8),
        ‖fullOneHighKernelAction (radialKernelParameters parameters r) grade (fullKernelSub (radialEliminatedBulkKernel parameters L compact state r)
          (circularEliminatedBulkKernel (radialKernelParameters parameters r) L)) high low‖ ≤
          constant * (state.val.errorBudget 1 * ‖high‖ + state.val.errorBudget (grade + 1) * ‖low‖) := by
  obtain ⟨lowConstant, lowNonnegative, lowBound⟩ := radialEliminatedBulkKernel_referenceDifference parameters L compact 1
  obtain ⟨highConstant, highNonnegative, highBound⟩ := radialEliminatedBulkKernel_referenceDifference parameters L compact (grade + 1)
  refine ⟨2 ^ grade * (lowConstant + highConstant), by positivity, ?_⟩
  intro state r high low
  have lowSizeNonnegative := physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8
  have highSizeNonnegative := physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon ((grade + 1) + 7)
  apply (fullOneHighKernelAction_bound (radialKernelParameters parameters r) grade (fullKernelSub (radialEliminatedBulkKernel parameters L compact state r)
          (circularEliminatedBulkKernel (radialKernelParameters parameters r) L)) high low).trans
  calc
    _ ≤ 2 ^ grade *
      ((lowConstant * state.val.errorBudget 1) * ‖high‖ +
        (highConstant * state.val.errorBudget (grade + 1)) * ‖low‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact add_le_add
        (mul_le_mul_of_nonneg_right (lowBound state r) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (highBound state r) (norm_nonneg _))
    _ ≤ 2 ^ grade *
      (((lowConstant + highConstant) * state.val.errorBudget 1) * ‖high‖ +
        ((lowConstant + highConstant) * state.val.errorBudget (grade + 1)) * ‖low‖) := by
      gcongr <;> linarith
    _ = _ := by ring


/-- Compatible representatives yield the actual eliminated-bulk-minus-circular Fourier action. -/
theorem eliminatedBulkError_oneHigh_physical
    (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (r : RadialPoint) (grade : ℕ)
    (high : NegativeTotalTrace (radialKernelParameters parameters r) grade 8)
    (low : NegativeTotalTrace (radialKernelParameters parameters r) 0 8)
    (compatible : TotalTraceCompatible (radialKernelParameters parameters r) grade high low)
    (mode : ℤ × ℤ) :
    let error := fullKernelSub (radialEliminatedBulkKernel parameters L compact state r)
      (circularEliminatedBulkKernel (radialKernelParameters parameters r) L)
    HasSum (fun shift => error.entry shift (twoFrequencyTranslation shift mode)
      (negativeTotalCoefficient (radialKernelParameters parameters r) grade high
        (twoFrequencyTranslation shift mode)))
      (negativeTotalCoefficient (radialKernelParameters parameters r) grade
        (fullOneHighKernelAction (radialKernelParameters parameters r) grade error high low) mode) :=
  fullOneHighKernelAction_coefficient_hasSum _ _ _ _ _ compatible _

open Grad.ActualGaugeSigmaPrimitives Grad.ActualCurrentPrimitives Grad.SourceCollarCoefficients

/-- The displayed radial coefficient derivative is the derivative of the SAME cofactor Fourier coefficient. -/
theorem radialCofactorJetScalar_genuineRadial (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row column : Fin 3) (r : RadialPoint) (mode : ℤ × ℤ) :
    HasDerivAt (fun radius => polarEntryScalar parameters
      (originalCofactorDeviation parameters L state.val.val.epsilon state.val.val.field)
      (originalCofactorDeviation_coherent parameters L state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low)
      row column 0 radius mode)
      (radialCofactorJetScalar parameters L compact state row column 1 0 r mode) r.val := by
  simpa [radialCofactorJetScalar, cofactorJetSequence, cofactorJetMultiplier] using
    polarEntryScalar_hasDerivAt parameters
      (originalCofactorDeviation parameters L state.val.val.epsilon state.val.val.field)
      (originalCofactorDeviation_coherent parameters L state.val.val.rho state.val.val.epsilon state.val.val.field state.val.val.low)
      row column 0 r.val mode

/-- The displayed axial coefficient derivative uses the original axial Fourier index n. -/
theorem radialCofactorJetScalar_genuineAxial (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact) (row column : Fin 3) (r : RadialPoint) (mode : ℤ × ℤ) :
    radialCofactorJetScalar parameters L compact state row column 0 2 r mode =
      (Complex.I * (mode.2 : ℂ)) * radialCofactorJetScalar parameters L compact state row column 0 0 r mode := by
  simp [radialCofactorJetScalar, cofactorJetSequence, cofactorJetMultiplier]

end Grad.AnnularReconstruction
