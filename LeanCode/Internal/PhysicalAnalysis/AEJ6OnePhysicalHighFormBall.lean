import AEJ5ActualFullHighForm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
namespace Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularKernelL2 Grad.AnnularCurrentBoundary
open Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Allocation

attribute [local instance] energyNormed energySeminormed energyRealNormed energyRealModule

/-- One positive primitive neighborhood simultaneously preserves the actual
radial reconstruction, retained first-row and outer inverses, and the full
high-form perturbation. No inner radius occurs in its definition. -/
def currentHighPrimitiveRadius (parameters : PhaseParameters) (L compact : ℝ) : ℝ :=
  min (radialMassLowRadius parameters L compact)
    (min (retainedInverseLowRadius parameters L compact)
      (32 * (currentHighErrorConstant parameters L compact + 1))⁻¹)

theorem currentHighPrimitiveRadius_positive (parameters : PhaseParameters) (L compact : ℝ) :
    0 < currentHighPrimitiveRadius parameters L compact := by
  apply lt_min (radialMassLowRadius_positive parameters L compact)
  apply lt_min (retainedInverseLowRadius_positive parameters L compact)
  apply inv_pos.mpr
  have := currentHighErrorConstant_nonnegative parameters L compact
  positivity

/-- The same original physical coefficient data supplies all retained
inverses on this B8 ball; the lower B7 requirements follow by monotonicity. -/
def currentHighRetainedState (parameters : PhaseParameters) (L compact : ℝ)
    (state : BoundaryReconstructionState parameters L compact)
    (small : physicalBudget parameters state.field state.rho state.epsilon 8 ≤
      currentHighPrimitiveRadius parameters L compact) : RetainedInverseState parameters L compact := by
  have lowerBudget : physicalBudget parameters state.field state.rho state.epsilon 7 ≤
      currentHighPrimitiveRadius parameters L compact :=
    (physicalBudget_monotone parameters state.field state.rho state.epsilon (by norm_num : 7 ≤ 8)).trans small
  let annular : AnnularReconstructionState parameters L compact :=
    ⟨state, lowerBudget.trans (min_le_left _ _)⟩
  exact ⟨annular, lowerBudget.trans ((min_le_right _ _).trans (min_le_left _ _))⟩

theorem currentHighRetainedState_same (parameters : PhaseParameters) (L compact : ℝ)
    (state : BoundaryReconstructionState parameters L compact)
    (small : physicalBudget parameters state.field state.rho state.epsilon 8 ≤
      currentHighPrimitiveRadius parameters L compact) :
    (currentHighRetainedState parameters L compact state small).val.val = state := rfl

theorem currentHighError_small (parameters : PhaseParameters) (L compact : ℝ)
    (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact) :
    currentHighErrorConstant parameters L compact * state.val.errorBudget 1 ≤ 1 / 32 := by
  have nonnegative := currentHighErrorConstant_nonnegative parameters L compact
  have budget := small.trans ((min_le_right _ _).trans (min_le_right _ _))
  apply (mul_le_mul_of_nonneg_left budget nonnegative).trans
  rw [← div_eq_mul_inv]
  apply (div_le_iff₀ (by positivity : 0 < 32 * (currentHighErrorConstant parameters L compact + 1))).mpr
  linarith

/-- The complete actual current form and its original circular counterpart
differ by at most 1/32 on the same energy space, uniformly in ell. -/
theorem actualHighForm_onePhysicalBall (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact) :
    ‖currentHighForm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state -
      circularHighBulkForm parameters L lower positive (lowerHalf.trans (by norm_num)) lengthPositive widthHalf widthLength 0‖ ≤ 1 / 32 ∧
    ∀ field test : annularEnergySpace lower L positive,
    ‖currentHighFormValue parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test -
      circularHighBulkFormValue parameters L lower positive (lowerHalf.trans (by norm_num)) lengthPositive widthHalf widthLength 0 field test‖ ≤
      (1 / 32 : ℝ) * ‖field‖ * ‖test‖ := by
  have smallError := currentHighError_small parameters L compact state small
  refine ⟨(currentHighForm_difference_norm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state).trans smallError, ?_⟩
  intro field test
  exact (currentHighFormValue_difference_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state field test).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right smallError (norm_nonneg field)) (norm_nonneg test))

end Grad.AnnularCurrentEnergy
