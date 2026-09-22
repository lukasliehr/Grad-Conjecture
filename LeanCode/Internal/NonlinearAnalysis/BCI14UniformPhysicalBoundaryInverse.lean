import BCI13VanishingBoundaryErrorMoments

noncomputable section
set_option maxHeartbeats 1000000
namespace Grad.ActualBoundaryInverse
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.GaugeCoefficients.Physical.Allocation

abbrev BoundaryInverseState (parameters : PhaseParameters) (L compact : ℝ) :=
  {state : PhysicalBoundaryState parameters L compact // state.budget 0 ≤ boundaryInverseLowRadius parameters L compact}

abbrev BoundaryInverseMoments (parameters : PhaseParameters) (L compact : ℝ) {input output : ℕ}
    (family : BoundaryInverseState parameters L compact → FullTwoFrequencyKernel parameters input output) :=
  UniformKernelMoments parameters (fun state => state.val.val.size) family

theorem BoundaryInverseMoments.restrict {parameters : PhaseParameters} {L compact : ℝ} {input output : ℕ}
    {family : PhysicalBoundaryState parameters L compact → FullTwoFrequencyKernel parameters input output}
    (bounded : BoundaryKernelMoments parameters L compact family) :
    BoundaryInverseMoments parameters L compact (fun state => family state.val) := by
  intro moment
  obtain ⟨constant, nonnegative, bound⟩ := bounded moment
  exact ⟨constant, nonnegative, fun state => bound state.val⟩

theorem BoundaryInverseMoments.comp {parameters : PhaseParameters} {L compact : ℝ} {input middle output : ℕ}
    {outer : BoundaryInverseState parameters L compact → FullTwoFrequencyKernel parameters middle output}
    {inner : BoundaryInverseState parameters L compact → FullTwoFrequencyKernel parameters input middle}
    (houter : BoundaryInverseMoments parameters L compact outer) (hinner : BoundaryInverseMoments parameters L compact inner) :
    BoundaryInverseMoments parameters L compact (fun state => fullKernelComposition (outer state) (inner state)) :=
  UniformKernelMoments.comp (fun state => state.val.val.size_nonnegative)
    (1 + actualMassInverseLowRadius parameters L compact)
    (by linarith [actualMassInverseLowRadius_positive parameters L compact])
    (fun state => state.val.val.size_zero_le) houter hinner

theorem actualBoundaryAmbientInverse_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryInverseMoments parameters L compact (fun state => actualBoundaryAmbientInverse state.val state.property) := by
  unfold actualBoundaryAmbientInverse
  apply UniformKernelMoments.negativeIdentityInverse (fun state => state.val.val.one_le_size)
  · exact BoundaryInverseMoments.restrict (BoundaryDeviationMoments.regular (actualBoundaryE_vanishingMoments parameters L compact))
  · intro state
    exact (boundary_E_le_quarter state.val state.property).trans (by norm_num)

theorem actualHighBoundaryInverse_physicalMoments (parameters : PhaseParameters) (L compact : ℝ) :
    BoundaryInverseMoments parameters L compact (fun state => actualHighBoundaryInverse state.val state.property) := by
  unfold actualHighBoundaryInverse
  exact BoundaryInverseMoments.comp
    (BoundaryInverseMoments.restrict (BoundaryKernelMoments.fixed parameters L compact (highAngularKernel parameters 1)))
    (actualBoundaryAmbientInverse_physicalMoments parameters L compact)

/-- The genuine boundary inverse has the same original total-grade one-high
allocation as the accepted physical reconstruction. -/
theorem actualHighBoundaryInverse_oneHigh (parameters : PhaseParameters) (L compact : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ state : BoundaryInverseState parameters L compact,
      ∀ (high : NegativeTotalTrace parameters grade 1) (low : NegativeTotalTrace parameters 0 1),
      ‖fullOneHighKernelAction parameters grade (actualHighBoundaryInverse state.val state.property) high low‖ ≤
        constant * ((1 + state.val.budget 1) * ‖high‖ + (1 + state.val.budget (grade + 1)) * ‖low‖) := by
  obtain ⟨base, baseNonnegative, baseBound⟩ := actualHighBoundaryInverse_physicalMoments parameters L compact 1
  obtain ⟨top, topNonnegative, topBound⟩ := actualHighBoundaryInverse_physicalMoments parameters L compact (grade + 1)
  refine ⟨2 ^ grade * (base + top), mul_nonneg (by positivity) (add_nonneg baseNonnegative topNonnegative), ?_⟩
  intro state high low
  apply (fullOneHighKernelAction_bound parameters grade (actualHighBoundaryInverse state.val state.property) high low).trans
  have first := mul_le_mul_of_nonneg_right (baseBound state) (norm_nonneg high)
  have second := mul_le_mul_of_nonneg_right (topBound state) (norm_nonneg low)
  have budgetBase := physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8
  have budgetHigh := physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon (grade + 1 + 7)
  have sumBound : fullKernelMoment parameters 1 (actualHighBoundaryInverse state.val state.property) * ‖high‖ +
      fullKernelMoment parameters (grade + 1) (actualHighBoundaryInverse state.val state.property) * ‖low‖ ≤
      (base + top) * ((1 + state.val.budget 1) * ‖high‖ + (1 + state.val.budget (grade + 1)) * ‖low‖) := by
    change _ ≤ _ at first second
    have firstTerm : 0 ≤ (1 + state.val.budget 1) * ‖high‖ := mul_nonneg (by linarith) (norm_nonneg _)
    have secondTerm : 0 ≤ (1 + state.val.budget (grade + 1)) * ‖low‖ := mul_nonneg (by linarith) (norm_nonneg _)
    change _ ≤ base * (1 + state.val.budget 1) * ‖high‖ at first
    change _ ≤ top * (1 + state.val.budget (grade + 1)) * ‖low‖ at second
    nlinarith [mul_nonneg baseNonnegative secondTerm, mul_nonneg topNonnegative firstTerm]
  exact (mul_le_mul_of_nonneg_left sumBound (by positivity : 0 ≤ (2 : ℝ) ^ grade)).trans_eq (by ring)

end Grad.ActualBoundaryInverse
