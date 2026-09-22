import AJG11UniformFullReconstruction
import AJG12SameOriginalCorrectedFlux

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularPhysicalReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularReconstruction
open Grad.AnnularKernelL2 Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularFullSource
open Grad.GaugeCoefficients.Physical.Allocation

/-- Uniform reconstruction of the SAME shared-source inverse on the SAME
original B8 ball. All constants precede the collar, state and datum. -/
theorem sameSharedInverse_reconstruction_uniform (parameters : PhaseParameters) (L compact : ℝ)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
        (state : RetainedInverseState parameters L compact)
        (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
          coupledPrimitiveRadius parameters L compact)
        (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0),
        let solution := sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
        ‖sharedFullCovariant parameters L compact lower positive (lowerHalf.trans (by norm_num)) lengthPositive state.val data solution‖ +
          ‖sharedFullRotatedCovariant parameters L compact lower positive (lowerHalf.trans (by norm_num)) lengthPositive state.val data solution‖ ≤
        constant * ‖data‖ := by
  obtain ⟨coefficient, nonnegative, estimate⟩ := sharedFullReconstruction_uniform parameters L compact
  let inverseConstant := independentCoupledDataConstant parameters L compact
  have inverseNonnegative : 0 ≤ inverseConstant := independentCoupledDataConstant_nonnegative parameters L compact
  refine ⟨2 * coefficient * ((11 + 4 * L) * (2 * inverseConstant) + 3), by positivity, ?_⟩
  intro lower positive lowerHalf state small data
  let solution := sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  have response : ‖solution‖ ≤ 2 * inverseConstant * ‖data‖ :=
    sharedStrongResponse_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data
  have budget : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 7 ≤ 1 :=
    (physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon (by norm_num : 7 ≤ 8)).trans
      (coupledPrimitive_budget_one parameters L compact state small)
  have scalarBound : 1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 7 ≤ 2 := by linarith
  have reconstructed := estimate lower positive (lowerHalf.trans (by norm_num)) lengthPositive state.val data solution
  apply reconstructed.trans
  calc
    _ ≤ coefficient * 2 * ((11 + 4 * L) * (2 * inverseConstant * ‖data‖) + 3 * ‖data‖) := by
      gcongr
    _ = (2 * coefficient * ((11 + 4 * L) * (2 * inverseConstant) + 3)) * ‖data‖ := by ring

end Grad.AnnularPhysicalReconstruction
