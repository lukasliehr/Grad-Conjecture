import AJC18OriginalSharedInverseBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Grad.AnnularStrongSolution
open Grad.CartesianState Grad.AnnularVariational Grad.AnnularCoupledInverse Grad.AnnularCrossMaps
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularHighTilt Grad.AnnularLowEnergy
open Grad.AnnularStrongData Grad.AnnularFullSource Grad.AnnularReconstruction
open Grad.BoundaryKernelAction
open Grad.AnnularCurrentSource Grad.GaugeCoefficients.Physical.Allocation

private theorem equivalent_solution {D E F : Type*} (equivalence : E ≃ F)
    (equation : D → F → Prop) (solution : D → F)
    (solves : ∀ data, equation data (solution data)) (data : D) :
    equation data (equivalence (equivalence.symm (solution data))) := by
  rw [equivalence.apply_symm_apply]
  exact solves data

private theorem equivalent_unique {D E F : Type*} (equivalence : E ≃ F)
    (equation : D → F → Prop) (solution : D → F)
    (unique : ∀ data candidate, equation data candidate → candidate = solution data)
    (data : D) (candidate : E) (solves : equation data (equivalence candidate)) :
    candidate = equivalence.symm (solution data) := by
  exact (equivalence.symm_apply_apply candidate).symm.trans (congrArg equivalence.symm (unique data _ solves))

private theorem norm_bound_of_same {E : Type*} [NormedAddCommGroup E]
    (candidate solution : E) (bound : ℝ) (same : candidate = solution) (estimate : ‖solution‖ ≤ bound) :
    ‖candidate‖ ≤ bound := same ▸ estimate

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
    (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)

/-- The same independently sourced coupled equation in the original actual
AK/AJ coordinates, via the proved BF5 and BF6 equivalences. -/
def OriginalStrongCoupledEquation (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower L positive) : Prop :=
  StrongCoupledEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (originalStrongWeightEquivalence parameters lower L positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)
    (originalCoupledEquivalence parameters lower L positive (lowerHalf.trans (by norm_num)) lengthPositive candidate)

variable (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤
      coupledPrimitiveRadius parameters L compact)

theorem originalSharedResponse_equation (data : OriginalStrongCarrier parameters lower 0 0) :
    OriginalStrongCoupledEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data
      (originalSharedResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data) := by
  exact equivalent_solution
    (originalCoupledEquivalence parameters lower L positive (lowerHalf.trans (by norm_num)) lengthPositive).toEquiv
    (StrongCoupledEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (sharedStrongResponse_equation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (originalStrongWeightEquivalence parameters lower L positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data)

theorem originalSharedResponse_unique (data : OriginalStrongCarrier parameters lower 0 0)
    (candidate : OriginalCoupledSpace lower L positive)
    (equation : OriginalStrongCoupledEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state data candidate) :
    candidate = originalSharedResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small data := by
  exact equivalent_unique
    (originalCoupledEquivalence parameters lower L positive (lowerHalf.trans (by norm_num)) lengthPositive).toEquiv
    (StrongCoupledEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (sharedStrongResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (sharedStrongResponse_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (originalStrongWeightEquivalence parameters lower L positive (lowerHalf.trans (by norm_num)) lengthPositive 0 0 data) candidate equation

/-- One primitive B8 ball gives the same unique original-coordinate solution
for every collar and original strong datum, with the exact base ell^-13/4
bound. This does not assert all-grade full-graph completion or exhaustion. -/
theorem originalSharedInverse_oneBall (parameters : PhaseParameters) (L compact : ℝ)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) :
    0 < coupledPrimitiveRadius parameters L compact ∧
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
        (state : BoundaryReconstructionState parameters L compact)
        (small : physicalBudget parameters state.field state.rho state.epsilon 8 ≤ coupledPrimitiveRadius parameters L compact)
        (data : OriginalStrongCarrier parameters lower 0 0),
        let retained := coupledRetainedState parameters L compact state small
        (∃! solution : OriginalCoupledSpace lower L positive,
          OriginalStrongCoupledEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength retained data solution) ∧
        (∀ solution : OriginalCoupledSpace lower L positive,
          OriginalStrongCoupledEquation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength retained data solution →
          ‖solution‖ ≤ C * lower ^ (-13 / 4 : ℝ) * ‖data‖) := by
  refine ⟨coupledPrimitiveRadius_positive parameters L compact lengthPositive,
    originalSharedInverseConstant parameters L compact,
    originalSharedInverseConstant_nonnegative parameters L compact lengthPositive, ?_⟩
  intro lower positive lowerHalf state small data
  let retained := coupledRetainedState parameters L compact state small
  have sameSmall := coupledRetainedState_small parameters L compact state small
  constructor
  · exact ⟨originalSharedResponse parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength retained sameSmall data,
      originalSharedResponse_equation parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength retained sameSmall data,
      fun candidate equation => originalSharedResponse_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength retained sameSmall data candidate equation⟩
  · intro candidate equation
    exact norm_bound_of_same candidate _ _
      (originalSharedResponse_unique parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength retained sameSmall data candidate equation)
      (originalSharedResponse_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength retained sameSmall data)

end Grad.AnnularStrongSolution
