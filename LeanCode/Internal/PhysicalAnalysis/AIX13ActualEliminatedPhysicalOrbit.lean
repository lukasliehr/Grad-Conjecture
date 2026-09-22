import AIX12OriginalOrbitAndReferenceCancellation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKernelOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularKernelContinuity
open Grad.AnnularCircularForm Grad.GaugeCoefficients.Physical.Allocation

/-- The orbital family of the SAME original normalized eight-to-three
physical elimination, with its complete x,c,rV signs and source slots. -/
def actualEliminatedOrbit (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)
    (power : ℕ) (tau : OrbitParameter) : DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower :=
  radialOrbitAction parameters (radialEliminatedBulkKernel parameters L compact state)
    (radialEliminatedBulkKernel_regular parameters L compact state) power lower positive bounded tau

def actualEliminatedOrbitJet (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)
    (power : ℕ) (tau : OrbitParameter) (angular cell : ℕ) : DivisionRow 8 lower →L[ℂ] DivisionRow 3 lower :=
  radialOrbitJetAction parameters (radialEliminatedBulkKernel parameters L compact state)
    (radialEliminatedBulkKernel_regular parameters L compact state) power lower positive bounded tau angular cell

theorem actualEliminatedOrbit_conjugation (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)
    (power : ℕ) (tau : OrbitParameter) :
    actualEliminatedOrbit parameters L compact lower positive bounded state power tau =
      (orbitLpAction (RadialL2 3 lower) tau).comp
        ((eliminatedBulkAction parameters L compact lower positive bounded state power).comp
          (orbitLpAction (RadialL2 8 lower) (-tau))) := by
  rw [eliminatedBulkAction_eq_regular]
  exact radialOrbitAction_conjugation _ _ _ _ _ _ _ _

theorem actualEliminatedOrbit_hasFDerivAt (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters L compact)
    (power : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (actualEliminatedOrbit parameters L compact lower positive bounded state power)
      (orbitDifferential
        (actualEliminatedOrbitJet parameters L compact lower positive bounded state power tau 1 0)
        (actualEliminatedOrbitJet parameters L compact lower positive bounded state power tau 0 1)) tau :=
  radialOrbitAction_hasFDerivAt _ _ _ _ _ _ _ _

/-- Every positive derivative uses one actual error envelope moment, with
no extra constant reference term and no radius-dependent smallness. -/
theorem actualEliminatedOrbitJet_oneHigh (parameters : PhaseParameters) (L compact : ℝ)
    (power angular cell : ℕ) (orderPositive : 0 < angular + cell) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : RetainedInverseState parameters L compact) (lower : ℝ)
        (positive : 0 < lower) (bounded : lower ≤ 1) (tau : OrbitParameter),
        ‖actualEliminatedOrbitJet parameters L compact lower positive bounded state power tau angular cell‖ ≤
          constant * state.val.errorBudget (power + (angular + cell)) := by
  obtain ⟨constant, nonnegative, moment⟩ :=
    radialEliminatedBulkKernel_referenceDifference parameters L compact (power + (angular + cell))
  refine ⟨constant, nonnegative, ?_⟩
  intro state lower positive bounded tau
  have budgetNonnegative : 0 ≤ state.val.errorBudget (power + (angular + cell)) :=
    physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon _
  exact radialOrbitJetAction_referenceMoment_bound parameters
    (radialEliminatedBulkKernel parameters L compact state)
    (fun r => circularEliminatedBulkKernel (radialKernelParameters parameters r) L)
    (radialEliminatedBulkKernel_regular parameters L compact state)
    (radialEliminatedBulkError_regular parameters L compact state)
    (fun r => circularEliminatedBulkKernel_zeroShift (radialKernelParameters parameters r) L)
    power lower positive bounded tau angular cell orderPositive
    (constant * state.val.errorBudget (power + (angular + cell))) (mul_nonneg nonnegative budgetNonnegative)
    (moment state)

/-- Concrete operator-norm remainder for the same physical reconstruction
orbit at every mixed order, independent of the inner radius. -/
theorem actualEliminatedOrbitJet_remainder (parameters : PhaseParameters) (L compact : ℝ)
    (power angular cell : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : RetainedInverseState parameters L compact) (lower : ℝ)
        (positive : 0 < lower) (bounded : lower ≤ 1) (tau step : OrbitParameter),
        ‖actualEliminatedOrbitJet parameters L compact lower positive bounded state power (tau + step) angular cell -
          actualEliminatedOrbitJet parameters L compact lower positive bounded state power tau angular cell -
          (step.1 : ℂ) • actualEliminatedOrbitJet parameters L compact lower positive bounded state power tau (angular + 1) cell -
          (step.2 : ℂ) • actualEliminatedOrbitJet parameters L compact lower positive bounded state power tau angular (cell + 1)‖ ≤
          constant * orbitStepSize step ^ 2 * state.val.size (power + (angular + cell + 2)) := by
  obtain ⟨constant, nonnegative, moment⟩ :=
    radialEliminatedBulkKernel_physicalMoments parameters L compact (power + (angular + cell + 2))
  refine ⟨3 * constant, by positivity, ?_⟩
  intro state lower positive bounded tau step
  have sizeNonnegative : 0 ≤ state.val.size (power + (angular + cell + 2)) := by
    change 0 ≤ 1 + physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon _
    exact add_nonneg (by norm_num) (physicalBudget_nonnegative _ _ _ _ _)
  have bound := radialOrbitJetAction_remainder_bound parameters
    (radialEliminatedBulkKernel parameters L compact state) (radialEliminatedBulkKernel_regular parameters L compact state)
    power lower positive bounded tau step angular cell (constant * state.val.size (power + (angular + cell + 2)))
    (mul_nonneg nonnegative sizeNonnegative) (moment state)
  exact bound.trans_eq (by ring)

end Grad.AnnularKernelOrbit
