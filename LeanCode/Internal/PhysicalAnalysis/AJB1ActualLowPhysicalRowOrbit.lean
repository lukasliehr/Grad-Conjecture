import AIW18OriginalLowBF6Consumer
import AIX13ActualEliminatedPhysicalOrbit

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularCurrentLow Grad.AnnularKernelOrbit
open Grad.AnnularKernelL2 Grad.AnnularKernelContinuity Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.GaugeCoefficients.Physical.Allocation

/-- The SAME physical pre-Q seven-to-one row, translated at the full kernel
level. The third row contains the literal mean-free P in physical rV. -/
def actualLowRowOrbit (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters length compact)
    (row : Fin 3) (tau : OrbitParameter) : DivisionRow 7 lower →L[ℂ] DivisionRow 1 lower :=
  radialOrbitAction parameters (lowPhysicalRowKernel parameters length compact state row)
    (lowPhysicalRowKernel_regular parameters length compact state row) 0 lower positive bounded tau

def actualLowRowOrbitJet (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters length compact)
    (row : Fin 3) (tau : OrbitParameter) (angular cell : ℕ) : DivisionRow 7 lower →L[ℂ] DivisionRow 1 lower :=
  radialOrbitJetAction parameters (lowPhysicalRowKernel parameters length compact state row)
    (lowPhysicalRowKernel_regular parameters length compact state row) 0 lower positive bounded tau angular cell

theorem actualLowRowOrbit_conjugation (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters length compact)
    (row : Fin 3) (tau : OrbitParameter) :
    actualLowRowOrbit parameters length compact lower positive bounded state row tau =
      (orbitLpAction (RadialL2 1 lower) tau).comp
        ((lowPhysicalRowAction parameters length compact lower positive bounded state row).comp
          (orbitLpAction (RadialL2 7 lower) (-tau))) :=
  radialOrbitAction_conjugation _ _ _ _ _ _ _ _

theorem actualLowRowOrbit_hasFDerivAt (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : RetainedInverseState parameters length compact)
    (row : Fin 3) (tau : OrbitParameter) :
    HasFDerivAt (actualLowRowOrbit parameters length compact lower positive bounded state row)
      (orbitDifferential
        (actualLowRowOrbitJet parameters length compact lower positive bounded state row tau 1 0)
        (actualLowRowOrbitJet parameters length compact lower positive bounded state row tau 0 1)) tau :=
  radialOrbitAction_hasFDerivAt _ _ _ _ _ _ _ _

/-- Circular low rows are genuinely zero-shift, including the physical rV P. -/
theorem actualLowCircularRow_zeroShift (parameters : PhaseParameters) (length : ℝ)
    (row : Fin 3) (radius : RadialPoint) :
    ZeroShiftKernel (lowCircularRowKernel parameters length row radius) := by
  fin_cases row
  · exact circularNormalizedUnprojectedFirstRowKernel_zeroShift _ length
  · exact circularNormalizedUnprojectedCKernel_zeroShift _ length
  · exact circularNormalizedPhysicalRVKernel_zeroShift _ length

/-- A first positive jet uses exactly state.errorBudget 1 = primitive B8;
no higher-moment smallness and no translated coefficient state is assumed. -/
theorem actualLowRowOrbitJet_oneHigh (parameters : PhaseParameters) (length compact : ℝ)
    (row : Fin 3) (angular cell : ℕ) (orderPositive : 0 < angular + cell) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (state : RetainedInverseState parameters length compact) (lower : ℝ)
        (positive : 0 < lower) (bounded : lower ≤ 1) (tau : OrbitParameter),
        ‖actualLowRowOrbitJet parameters length compact lower positive bounded state row tau angular cell‖ ≤
          constant * state.val.errorBudget (angular + cell) := by
  obtain ⟨constant, nonnegative, moment⟩ :=
    lowPhysicalRowKernel_referenceDifference parameters length compact row (angular + cell)
  refine ⟨constant, nonnegative, ?_⟩
  intro state lower positive bounded tau
  have budgetNonnegative : 0 ≤ state.val.errorBudget (angular + cell) :=
    physicalBudget_nonnegative parameters state.val.val.field state.val.val.rho state.val.val.epsilon _
  exact radialOrbitJetAction_referenceMoment_bound parameters
    (lowPhysicalRowKernel parameters length compact state row)
    (lowCircularRowKernel parameters length row)
    (lowPhysicalRowKernel_regular parameters length compact state row)
    ((lowPhysicalRowKernel_regular parameters length compact state row).sub (lowCircularRowKernel_regular parameters length row))
    (actualLowCircularRow_zeroShift parameters length row) 0 lower positive bounded tau angular cell orderPositive
    (constant * state.val.errorBudget (angular + cell)) (mul_nonneg nonnegative budgetNonnegative) (by simpa only [Nat.zero_add] using moment state)

end Grad.AnnularLowOrbit
