import AJA14ActualFullJetTower

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.AnnularHighInverseOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularCurrentEnergy Grad.AnnularCurrentInverse
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit Grad.GaugeCoefficients.Physical.Allocation
attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

/-- The full positive form jet has only one original B_(j+8) factor. -/
theorem currentHighFormOrbitJet_oneHigh (parameters : PhaseParameters) (L compact : ℝ)
    (angular cell : ℕ) (orderPositive : 0 < angular + cell) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
        (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
        (state : RetainedInverseState parameters L compact) (tau : OrbitParameter),
      ‖currentHighFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau‖ ≤
        constant * state.val.errorBudget (1 + (angular + cell)) := by
  obtain ⟨bulkC, bulkNonnegative, bulkBound⟩ := highBulkFormOrbitJet_oneHigh parameters L compact angular cell orderPositive
  obtain ⟨boundaryC, boundaryNonnegative, boundaryBound⟩ := highBoundaryFormOrbitJet_oneHigh parameters L compact angular cell
  refine ⟨bulkC + boundaryC, add_nonneg bulkNonnegative boundaryNonnegative, ?_⟩
  intro lower positive lowerHalf lengthPositive widthHalf widthLength state tau
  have budget : state.val.errorBudget (angular + cell) ≤ state.val.errorBudget (1 + (angular + cell)) :=
    physicalBudget_monotone parameters state.val.val.field state.val.val.rho state.val.val.epsilon (by omega)
  have bulk := (bulkBound lower positive (lowerHalf.trans (by norm_num)) lengthPositive widthHalf widthLength state tau).trans
    (mul_le_mul_of_nonneg_left budget bulkNonnegative)
  have boundary := boundaryBound lower positive lowerHalf lengthPositive state tau
  change ‖highBulkFormOrbitJet parameters L lower positive lengthPositive widthHalf widthLength compact
    (lowerHalf.trans (by norm_num)) state tau angular cell +
    highBoundaryFormOrbitJet parameters L lower positive lowerHalf lengthPositive compact state tau angular cell‖ ≤ _
  have combined := add_le_add bulk boundary
  calc
    _ ≤ _ := norm_add_le
      (highBulkFormOrbitJet parameters L lower positive lengthPositive widthHalf widthLength compact (lowerHalf.trans (by norm_num)) state tau angular cell)
      (highBoundaryFormOrbitJet parameters L lower positive lowerHalf lengthPositive compact state tau angular cell)
    _ ≤ bulkC * state.val.errorBudget (1 + (angular + cell)) + boundaryC * state.val.errorBudget (1 + (angular + cell)) := combined
    _ = (bulkC + boundaryC) * state.val.errorBudget (1 + (angular + cell)) := by ring

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
    (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)

def currentHighZeroFormOrbitJet (angular cell : ℕ) (tau : OrbitParameter) :=
  formRestriction (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
    (currentHighFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau)

theorem currentHighZeroFormOrbitJet_norm_le (angular cell : ℕ) (tau : OrbitParameter) :
    ‖currentHighZeroFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau‖ ≤
      ‖currentHighFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau‖ :=
  formRestriction_norm_le _ (fun _ => rfl) _

theorem currentHighZeroFormOrbitJet_hasFDerivAt (angular cell : ℕ) (tau : OrbitParameter) :
    HasFDerivAt (currentHighZeroFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell)
      (orbitColumns
        (currentHighZeroFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state (angular + 1) cell tau)
        (currentHighZeroFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular (cell + 1) tau)) tau := by
  have derivative := formRestriction_hasFDerivAt
    (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
    (currentHighFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell)
    _ tau (currentHighFormOrbitJet_hasFDerivAt parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state angular cell tau)
  apply derivative.congr_fderiv
  exact orbitColumns_comp
    (E := annularEnergySpace lower L positive →L[ℝ] annularEnergySpace lower L positive →L[ℝ] ℝ)
    (F := annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ]
      annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    (formRestriction (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)) _ _

theorem currentHighZeroFormOrbitJet_zero (tau : OrbitParameter) :
    currentHighZeroFormOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau =
      currentHighZeroFormOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau :=
  congrArg (formRestriction (annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive))
    (currentHighFormOrbitJet_zero parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state tau)

end Grad.AnnularHighInverseOrbit
