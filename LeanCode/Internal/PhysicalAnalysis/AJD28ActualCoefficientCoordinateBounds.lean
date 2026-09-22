import AJD27OriginalCoupledBudgetContexts
import AJD24ActualBetaInverseJetBounds

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace Grad.AnnularCrossOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularKernelOrbit Grad.AnnularKernelL2 Grad.AnnularKernelContinuity
open Grad.AnnularReconstruction Grad.AnnularCurrentLow Grad.AnnularLowOrbit Grad.BoundaryKernelAction
open Grad.AnnularHighInverseOrbit Grad.AnnularInverseCalculus Grad.GaugeCoefficients.Physical.Allocation

private theorem uniformCoordinateBound_of_jet {Context : Type*} {E : Context → Type*}
    [∀ context, NormedAddCommGroup (E context)] [∀ context, NormedSpace ℝ (E context)]
    (budget : Context → ℕ → ℝ) (jet : (context : Context) → ℕ → ℕ → OrbitParameter → E context)
    (derivative : ∀ context angular cell point, HasFDerivAt (jet context angular cell)
      (orbitColumns (jet context (angular + 1) cell point) (jet context angular (cell + 1) point)) point)
    (bound : ∀ angular cell, ∃ constant : ℝ, 0 ≤ constant ∧ ∀ context point,
      ‖jet context angular cell point‖ ≤ constant * coordinateJetWeight (budget context) (angular + cell)) :
    UniformCoordinateBound budget (fun context => jet context 0 0) := by
  intro axis order
  obtain ⟨constant, nonnegative, estimate⟩ := bound (if axis then 0 else order) (if axis then order else 0)
  refine ⟨constant, nonnegative, ?_⟩
  intro context base time
  rw [iteratedDeriv_coordinateJet (jet context) (derivative context)]
  cases axis <;> simpa only [Bool.false_eq_true, ↓reduceIte, Nat.zero_add, Nat.add_zero] using estimate context (base + time • axisVector _)

variable (parameters : PhaseParameters) (L compact : ℝ)

/-- The physical low rows have the same uniform moment family as their
actual reconstruction kernels, before either high/low support projection. -/
theorem lowPhysicalRowKernel_allMoments (row : Fin 3) :
    RetainedPhysicalMoments parameters L compact (fun state radius => lowPhysicalRowKernel parameters L compact state row radius) := by
  fin_cases row
  · exact radialNormalizedUnprojectedFirstRowKernel_physicalMoments parameters L compact
  · exact radialNormalizedUnprojectedCKernel_physicalMoments parameters L compact
  · exact radialNormalizedPhysicalRVKernel_physicalMoments parameters L compact

/-- The actual full eight-to-three elimination has a bounded base value
and one-high positive coordinate derivatives on the original coupled ball. -/
theorem actualEliminatedOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        actualEliminatedOrbit parameters L compact context.lower context.positive
          (context.lowerHalf.trans (by norm_num)) context.state 0) := by
  let jet := fun (context : CoupledCoordinateContext parameters L compact) angular cell tau =>
    actualEliminatedOrbitJet parameters L compact context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) context.state 0 tau angular cell
  have derivative (context : CoupledCoordinateContext parameters L compact) (angular cell : ℕ) (tau : OrbitParameter) :
      HasFDerivAt (jet context angular cell)
        (orbitColumns (jet context (angular + 1) cell tau) (jet context angular (cell + 1) tau)) tau :=
    radialOrbitJetAction_hasFDerivAt parameters (radialEliminatedBulkKernel parameters L compact context.state)
      (radialEliminatedBulkKernel_regular parameters L compact context.state) 0 context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) tau angular cell
  have bound (angular cell : ℕ) : ∃ constant : ℝ, 0 ≤ constant ∧ ∀ context tau,
      ‖jet context angular cell tau‖ ≤ constant * coordinateJetWeight context.budget (angular + cell) := by
    by_cases zero : angular + cell = 0
    · have angularZero : angular = 0 := by omega
      have cellZero : cell = 0 := by omega
      subst angular
      subst cell
      obtain ⟨constant, nonnegative, moment⟩ := radialEliminatedBulkKernel_physicalMoments parameters L compact 0
      refine ⟨2 * constant, by positivity, ?_⟩
      intro context tau
      simp only [Nat.zero_add, coordinateJetWeight, ↓reduceIte, mul_one]
      apply radialOrbitJetAction_norm_le parameters _ _ 0 context.lower context.positive
        (context.lowerHalf.trans (by norm_num)) tau 0 0 (2 * constant) (by positivity)
      intro radius
      exact (moment context.state radius).trans
        ((mul_le_mul_of_nonneg_left context.size_zero_le_two nonnegative).trans_eq (mul_comm constant 2))
    · obtain ⟨constant, nonnegative, estimate⟩ := actualEliminatedOrbitJet_oneHigh parameters L compact 0 angular cell (by omega)
      refine ⟨constant, nonnegative, ?_⟩
      intro context tau
      rw [coordinateJetWeight, if_neg zero]
      have actual := estimate context.state context.lower context.positive (context.lowerHalf.trans (by norm_num)) tau
      exact actual.trans (mul_le_mul_of_nonneg_left (physicalBudget_monotone _ _ _ _ (by omega)) nonnegative)
  have tame := uniformCoordinateBound_of_jet CoupledCoordinateContext.budget jet derivative bound
  have same : (fun context => jet context 0 0) =
      fun context : CoupledCoordinateContext parameters L compact =>
        actualEliminatedOrbit parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state 0 := by
    funext context tau
    exact radialOrbitJetAction_zero parameters _ _ 0 context.lower context.positive (context.lowerHalf.trans (by norm_num)) tau
  rw [same] at tame
  exact tame

/-- The SAME pre-Q physical low row enjoys the identical pure-coordinate
bound; its zeroth estimate comes from the actual physical moment family. -/
theorem actualLowRowOrbit_uniformCoordinateBound (row : Fin 3) :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        actualLowRowOrbit parameters L compact context.lower context.positive
          (context.lowerHalf.trans (by norm_num)) context.state row) := by
  let jet := fun (context : CoupledCoordinateContext parameters L compact) angular cell tau =>
    actualLowRowOrbitJet parameters L compact context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) context.state row tau angular cell
  have derivative (context : CoupledCoordinateContext parameters L compact) (angular cell : ℕ) (tau : OrbitParameter) :
      HasFDerivAt (jet context angular cell)
        (orbitColumns (jet context (angular + 1) cell tau) (jet context angular (cell + 1) tau)) tau :=
    radialOrbitJetAction_hasFDerivAt parameters (lowPhysicalRowKernel parameters L compact context.state row)
      (lowPhysicalRowKernel_regular parameters L compact context.state row) 0 context.lower context.positive
      (context.lowerHalf.trans (by norm_num)) tau angular cell
  have bound (angular cell : ℕ) : ∃ constant : ℝ, 0 ≤ constant ∧ ∀ context tau,
      ‖jet context angular cell tau‖ ≤ constant * coordinateJetWeight context.budget (angular + cell) := by
    by_cases zero : angular + cell = 0
    · have angularZero : angular = 0 := by omega
      have cellZero : cell = 0 := by omega
      subst angular
      subst cell
      obtain ⟨constant, nonnegative, moment⟩ := lowPhysicalRowKernel_allMoments parameters L compact row 0
      refine ⟨2 * constant, by positivity, ?_⟩
      intro context tau
      simp only [Nat.zero_add, coordinateJetWeight, ↓reduceIte, mul_one]
      apply radialOrbitJetAction_norm_le parameters _ _ 0 context.lower context.positive
        (context.lowerHalf.trans (by norm_num)) tau 0 0 (2 * constant) (by positivity)
      intro radius
      exact (moment context.state radius).trans
        ((mul_le_mul_of_nonneg_left context.size_zero_le_two nonnegative).trans_eq (mul_comm constant 2))
    · obtain ⟨constant, nonnegative, estimate⟩ := actualLowRowOrbitJet_oneHigh parameters L compact row angular cell (by omega)
      refine ⟨constant, nonnegative, ?_⟩
      intro context tau
      rw [coordinateJetWeight, if_neg zero]
      have actual := estimate context.state context.lower context.positive (context.lowerHalf.trans (by norm_num)) tau
      exact actual.trans (mul_le_mul_of_nonneg_left (physicalBudget_monotone _ _ _ _ (by omega)) nonnegative)
  have tame := uniformCoordinateBound_of_jet CoupledCoordinateContext.budget jet derivative bound
  have same : (fun context => jet context 0 0) =
      fun context : CoupledCoordinateContext parameters L compact =>
        actualLowRowOrbit parameters L compact context.lower context.positive (context.lowerHalf.trans (by norm_num)) context.state row := by
    funext context tau
    exact radialOrbitJetAction_zero parameters _ _ 0 context.lower context.positive (context.lowerHalf.trans (by norm_num)) tau
  rw [same] at tame
  exact tame

/-- The actual beta inverse on the same original high negative-half data. -/
theorem actualBoundaryInverseOrbit_uniformCoordinateBound :
    UniformCoordinateBound CoupledCoordinateContext.budget
      (fun context : CoupledCoordinateContext parameters L compact =>
        actualBoundaryInverseOrbitJet parameters L compact context.state 0 0) := by
  apply uniformCoordinateBound_of_jet CoupledCoordinateContext.budget
    (fun context angular cell => actualBoundaryInverseOrbitJet parameters L compact context.state angular cell)
    (fun context => actualBoundaryInverseOrbitJet_hasFDerivAt parameters L compact context.state)
  intro angular cell
  by_cases zero : angular + cell = 0
  · have angularZero : angular = 0 := by omega
    have cellZero : cell = 0 := by omega
    subst angular
    subst cell
    obtain ⟨constant, nonnegative, estimate⟩ := actualBoundaryInverseOrbit_zero_uniform parameters L compact
    refine ⟨constant, nonnegative, ?_⟩
    intro context tau
    simpa only [Nat.zero_add, coordinateJetWeight, ↓reduceIte, mul_one] using
      estimate context.state context.budget_zero_le_one tau
  · obtain ⟨constant, nonnegative, estimate⟩ := actualBoundaryInverseOrbitJet_positive_oneHigh parameters L compact angular cell (by omega)
    refine ⟨constant, nonnegative, ?_⟩
    intro context tau
    simpa only [coordinateJetWeight, if_neg zero, CoupledCoordinateContext.budget] using estimate context.state tau

end Grad.AnnularCrossOrbit
