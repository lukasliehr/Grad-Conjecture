import AJF15SameLiftedHighSolverOrbit
import AJF18PositiveJetCompositionBound
import AJF19ActualJetAxisRestriction
import AJA22SharpHighInverseOneHigh

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option maxRecDepth 2000
open scoped ContDiff
namespace Grad.AnnularHighGenerators
open Grad.AnnularVariational Grad.AnnularHighInverseOrbit Grad.AnnularCurrentInverse Grad.AnnularCurrentEnergy
open Grad.AnnularKernelOrbit Grad.AnnularCoupledOrbit Grad.AnnularReconstruction Grad.CartesianState
open Grad.AnnularOrbitGenerators Grad.AnnularInverseCalculus Grad.ClosedJets Grad.SourceCollarDivision
open Grad.GaugeCoefficients.Physical.Allocation

section IsometricComposition
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem isometricComposition_norm (inclusion : F →L[ℝ] G) (isometry : ∀ value, ‖inclusion value‖ = ‖value‖)
    (operator : E →L[ℝ] F) : ‖inclusion.comp operator‖ ≤ ‖operator‖ := by
  apply ContinuousLinearMap.opNorm_le_bound (inclusion.comp operator) (norm_nonneg operator)
  intro value
  change ‖inclusion (operator value)‖ ≤ ‖operator‖ * ‖value‖
  rw [isometry]
  exact operator.le_opNorm value

end IsometricComposition

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed Grad.AnnularCurrentEnergy.energyRealModule
  Grad.AnnularCurrentInverse.currentZero_normedGroup Grad.AnnularCurrentInverse.currentZero_seminormedGroup
  Grad.AnnularCurrentInverse.currentZero_realNormedSpace

variable (parameters : PhaseParameters) (L compact lower : ℝ) (positive : 0 < lower)
  (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
  (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L)) (state : RetainedInverseState parameters L compact)
  (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact)

theorem highSourceSolverOrbit_axis_norm (axis : Bool) (order : ℕ) (time : ℝ) :
    ‖iteratedDeriv order (fun parameter : ℝ =>
      highSourceSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        (parameter • axisVector axis)) time‖ ≤
    ‖orderedOrbitDerivative (List.replicate order axis)
      (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
      (time • axisVector axis)‖ := by
  have restriction := iteratedDeriv_axis_restriction
    (highSourceSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (highSourceSolverOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    axis 0 order time
  simp only [zero_add] at restriction
  let inclusion := annularZeroRealInclusion lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive
  let mapping := (ContinuousLinearMap.compL ℝ
    (annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    (annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
    (annularEnergySpace lower L positive)) inclusion
  have mapped := orderedOrbitDerivative_map
    (E := (annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ) →L[ℝ]
      annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive)
    (F := (annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ) →L[ℝ]
      annularEnergySpace lower L positive) mapping
    (currentHighInverseOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (currentHighInverseOrbit_contDiff parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small)
    (List.replicate order axis) (time • axisVector axis)
  exact (congrArg norm restriction).le.trans
    ((congrArg norm mapped).le.trans (isometricComposition_norm inclusion (fun _ => rfl) _))

include small in

theorem liftedTestFunctionalOrbit_zero_norm (tau : OrbitParameter) :
    ‖liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau‖ ≤ 5 := by
  apply ContinuousLinearMap.opNorm_le_bound
    (liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau) (by norm_num)
  intro field
  apply ContinuousLinearMap.opNorm_le_bound
    (liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0 tau field)
    (mul_nonneg (by norm_num) (norm_nonneg field))
  intro test
  rw [liftedTestFunctionalOrbit_pullback]
  have bound := ((currentHighTestFunctional parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (energyTranslation lower L positive (-tau) field)).le_opNorm
      (zeroTestTranslation lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive (-tau) test)).trans
    (mul_le_mul_of_nonneg_right
      (currentHighTestFunctional_norm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
        (energyTranslation lower L positive (-tau) field)) (norm_nonneg _))
  simpa only [energyTranslation_norm, zeroTestTranslation_norm] using bound

theorem liftedTestFunctionalOrbit_iteratedDeriv (axis : Bool) (order : ℕ) (time : ℝ) :
    iteratedDeriv order (fun parameter : ℝ =>
      liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
        (parameter • axisVector axis)) time =
    liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
      (if axis then 0 else order) (if axis then order else 0) (time • axisVector axis) :=
  iteratedDeriv_jet_axis
    (E := annularEnergySpace lower L positive →L[ℝ]
      annularInnerZero lower L positive (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ)
    (liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    (liftedTestFunctionalOrbitJet_hasFDerivAt parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state)
    axis order time

/-- All constants are chosen before the inner radius and retained state.
Positive orders retain one B_(8+j); order zero uses the original norm 32. -/
theorem highSourceSolverOrbit_axis_bound (parameters : PhaseParameters) (L compact : ℝ)
    (axis : Bool) (order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
        (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
        (state : RetainedInverseState parameters L compact)
        (small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact) (time : ℝ),
      ‖iteratedDeriv order (fun parameter : ℝ =>
        highSourceSolverOrbit parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small
          (parameter • axisVector axis)) time‖ ≤
        constant * positiveJetBudget
          (fun index => physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + index)) order := by
  by_cases zero : order = 0
  · subst order
    refine ⟨32, by norm_num, ?_⟩
    intro lower positive lowerHalf lengthPositive widthHalf widthLength state small time
    have bound := (highSourceSolverOrbit_axis_norm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small axis 0 time).trans
      (currentHighInverseOrbit_norm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small (time • axisVector axis))
    simpa [positiveJetBudget] using bound
  obtain ⟨constant, nonnegative, estimate⟩ := currentHighInverseOrbit_positive_ordered_oneHigh parameters L compact
    (List.replicate order axis) (by simpa using zero)
  refine ⟨constant, nonnegative, ?_⟩
  intro lower positive lowerHalf lengthPositive widthHalf widthLength state small time
  have bound := (highSourceSolverOrbit_axis_norm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small axis order time).trans
    (estimate lower positive lowerHalf lengthPositive widthHalf widthLength state small (time • axisVector axis))
  simpa only [positiveJetBudget, if_neg zero, List.length_replicate] using bound

/-- Fixed radius-independent constants for the actual full test-functional axis jets. -/
def liftedFunctionalAxisConstant (parameters : PhaseParameters) (L compact : ℝ) (axis : Bool) (order : ℕ) : ℝ :=
  if order = 0 then 5 else actualHighJetConstant parameters L compact (if axis then 0 else order) (if axis then order else 0)

theorem liftedFunctionalAxisConstant_nonnegative (parameters : PhaseParameters) (L compact : ℝ) (axis : Bool) (order : ℕ) :
    0 ≤ liftedFunctionalAxisConstant parameters L compact axis order := by
  by_cases zero : order = 0
  · simp only [liftedFunctionalAxisConstant, if_pos zero]
    norm_num
  · rw [liftedFunctionalAxisConstant, if_neg zero]
    exact actualHighJetConstant_nonnegative parameters L compact _ _

include small in
theorem liftedFunctionalAxisConstant_bound (axis : Bool) (order : ℕ) (time : ℝ) :
    ‖iteratedDeriv order (fun parameter : ℝ =>
      liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
        (parameter • axisVector axis)) time‖ ≤
      liftedFunctionalAxisConstant parameters L compact axis order * positiveJetBudget
        (fun index => physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + index)) order := by
  by_cases zero : order = 0
  · subst order
    have bound := liftedTestFunctionalOrbit_zero_norm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small (time • axisVector axis)
    simpa only [iteratedDeriv_zero, liftedFunctionalAxisConstant, positiveJetBudget, ite_true, mul_one] using bound
  have sum : (if axis then 0 else order) + (if axis then order else 0) = order := by cases axis <;> simp
  have orderPositive : 0 < (if axis then 0 else order) + (if axis then order else 0) := by rw [sum]; omega
  have actual := liftedTestFunctionalOrbit_iteratedDeriv parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state axis order time
  have full := (currentHighFormOrbitJet_oneHigh parameters L compact (if axis then 0 else order) (if axis then order else 0) orderPositive).choose_spec.2
    lower positive lowerHalf lengthPositive widthHalf widthLength state (time • axisVector axis)
  have bound := (liftedTestFunctionalOrbitJet_norm parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state
    (if axis then 0 else order) (if axis then order else 0) (time • axisVector axis)).trans full
  apply (congrArg norm actual).le.trans
  simpa only [liftedFunctionalAxisConstant, positiveJetBudget, if_neg zero, actualHighJetConstant, dif_pos orderPositive,
    AnnularReconstructionState.errorBudget, sum, dif_pos (Nat.pos_of_ne_zero zero), show 1 + order + 7 = 8 + order by omega] using bound

/-- The nonzero-incoming test functional obeys the same one-high axis
estimate, with uniformly bounded order zero on the original ball. -/
theorem liftedTestFunctionalOrbit_axis_bound (parameters : PhaseParameters) (L compact : ℝ)
    (axis : Bool) (order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (lengthPositive : 0 < L)
        (widthHalf : parameters.gamma ≤ 1 / 2) (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
        (state : RetainedInverseState parameters L compact)
        (_small : state.val.errorBudget 1 ≤ currentHighPrimitiveRadius parameters L compact) (time : ℝ),
      ‖iteratedDeriv order (fun parameter : ℝ =>
        liftedTestFunctionalOrbitJet parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state 0 0
          (parameter • axisVector axis)) time‖ ≤
        constant * positiveJetBudget
          (fun index => physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon (8 + index)) order :=
  ⟨liftedFunctionalAxisConstant parameters L compact axis order,
    liftedFunctionalAxisConstant_nonnegative parameters L compact axis order,
    fun lower positive lowerHalf lengthPositive widthHalf widthLength state small time =>
      liftedFunctionalAxisConstant_bound parameters L compact lower positive lowerHalf lengthPositive widthHalf widthLength state small axis order time⟩

end Grad.AnnularHighGenerators
