import SeedParameterCoefficients
import SeedSequenceDerivative
import Mathlib.Analysis.Normed.Group.Bounded

noncomputable section

set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 800000

open scoped ContDiff BigOperators

namespace Grad.Constraints.Seed

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Neumann.Regularity Grad.GaugeCoefficients.Physical.Frame

local instance seedFamilyComplexSpace (phase : PhaseParameters) (grade : ℕ) :
    NormedSpace ℂ (Coefficient 1 phase.sigma0 phase.gamma 1 grade 2 2) := inferInstance
local instance seedFamilyRealSpace (phase : PhaseParameters) (grade : ℕ) :
    NormedSpace ℝ (Coefficient 1 phase.sigma0 phase.gamma 1 grade 2 2) := inferInstance

def weightedSeedFamilies (phase : PhaseParameters) (grade : ℕ) (kind : Fin 3) (parameter : Parameters) : WeightedSequence :=
  if kind = 0 then coefficientSequenceCLM phase grade
    (seedMatrixDeviationCoefficient (seedAdmissible phase) grade (parameter 0) (parameter 1) (parameter 2) (parameter 3))
  else if kind = 1 then coefficientSequenceCLM phase grade (inverseDeviationCoefficient phase grade parameter)
  else sequenceDerivativeCLM (coefficientSequenceCLM phase (grade + 1)
    (seedMatrixDeviationCoefficient (seedAdmissible phase) (grade + 1) (parameter 0) (parameter 1) (parameter 2) (parameter 3)))

theorem weightedSeedFamilies_cells (phase : PhaseParameters) (grade : ℕ) (kind : Fin 3) (parameter : Parameters)
    (inside : parameter ∈ parameterDomain) (cell : ℤ) :
    weightedSeedFamilies phase grade kind parameter cell =
      (sequenceWeight phase grade cell : ℂ) • actualCells kind parameter cell := by
  fin_cases kind
  · change coefficientSequenceCLM phase grade _ cell = _
    rw [coefficientSequenceCLM_apply, seedMatrixDeviation_cell]
    rfl
  · change coefficientSequenceCLM phase grade _ cell = _
    rw [coefficientSequenceCLM_apply, inverseDeviation_cell phase grade parameter inside]
    rfl
  · change sequenceDerivativeCLM (coefficientSequenceCLM phase (grade + 1) _) cell = _
    rw [sequenceDerivativeCLM_apply, coefficientSequenceCLM_apply, seedMatrixDeviation_cell,
      sequenceDerivative_weight]
    rfl

theorem weightedSeedFamilies_contDiffOn (phase : PhaseParameters) (grade : ℕ) (kind : Fin 3) :
    ContDiffOn ℝ ∞ (weightedSeedFamilies phase grade kind) parameterDomain := by
  fin_cases kind
  · exact ((coefficientSequenceCLM phase grade).restrictScalars ℝ).contDiff.comp_contDiffOn
      (seedDeviation_contDiffOn phase grade)
  · exact ((coefficientSequenceCLM phase grade).restrictScalars ℝ).contDiff.comp_contDiffOn
      (inverseDeviation_contDiffOn phase grade)
  · exact (sequenceDerivativeCLM.restrictScalars ℝ).contDiff.comp_contDiffOn
      (((coefficientSequenceCLM phase (grade + 1)).restrictScalars ℝ).contDiff.comp_contDiffOn
        (seedDeviation_contDiffOn phase (grade + 1)))

theorem parameterDomain_isOpen : IsOpen parameterDomain :=
  isOpen_lt (continuous_apply 0).abs continuous_const

theorem actualSeedParameters : ParameterGoal := by
  intro phase grade
  refine ⟨weightedSeedFamilies phase grade, weightedSeedFamilies_cells phase grade,
    weightedSeedFamilies_contDiffOn phase grade, ?_⟩
  intro compact isCompact subset order
  have each (kind : Fin 3) : ∃ constant : ℝ, ∀ parameter ∈ compact,
      ‖iteratedFDeriv ℝ order (weightedSeedFamilies phase grade kind) parameter‖ ≤ constant := by
    apply isCompact.exists_bound_of_continuousOn
    exact (ContinuousOn.continuousOn_iteratedFDeriv (k := order) (weightedSeedFamilies_contDiffOn phase grade kind)
      parameterDomain_isOpen (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).mono subset
  choose constants bounds using each
  refine ⟨∑ kind : Fin 3, max 0 (constants kind), Finset.sum_nonneg (fun _ _ => le_max_left _ _), ?_⟩
  intro kind parameter inside
  apply (bounds kind parameter inside).trans
  apply (le_max_right 0 (constants kind)).trans
  exact Finset.single_le_sum (f := fun index : Fin 3 => max 0 (constants index))
    (s := Finset.univ) (fun _ _ => le_max_left _ _) (Finset.mem_univ kind)

theorem actualSeed : SeedGoal := ⟨actualSeedAlgebra, actualSeedQuantitative, actualSeedParameters⟩

end Grad.Constraints.Seed
