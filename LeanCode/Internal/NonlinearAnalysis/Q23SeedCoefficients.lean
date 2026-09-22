import SeedParameterFamily

noncomputable section

set_option maxHeartbeats 1600000

open Set
open scoped BigOperators ContDiff ENNReal Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.Constraints.Seed
open Grad.GaugeCoefficients.Algebra

/-! The accepted seed package proves smoothness in each weighted `ℓ1`
coefficient space.  This file extracts one grade-independent, cellwise
derivative family and proves that it is represented by those Banach-space
derivatives at every grade. -/

/-- Evaluation of a weighted seed sequence at one cell, as a real continuous
linear map. -/
def seedWeightedCellEval (cell : ℤ) :
    WeightedSequence →L[ℝ] OperatorValue 2 2 :=
  lp.evalCLM ℝ (fun _ : ℤ => OperatorValue 2 2) 1 cell

/-- Complex scalar multiplication on operator values, regarded as a real
continuous linear map. -/
def seedOperatorScalar (scalar : ℂ) :
    OperatorValue 2 2 →L[ℝ] OperatorValue 2 2 :=
  (scalar • ContinuousLinearMap.id ℂ (OperatorValue 2 2)).restrictScalars ℝ

@[simp]
theorem seedOperatorScalar_apply (scalar : ℂ) (value : OperatorValue 2 2) :
    seedOperatorScalar scalar value = scalar • value := rfl

theorem sequenceWeight_pos (phase : PhaseParameters) (grade : ℕ) (cell : ℤ) :
    0 < sequenceWeight phase grade cell := by
  unfold sequenceWeight
  exact mul_pos (Real.exp_pos _)
    (pow_pos (by rw [cellPolynomialWeight_formula]; positivity) _)

/-- The literal pointwise finite-parameter derivative of a seed coefficient.
It is independent of the analytic grade. -/
def seedCellParameterDerivative (order : ℕ) (kind : Fin 3)
    (parameter : Seed.Parameters) (directions : Fin order → Seed.Parameters)
    (cell : ℤ) : OperatorValue 2 2 :=
  iteratedFDeriv ℝ order (fun p => Seed.actualCells kind p cell) parameter directions

theorem actualCells_eq_unweightedFamily (phase : PhaseParameters) (grade : ℕ)
    (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (cell : ℤ) :
    Seed.actualCells kind parameter cell =
      seedOperatorScalar ((sequenceWeight phase grade cell : ℂ)⁻¹)
        (seedWeightedCellEval cell (Seed.weightedSeedFamilies phase grade kind parameter)) := by
  rw [seedOperatorScalar_apply]
  change Seed.actualCells kind parameter cell =
    ((sequenceWeight phase grade cell : ℂ)⁻¹) •
      Seed.weightedSeedFamilies phase grade kind parameter cell
  rw [Seed.weightedSeedFamilies_cells phase grade kind parameter inside cell, smul_smul]
  rw [inv_mul_cancel₀]
  · exact (one_smul ℂ (Seed.actualCells kind parameter cell)).symm
  · exact Complex.ofReal_ne_zero.mpr (sequenceWeight_pos phase grade cell).ne'

/-- Each literal cell coefficient is genuinely smooth in the finite seed
parameters on the exact admissible domain. -/
theorem actualCells_contDiffOn (phase : PhaseParameters) (grade : ℕ)
    (kind : Fin 3) (cell : ℤ) :
    ContDiffOn ℝ ∞ (fun parameter => Seed.actualCells kind parameter cell)
      Seed.parameterDomain := by
  let evaluation := seedWeightedCellEval cell
  let unweight := seedOperatorScalar ((sequenceWeight phase grade cell : ℂ)⁻¹)
  have smoothWeighted := Seed.weightedSeedFamilies_contDiffOn phase grade kind
  have smoothEvaluation : ContDiffOn ℝ ∞
      (evaluation ∘ Seed.weightedSeedFamilies phase grade kind) Seed.parameterDomain :=
    evaluation.contDiff.comp_contDiffOn smoothWeighted
  have smoothUnweighted : ContDiffOn ℝ ∞
      (unweight ∘ evaluation ∘ Seed.weightedSeedFamilies phase grade kind)
        Seed.parameterDomain :=
    unweight.contDiff.comp_contDiffOn smoothEvaluation
  apply smoothUnweighted.congr
  intro parameter inside
  exact actualCells_eq_unweightedFamily phase grade kind parameter inside cell

/-- The grade-`q` weighting of the grade-independent cellwise derivative is
literally evaluation of the accepted `ℓ1`-valued Fréchet derivative. -/
theorem weightedSeedFamilies_iteratedFDeriv_cell (phase : PhaseParameters)
    (grade order : ℕ) (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (cell : ℤ) :
    (iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
        parameter directions) cell =
      (sequenceWeight phase grade cell : ℂ) •
        seedCellParameterDerivative order kind parameter directions cell := by
  let evaluation := seedWeightedCellEval cell
  let weight := seedOperatorScalar (sequenceWeight phase grade cell : ℂ)
  have pointwise : Set.EqOn
      (evaluation ∘ Seed.weightedSeedFamilies phase grade kind)
      (weight ∘ fun p => Seed.actualCells kind p cell) Seed.parameterDomain := by
    intro p hp
    change Seed.weightedSeedFamilies phase grade kind p cell =
      (sequenceWeight phase grade cell : ℂ) • Seed.actualCells kind p cell
    exact Seed.weightedSeedFamilies_cells phase grade kind p hp cell
  have agreement := iteratedFDerivWithin_congr (𝕜 := ℝ) pointwise inside order
  rw [iteratedFDerivWithin_of_isOpen order Seed.parameterDomain_isOpen inside,
    iteratedFDerivWithin_of_isOpen order Seed.parameterDomain_isOpen inside] at agreement
  have weightedSmooth :=
    (Seed.weightedSeedFamilies_contDiffOn phase grade kind).contDiffAt
      (Seed.parameterDomain_isOpen.mem_nhds inside)
  have actualSmooth :=
    (actualCells_contDiffOn phase grade kind cell).contDiffAt
      (Seed.parameterDomain_isOpen.mem_nhds inside)
  have left := evaluation.iteratedFDeriv_comp_left weightedSmooth
    (i := order) (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  have right := weight.iteratedFDeriv_comp_left actualSmooth
    (i := order) (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  rw [left, right] at agreement
  have applied := congrArg (fun derivative => derivative directions) agreement
  change (iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
      parameter directions) cell =
    (sequenceWeight phase grade cell : ℂ) •
      iteratedFDeriv ℝ order (fun p => Seed.actualCells kind p cell)
        parameter directions at applied
  exact applied

/-- Every literal cellwise parameter derivative is an admissible multiplier
coefficient family at every analytic grade. -/
theorem seedCellParameterDerivative_summable (phase : PhaseParameters)
    (grade order : ℕ) (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    Summable (envelopeTerm phase grade
      (seedCellParameterDerivative order kind parameter directions)) := by
  let derivativeSequence : WeightedSequence :=
    iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
      parameter directions
  have normSummable : Summable (fun cell : ℤ => ‖derivativeSequence cell‖) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      (lp.memℓp derivativeSequence).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  apply normSummable.congr
  intro cell
  rw [weightedSeedFamilies_iteratedFDeriv_cell phase grade order kind parameter inside
    directions cell, Seed.weighted_norm]
  rfl

end Grad.NonlinearQuotientBounds
