import TameChartMaster

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The tower-level one-high estimate: per-term constants summed over the
finite term list, with the exact-once permutation transporting each term's
index list onto `range level`. -/

variable {parameters : PhaseParameters}

/-- One term against the range form. -/
theorem evalChartTerm_range_envelope_le (grade level : ℕ) {ballBound : ℝ}
    (ballNonneg : 0 ≤ ballBound) (ballLt : ballBound < 1) (term : ChartTermData)
    (membership : term ∈ chartTerms level) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (base : TangentCoefficient parameters)
      (directions : ℕ → TangentCoefficient parameters),
      tangentPlanarEnvelope 0 base ≤ ballBound →
      coefficientEnvelope grade (evalChartTerm base directions term) ≤
        constant * ((1 + tangentPlanarEnvelope grade base) *
            lowIndexProd directions (List.range level) +
          oneHighIndex grade directions (List.range level)) := by
  obtain ⟨constant, constant_nonneg, bound⟩ :=
    eval_structure_envelope_le grade ballNonneg ballLt term.gOrder term.pairs term.singles
  refine ⟨constant, constant_nonneg, ?_⟩
  intro base directions ball
  have perm : (termIndexList term).Perm (List.range level) :=
    chartTerms_perm level term membership
  have structure_eq : (⟨term.gOrder, term.pairs, term.singles⟩ : ChartTermData) = term := rfl
  have graded := (bound base directions ball).1
  rw [structure_eq] at graded
  have index_eq : term.singles ++ term.pairs.flatMap (fun pair => [pair.1, pair.2]) =
      termIndexList term := rfl
  rw [index_eq, lowIndexProd_perm directions perm, oneHighIndex_perm grade directions perm]
    at graded
  exact graded

/-- The tower level against the range form. -/
theorem chartTower_range_envelope_le (grade level : ℕ) {ballBound : ℝ}
    (ballNonneg : 0 ≤ ballBound) (ballLt : ballBound < 1) :
    ∃ constant : ℝ, 0 ≤ constant ∧
    ∀ (base : TangentCoefficient parameters)
      (directions : ℕ → TangentCoefficient parameters),
      tangentPlanarEnvelope 0 base ≤ ballBound →
      coefficientEnvelope grade (chartTower level base directions) ≤
        constant * ((1 + tangentPlanarEnvelope grade base) *
            lowIndexProd directions (List.range level) +
          oneHighIndex grade directions (List.range level)) := by
  have shape_nonneg : ∀ (base : TangentCoefficient parameters)
      (directions : ℕ → TangentCoefficient parameters),
      0 ≤ (1 + tangentPlanarEnvelope grade base) *
          lowIndexProd directions (List.range level) +
        oneHighIndex grade directions (List.range level) := by
    intro base directions
    have := tangentPlanarEnvelope_nonneg grade base
    have := lowIndexProd_nonneg directions (List.range level)
    have := oneHighIndex_nonneg grade directions (List.range level)
    positivity
  -- Sum the per-term constants along the term list.
  suffices general : ∀ terms : List ChartTermData,
      (∀ term ∈ terms, term ∈ chartTerms level) →
      ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : TangentCoefficient parameters)
        (directions : ℕ → TangentCoefficient parameters),
        tangentPlanarEnvelope 0 base ≤ ballBound →
        coefficientEnvelope grade ((terms.map (evalChartTerm base directions)).sum) ≤
          constant * ((1 + tangentPlanarEnvelope grade base) *
              lowIndexProd directions (List.range level) +
            oneHighIndex grade directions (List.range level)) by
    obtain ⟨constant, constant_nonneg, bound⟩ :=
      general (chartTerms level) (fun _ membership => membership)
    exact ⟨constant, constant_nonneg, fun base directions ball => bound base directions ball⟩
  intro terms
  induction terms with
  | nil =>
    intro _
    refine ⟨0, le_rfl, ?_⟩
    intro base directions _
    rw [List.map_nil, List.sum_nil, coefficientEnvelope_zero, zero_mul]
  | cons head tail inductive_step =>
    intro all_membership
    obtain ⟨headConstant, headNonneg, headBound⟩ :=
      evalChartTerm_range_envelope_le grade level ballNonneg ballLt head
        (all_membership head List.mem_cons_self)
    obtain ⟨tailConstant, tailNonneg, tailBound⟩ := inductive_step
      (fun term membership => all_membership term (List.mem_cons_of_mem head membership))
    refine ⟨headConstant + tailConstant, by linarith, ?_⟩
    intro base directions ball
    rw [List.map_cons, List.sum_cons]
    calc coefficientEnvelope grade (evalChartTerm base directions head +
          (tail.map (evalChartTerm base directions)).sum)
        ≤ coefficientEnvelope grade (evalChartTerm base directions head) +
          coefficientEnvelope grade ((tail.map (evalChartTerm base directions)).sum) :=
          coefficientEnvelope_add_le grade _ _
      _ ≤ headConstant * ((1 + tangentPlanarEnvelope grade base) *
            lowIndexProd directions (List.range level) +
            oneHighIndex grade directions (List.range level)) +
          tailConstant * ((1 + tangentPlanarEnvelope grade base) *
            lowIndexProd directions (List.range level) +
            oneHighIndex grade directions (List.range level)) :=
          add_le_add (headBound base directions ball) (tailBound base directions ball)
      _ = _ := by ring

end Grad.NonlinearQuotientBounds
