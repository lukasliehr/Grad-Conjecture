import TameTangentDot

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The chart derivative tower grammar: each term of the `j`-th derivative
of `a(τ) = F(τ·τ/2)` is a shifted root series factor times pair and single
dot factors; differentiation maps a term to its children, one per factor
that can absorb the new direction. -/

variable {parameters : PhaseParameters}

/-- One formal term of the chart derivative tower. -/
structure ChartTermData where
  gOrder : ℕ
  pairs : List (ℕ × ℕ)
  singles : List ℕ
  deriving Repr

/-- The children created by replacing one single factor, keeping order. -/
noncomputable def singlesChildren (newIndex gOrder : ℕ) (pairs : List (ℕ × ℕ)) :
    List ℕ → List ChartTermData
  | [] => []
  | index :: rest =>
      ⟨gOrder, (newIndex, index) :: pairs, rest⟩ ::
        (singlesChildren newIndex gOrder pairs rest).map
          (fun child => ⟨child.gOrder, child.pairs, index :: child.singles⟩)

/-- All children of one term under differentiation along the new index. -/
def chartTermChildren (newIndex : ℕ) (term : ChartTermData) : List ChartTermData :=
  ⟨term.gOrder + 1, term.pairs, newIndex :: term.singles⟩ ::
    singlesChildren newIndex term.gOrder term.pairs term.singles

/-- The complete term list of the `j`-th tower level. -/
noncomputable def chartTerms : ℕ → List ChartTermData
  | 0 => [⟨0, [], []⟩]
  | level + 1 => (chartTerms level).flatMap (chartTermChildren level)

/-- Evaluation of one term at a base and a direction assignment. -/
def evalChartTerm (base : TangentCoefficient parameters)
    (directions : ℕ → TangentCoefficient parameters) (term : ChartTermData) :
    TameCoefficient parameters :=
  tameRootShifted term.gOrder (tangentQuadratic base) *
    ((term.pairs.map (fun pair => tangentDot (directions pair.1) (directions pair.2))).prod *
      (term.singles.map (fun index => tangentDot base (directions index))).prod)

/-- The `j`-th chart tower level. -/
def chartTower (level : ℕ) (base : TangentCoefficient parameters)
    (directions : ℕ → TangentCoefficient parameters) : TameCoefficient parameters :=
  ((chartTerms level).map (evalChartTerm base directions)).sum

theorem chartTower_zero (base : TangentCoefficient parameters)
    (directions : ℕ → TangentCoefficient parameters) :
    chartTower 0 base directions = tameRootShifted 0 (tangentQuadratic base) := by
  simp [chartTower, chartTerms, evalChartTerm]

/-! ### The index invariant -/

/-- All direction indices of a term lie strictly below the bound. -/
def TermIndicesBelow (bound : ℕ) (term : ChartTermData) : Prop :=
  (∀ pair ∈ term.pairs, pair.1 < bound ∧ pair.2 < bound) ∧
    ∀ index ∈ term.singles, index < bound

theorem termIndicesBelow_mono {lower upper : ℕ} (le : lower ≤ upper)
    {term : ChartTermData} (below : TermIndicesBelow lower term) :
    TermIndicesBelow upper term := by
  obtain ⟨pairs_below, singles_below⟩ := below
  exact ⟨fun pair mem => ⟨lt_of_lt_of_le (pairs_below pair mem).1 le,
      lt_of_lt_of_le (pairs_below pair mem).2 le⟩,
    fun index mem => lt_of_lt_of_le (singles_below index mem) le⟩

theorem singlesChildren_indices (newIndex gOrder : ℕ) (pairs : List (ℕ × ℕ))
    (bound : ℕ) (new_lt : newIndex < bound)
    (pairs_below : ∀ pair ∈ pairs, pair.1 < bound ∧ pair.2 < bound) :
    ∀ singles : List ℕ, (∀ index ∈ singles, index < bound) →
    ∀ child ∈ singlesChildren newIndex gOrder pairs singles, TermIndicesBelow bound child := by
  intro singles
  induction singles with
  | nil =>
    intro _ child membership
    exact absurd membership (List.not_mem_nil)
  | cons head rest inductive_step =>
    intro singles_below child membership
    rw [singlesChildren] at membership
    rcases List.mem_cons.mp membership with head_case | tail_case
    · subst head_case
      refine ⟨?_, ?_⟩
      · intro pair pair_mem
        rcases List.mem_cons.mp pair_mem with new_pair | old_pair
        · subst new_pair
          exact ⟨new_lt, singles_below head (List.mem_cons_self)⟩
        · exact pairs_below pair old_pair
      · intro index index_mem
        exact singles_below index (List.mem_cons_of_mem head index_mem)
    · obtain ⟨inner, inner_mem, inner_eq⟩ := List.mem_map.mp tail_case
      have inner_below := inductive_step
        (fun index mem => singles_below index (List.mem_cons_of_mem head mem))
        inner inner_mem
      subst inner_eq
      refine ⟨inner_below.1, ?_⟩
      intro index index_mem
      rcases List.mem_cons.mp index_mem with head_eq | rest_mem
      · subst head_eq
        exact singles_below index (List.mem_cons_self)
      · exact inner_below.2 index rest_mem

theorem chartTermChildren_indices (newIndex bound : ℕ) (new_lt : newIndex < bound)
    {term : ChartTermData} (below : TermIndicesBelow bound term) :
    ∀ child ∈ chartTermChildren newIndex term, TermIndicesBelow bound child := by
  intro child membership
  rw [chartTermChildren] at membership
  rcases List.mem_cons.mp membership with g_case | singles_case
  · subst g_case
    refine ⟨below.1, ?_⟩
    intro index index_mem
    rcases List.mem_cons.mp index_mem with new_eq | old_mem
    · subst new_eq
      exact new_lt
    · exact below.2 index old_mem
  · exact singlesChildren_indices newIndex term.gOrder term.pairs bound new_lt
      below.1 term.singles below.2 child singles_case

/-- Every term of the `j`-th level references only directions below `j`. -/
theorem chartTerms_indices : ∀ level : ℕ, ∀ term ∈ chartTerms level,
    TermIndicesBelow level term := by
  intro level
  induction level with
  | zero =>
    intro term membership
    rw [chartTerms] at membership
    rcases List.mem_cons.mp membership with base_case | absurd_case
    · subst base_case
      exact ⟨fun pair mem => absurd mem (List.not_mem_nil),
        fun index mem => absurd mem (List.not_mem_nil)⟩
    · exact absurd absurd_case (List.not_mem_nil)
  | succ smaller inductive_step =>
    intro term membership
    rw [chartTerms] at membership
    obtain ⟨parent, parent_mem, child_mem⟩ := List.mem_flatMap.mp membership
    have parent_below := termIndicesBelow_mono (Nat.le_succ smaller)
      (inductive_step parent parent_mem)
    exact chartTermChildren_indices smaller (smaller + 1) (Nat.lt_succ_self smaller)
      parent_below term child_mem

/-- Evaluation only depends on the directions the term references. -/
theorem evalChartTerm_congr (base : TangentCoefficient parameters)
    {firstDirections secondDirections : ℕ → TangentCoefficient parameters}
    {bound : ℕ} {term : ChartTermData} (below : TermIndicesBelow bound term)
    (agree : ∀ index < bound, firstDirections index = secondDirections index) :
    evalChartTerm base firstDirections term = evalChartTerm base secondDirections term := by
  rw [evalChartTerm, evalChartTerm]
  congr 1
  congr 1
  · congr 1
    apply List.map_congr_left
    intro pair pair_mem
    rw [agree pair.1 (below.1 pair pair_mem).1, agree pair.2 (below.1 pair pair_mem).2]
  · congr 1
    apply List.map_congr_left
    intro index index_mem
    rw [agree index (below.2 index index_mem)]

/-- The tower level only depends on the directions strictly below it. -/
theorem chartTower_congr (level : ℕ) (base : TangentCoefficient parameters)
    {firstDirections secondDirections : ℕ → TangentCoefficient parameters}
    (agree : ∀ index < level, firstDirections index = secondDirections index) :
    chartTower level base firstDirections = chartTower level base secondDirections := by
  rw [chartTower, chartTower]
  congr 1
  apply List.map_congr_left
  intro term term_mem
  exact evalChartTerm_congr base (chartTerms_indices level term term_mem) agree

end Grad.NonlinearQuotientBounds
