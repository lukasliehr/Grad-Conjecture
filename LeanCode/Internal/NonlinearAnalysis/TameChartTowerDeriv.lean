import TameChartTerms

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! Genuineness of the chart derivative tower: each level's curve along a
new tangential direction has the next level as genuine envelope derivative.
The proof runs term by term through the product calculus, matching the
formal children exactly. -/

variable {parameters : PhaseParameters}

/-- The list sum rule for envelope derivatives. -/
theorem hasEnvDerivAt_list_sum {Item : Type}
    (items : List Item) (curve : Item → ℝ → TameCoefficient parameters)
    (derivative : Item → TameCoefficient parameters)
    (each : ∀ item ∈ items, HasEnvDerivAt (curve item) (derivative item)) :
    HasEnvDerivAt (fun t => (items.map (fun item => curve item t)).sum)
      ((items.map derivative).sum) := by
  induction items with
  | nil =>
    refine HasEnvDerivAt.congr_derivative
      (HasEnvDerivAt.congr_curve (hasEnvDerivAt_const (0 : TameCoefficient parameters))
        (fun t => ?_)) ?_
    · simp
    · simp
  | cons head tail inductive_step =>
    have head_deriv := each head List.mem_cons_self
    have tail_deriv := inductive_step
      (fun item membership => each item (List.mem_cons_of_mem head membership))
    refine HasEnvDerivAt.congr_derivative
      (HasEnvDerivAt.congr_curve (head_deriv.add tail_deriv) (fun t => ?_)) ?_
    · simp
    · simp

/-- The affine single-factor curve. -/
theorem tangentDot_curve_affine (base direction : TangentCoefficient parameters)
    (single : TangentCoefficient parameters) (t : ℝ) :
    tangentDot (base + (t : ℂ) • direction) single =
      tangentDot base single + (t : ℂ) • tangentDot direction single := by
  rw [tangentDot_add_left, tangentDot_smul_left]

/-- The recursive derivative of the singles product. -/
noncomputable def singlesProdDerivative (base : TangentCoefficient parameters)
    (directions : ℕ → TangentCoefficient parameters) (newIndex : ℕ) :
    List ℕ → TameCoefficient parameters
  | [] => 0
  | index :: rest =>
      tangentDot (directions newIndex) (directions index) *
        (rest.map (fun other => tangentDot base (directions other))).prod +
      tangentDot base (directions index) *
        singlesProdDerivative base directions newIndex rest

/-- The singles product rule. -/
theorem singles_prod_hasEnvDerivAt (base : TangentCoefficient parameters)
    (directions : ℕ → TangentCoefficient parameters) (newIndex : ℕ) :
    ∀ singles : List ℕ,
    HasEnvDerivAt (fun t => ((singles.map (fun index =>
        tangentDot (base + (t : ℂ) • directions newIndex) (directions index)))).prod)
      (singlesProdDerivative base directions newIndex singles) := by
  intro singles
  induction singles with
  | nil =>
    refine HasEnvDerivAt.congr_derivative
      (HasEnvDerivAt.congr_curve (hasEnvDerivAt_const (1 : TameCoefficient parameters))
        (fun t => ?_)) ?_
    · simp
    · simp [singlesProdDerivative]
  | cons head tail inductive_step =>
    have head_deriv : HasEnvDerivAt (fun t =>
        tangentDot (base + (t : ℂ) • directions newIndex) (directions head))
        (tangentDot (directions newIndex) (directions head)) := by
      apply (hasEnvDerivAt_affine (tangentDot base (directions head))
        (tangentDot (directions newIndex) (directions head))).congr_curve
      intro t
      rw [tangentDot_curve_affine]
    refine HasEnvDerivAt.congr_derivative
      (HasEnvDerivAt.congr_curve (head_deriv.mul inductive_step) (fun t => ?_)) ?_
    · simp
    · simp only [singlesProdDerivative]
      congr 2
      · apply congrArg
        apply List.map_congr_left
        intro other _
        rw [tangentDot_curve_affine, Complex.ofReal_zero, zero_smul, add_zero]
      · rw [tangentDot_curve_affine, Complex.ofReal_zero, zero_smul, add_zero]

/-- Multiplying a mapped list sum on the left. -/
theorem list_sum_map_mul_left {Item : Type} (items : List Item)
    (factor : TameCoefficient parameters)
    (value : Item → TameCoefficient parameters) :
    ((items.map (fun item => factor * value item)).sum) =
      factor * (items.map value).sum := by
  induction items with
  | nil => simp
  | cons head tail inductive_step =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, inductive_step, mul_add]

/-- The children evaluation of the singles replacements. -/
theorem singlesChildren_eval_sum (base : TangentCoefficient parameters)
    (directions : ℕ → TangentCoefficient parameters) (newIndex gOrder : ℕ)
    (pairs : List (ℕ × ℕ)) :
    ∀ singles : List ℕ,
    (((singlesChildren newIndex gOrder pairs singles).map
        (evalChartTerm base directions)).sum) =
      tameRootShifted gOrder (tangentQuadratic base) *
        ((pairs.map (fun pair =>
          tangentDot (directions pair.1) (directions pair.2))).prod *
          singlesProdDerivative base directions newIndex singles) := by
  intro singles
  induction singles with
  | nil =>
    simp [singlesChildren, singlesProdDerivative]
  | cons head tail inductive_step =>
    rw [singlesChildren, List.map_cons, List.sum_cons]
    have head_eval : evalChartTerm base directions
        ⟨gOrder, (newIndex, head) :: pairs, tail⟩ =
        tameRootShifted gOrder (tangentQuadratic base) *
          ((pairs.map (fun pair =>
            tangentDot (directions pair.1) (directions pair.2))).prod *
            (tangentDot (directions newIndex) (directions head) *
              (tail.map (fun other => tangentDot base (directions other))).prod)) := by
      simp only [evalChartTerm, List.map_cons, List.prod_cons]
      ring
    have mapped_eval : (((singlesChildren newIndex gOrder pairs tail).map
        (fun child => evalChartTerm base directions
          ⟨child.gOrder, child.pairs, head :: child.singles⟩)).sum) =
        tangentDot base (directions head) *
          (((singlesChildren newIndex gOrder pairs tail).map
            (evalChartTerm base directions)).sum) := by
      rw [← list_sum_map_mul_left]
      congr 1
      apply List.map_congr_left
      intro child _
      simp only [evalChartTerm, List.map_cons, List.prod_cons]
      ring
    rw [List.map_map]
    have composed : ((singlesChildren newIndex gOrder pairs tail).map
        (evalChartTerm base directions ∘ fun child =>
          (⟨child.gOrder, child.pairs, head :: child.singles⟩ : ChartTermData))).sum =
        (((singlesChildren newIndex gOrder pairs tail).map
          (fun child => evalChartTerm base directions
            ⟨child.gOrder, child.pairs, head :: child.singles⟩)).sum) := rfl
    rw [composed, mapped_eval, head_eval, inductive_step]
    simp only [singlesProdDerivative]
    ring

/-- Per-term genuineness: the curve of one term has the sum of its children
as genuine envelope derivative. -/
theorem evalChartTerm_hasEnvDerivAt (base : TangentCoefficient parameters)
    (directions : ℕ → TangentCoefficient parameters) (newIndex : ℕ)
    (small : tangentPlanarEnvelope 0 base < 1) (term : ChartTermData) :
    HasEnvDerivAt (fun t => evalChartTerm (base + (t : ℂ) • directions newIndex)
        directions term)
      (((chartTermChildren newIndex term).map (evalChartTerm base directions)).sum) := by
  have quadratic_small := tangentQuadratic_small small
  have g_deriv : HasEnvDerivAt (fun t => tameRootShifted term.gOrder
      (tangentQuadratic (base + (t : ℂ) • directions newIndex)))
      (tameRootShifted (term.gOrder + 1) (tangentQuadratic base) *
        tangentDot base (directions newIndex)) := by
    apply (hasEnvDerivAt_tameRootShifted term.gOrder quadratic_small
      (tangentDot base (directions newIndex))
      (((2 : ℂ))⁻¹ • tangentDot (directions newIndex) (directions newIndex))).congr_curve
    intro t
    rw [tangentQuadratic_curve]
  have pairs_deriv : HasEnvDerivAt (fun _ : ℝ => (term.pairs.map (fun pair =>
      tangentDot (directions pair.1) (directions pair.2))).prod)
      (0 : TameCoefficient parameters) := hasEnvDerivAt_const _
  have singles_deriv := singles_prod_hasEnvDerivAt base directions newIndex term.singles
  refine HasEnvDerivAt.congr_derivative
    (HasEnvDerivAt.congr_curve (g_deriv.mul (pairs_deriv.mul singles_deriv))
      (fun t => ?_)) ?_
  · simp only [evalChartTerm]
  · -- Identify the product-rule derivative with the children sum.
    have base_zero : base + ((0 : ℝ) : ℂ) • directions newIndex = base := by
      rw [Complex.ofReal_zero, zero_smul, add_zero]
    simp only [chartTermChildren, List.map_cons, List.sum_cons]
    rw [singlesChildren_eval_sum, base_zero]
    have g_child_eval : evalChartTerm base directions
        ⟨term.gOrder + 1, term.pairs, newIndex :: term.singles⟩ =
        tameRootShifted (term.gOrder + 1) (tangentQuadratic base) *
          ((term.pairs.map (fun pair =>
            tangentDot (directions pair.1) (directions pair.2))).prod *
            (tangentDot base (directions newIndex) *
              (term.singles.map (fun index =>
                tangentDot base (directions index))).prod)) := by
      simp only [evalChartTerm, List.map_cons, List.prod_cons]
    rw [g_child_eval, zero_mul, zero_add]
    ring

/-- Flattened children sums assemble the next level. -/
theorem chartTerms_children_sum (level : ℕ) (base : TangentCoefficient parameters)
    (directions : ℕ → TangentCoefficient parameters) :
    ((chartTerms level).map (fun term =>
      ((chartTermChildren level term).map (evalChartTerm base directions)).sum)).sum =
      chartTower (level + 1) base directions := by
  rw [chartTower]
  show ((chartTerms level).map (fun term =>
      ((chartTermChildren level term).map (evalChartTerm base directions)).sum)).sum =
    (((chartTerms level).flatMap (chartTermChildren level)).map
      (evalChartTerm base directions)).sum
  induction chartTerms level with
  | nil => simp
  | cons head tail inductive_step =>
    rw [List.map_cons, List.sum_cons, List.flatMap_cons, List.map_append, List.sum_append,
      inductive_step]

/-- The tower step: each level's curve along the newest direction has the
next level as genuine envelope derivative. -/
theorem chartTower_hasEnvDerivAt (level : ℕ) (base : TangentCoefficient parameters)
    (directions : ℕ → TangentCoefficient parameters)
    (small : tangentPlanarEnvelope 0 base < 1) :
    HasEnvDerivAt (fun t => chartTower level (base + (t : ℂ) • directions level) directions)
      (chartTower (level + 1) base directions) := by
  have each := hasEnvDerivAt_list_sum (chartTerms level)
    (fun term t => evalChartTerm (base + (t : ℂ) • directions level) directions term)
    (fun term => ((chartTermChildren level term).map (evalChartTerm base directions)).sum)
    (fun term _ => evalChartTerm_hasEnvDerivAt base directions level small term)
  refine HasEnvDerivAt.congr_derivative
    (HasEnvDerivAt.congr_curve each (fun t => ?_)) ?_
  · simp only [chartTower]
  · exact chartTerms_children_sum level base directions

end Grad.NonlinearQuotientBounds
