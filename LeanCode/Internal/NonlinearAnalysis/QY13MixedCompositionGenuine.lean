import QY12MixedCompositionTerms

noncomputable section

set_option maxHeartbeats 1600000

open Filter
open scoped BigOperators Topology

namespace Grad.MixedQuotientComposition

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.Constraints
open Grad.NonlinearQuotientBounds

/-! # Genuineness of the composed derivative family

The finite set-partition chain rule: the term sums of every homogeneous part
differentiate genuinely along the newest direction to the term sums of the
next order, and the literal quotient polynomial composed with an admissible
inner family has the composed family as genuine iterated derivative tower. -/

variable {parameters : PhaseParameters}

/-- Original all-grade state difference quotient, with actual real mixed input. -/
def IsStateDirectionalDerivative (mapping : Input parameters → QuotientState parameters)
    (base direction : Input parameters) (derivative : QuotientState parameters) : Prop :=
  ∀ grade, Tendsto (fun t : ℝ => stateNorm grade
    (((t : ℂ)⁻¹ • (mapping (base + t • direction) - mapping base)) - derivative))
    (𝓝[≠] (0 : ℝ)) (𝓝 0)

/-- Original all-grade quotient difference quotient, with actual real mixed input. -/
def IsRowsDirectionalDerivative (mapping : Input parameters → QuotientRows parameters)
    (base direction : Input parameters) (derivative : QuotientRows parameters) : Prop :=
  ∀ grade, Tendsto (fun t : ℝ => rowsGradeNorm grade
    (((t : ℂ)⁻¹ • (mapping (base + t • direction) - mapping base)) - derivative))
    (𝓝[≠] (0 : ℝ)) (𝓝 0)


/-! ### Sum and addition rules -/

theorem jointRows_sum_rule {Index : Type} (indices : Finset Index)
    (mappings : Index → Input parameters → QuotientRows parameters)
    (base direction : Input parameters) (derivatives : Index → QuotientRows parameters)
    (each : ∀ index ∈ indices,
      IsRowsDirectionalDerivative (mappings index) base direction (derivatives index)) :
    IsRowsDirectionalDerivative (fun state => ∑ index ∈ indices, mappings index state)
      base direction (∑ index ∈ indices, derivatives index) := by
  intro grade
  have expression : ∀ t : ℝ,
      (((t : ℂ))⁻¹ • ((∑ index ∈ indices, mappings index (base + t • direction)) -
        ∑ index ∈ indices, mappings index base)) - ∑ index ∈ indices, derivatives index =
      ∑ index ∈ indices, ((((t : ℂ))⁻¹ • (mappings index (base + t • direction) -
        mappings index base)) - derivatives index) := by
    intro t
    simp only [smul_sub, Finset.smul_sum, Finset.sum_sub_distrib]
  have each' : ∀ index ∈ indices, Tendsto (fun t : ℝ => rowsGradeNorm grade
      ((((t : ℂ))⁻¹ • (mappings index (base + t • direction) - mappings index base)) -
        derivatives index)) (𝓝[≠] (0 : ℝ)) (𝓝 0) :=
    fun index mem => each index mem grade
  have sumTendsto : Tendsto (fun t : ℝ => ∑ index ∈ indices, rowsGradeNorm grade
      ((((t : ℂ))⁻¹ • (mappings index (base + t • direction) - mappings index base)) -
        derivatives index)) (𝓝[≠] (0 : ℝ)) (𝓝 (∑ index ∈ indices, (0 : ℝ))) :=
    tendsto_finsetSum indices each'
  rw [Finset.sum_const_zero] at sumTendsto
  have bound : ∀ t : ℝ, rowsGradeNorm grade
      ((((t : ℂ))⁻¹ • ((∑ index ∈ indices, mappings index (base + t • direction)) -
        ∑ index ∈ indices, mappings index base)) - ∑ index ∈ indices, derivatives index) ≤
      ∑ index ∈ indices, rowsGradeNorm grade
        ((((t : ℂ))⁻¹ • (mappings index (base + t • direction) - mappings index base)) -
          derivatives index) := by
    intro t
    rw [expression t]
    exact rowsGradeNorm_sum_le grade _ _
  exact squeeze_zero (fun _ => rowsGradeNorm_nonneg _ _) bound sumTendsto

theorem jointRows_add_rule (first second : Input parameters → QuotientRows parameters)
    (base direction : Input parameters) (firstD secondD : QuotientRows parameters)
    (firstRule : IsRowsDirectionalDerivative first base direction firstD)
    (secondRule : IsRowsDirectionalDerivative second base direction secondD) :
    IsRowsDirectionalDerivative (fun state => first state + second state)
      base direction (firstD + secondD) := by
  intro grade
  have expression : ∀ t : ℝ,
      (((t : ℂ))⁻¹ • ((first (base + t • direction) + second (base + t • direction)) -
        (first base + second base))) - (firstD + secondD) =
      ((((t : ℂ))⁻¹ • (first (base + t • direction) - first base)) - firstD) +
        ((((t : ℂ))⁻¹ • (second (base + t • direction) - second base)) - secondD) := by
    intro t
    simp only [smul_sub, smul_add]
    abel
  have sumTendsto := (firstRule grade).add (secondRule grade)
  rw [add_zero] at sumTendsto
  refine squeeze_zero (fun _ => rowsGradeNorm_nonneg _ _) (fun t => ?_) sumTendsto
  rw [expression t]
  exact rowsGradeNorm_add_le grade _ _

/-! ### The chain rule for one part -/

section Composition

variable (family : (order : ℕ) → Input parameters →
    (Fin order → Input parameters) → QuotientState parameters)
  (Admissible : Input parameters → Prop)
  (genuine : ∀ (order : ℕ) (base : Input parameters)
    (directions : Fin (order + 1) → Input parameters), Admissible base →
    IsStateDirectionalDerivative
      (fun state => family order state (fun position => directions position.castSucc))
      base (directions (Fin.last order)) (family (order + 1) base directions))

include genuine in
/-- One term differentiates to the sum of its children: the newest direction
joins the block of each slot in turn. -/
theorem termValue_genuine {order slots : ℕ}
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (bounded : OneHighBounded P) (assignment : Fin order → Fin slots)
    (base : Input parameters) (directions : Fin (order + 1) → Input parameters)
    (admissible : Admissible base) :
    IsRowsDirectionalDerivative
      (fun state => termValue family P assignment state
        (fun position => directions position.castSucc))
      base (directions (Fin.last order))
      (∑ slot : Fin slots, termValue family P (Fin.snoc assignment slot) base directions) := by
  intro grade
  have differentiable : ∀ (slot : Fin slots) (r : ℕ), Tendsto (fun t : ℝ => stateNorm r
      ((((t : ℂ))⁻¹ • ((fun slot t => family (assignmentFiber assignment slot).card
          (base + t • directions (Fin.last order))
          (fiberTuple assignment slot (fun position => directions position.castSucc))) slot t -
        termArguments family assignment base (fun position => directions position.castSucc) slot)) -
        (fun slot => family ((assignmentFiber assignment slot).card + 1) base
          (Fin.snoc (fiberTuple assignment slot (fun position => directions position.castSucc))
            (directions (Fin.last order)))) slot)) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    intro slot r
    have step := genuine (assignmentFiber assignment slot).card base
      (Fin.snoc (fiberTuple assignment slot (fun position => directions position.castSucc))
        (directions (Fin.last order))) admissible r
    simp only [Fin.snoc_last, Fin.snoc_castSucc] at step
    exact step
  have rule := multilinear_product_rule P bounded
    (fun slot t => family (assignmentFiber assignment slot).card
      (base + t • directions (Fin.last order))
      (fiberTuple assignment slot (fun position => directions position.castSucc)))
    (termArguments family assignment base (fun position => directions position.castSucc))
    (fun slot => family ((assignmentFiber assignment slot).card + 1) base
      (Fin.snoc (fiberTuple assignment slot (fun position => directions position.castSucc))
        (directions (Fin.last order))))
    differentiable grade
  have children : (∑ slot : Fin slots, P (Function.update
      (termArguments family assignment base (fun position => directions position.castSucc)) slot
      (family ((assignmentFiber assignment slot).card + 1) base
        (Fin.snoc (fiberTuple assignment slot (fun position => directions position.castSucc))
          (directions (Fin.last order)))))) =
      ∑ slot : Fin slots, termValue family P (Fin.snoc assignment slot) base directions := by
    apply Finset.sum_congr rfl
    intro slot _
    unfold termValue
    rw [termArguments_snoc]
  rw [children] at rule
  exact rule

include genuine in
/-- The term sum of a part differentiates genuinely to the term sum of the
next order. -/
theorem partComposedDerivative_genuine {slots : ℕ}
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (bounded : OneHighBounded P) (order : ℕ) (base : Input parameters)
    (directions : Fin (order + 1) → Input parameters) (admissible : Admissible base) :
    IsRowsDirectionalDerivative
      (fun state => partComposedDerivative family P order state
        (fun position => directions position.castSucc))
      base (directions (Fin.last order))
      (partComposedDerivative family P (order + 1) base directions) := by
  rw [partComposedDerivative_succ]
  unfold partComposedDerivative
  exact jointRows_sum_rule Finset.univ
    (fun assignment state => termValue family P assignment state
      (fun position => directions position.castSucc))
    base (directions (Fin.last order))
    (fun assignment => ∑ slot : Fin slots, termValue family P (Fin.snoc assignment slot)
      base directions)
    (fun assignment _ => termValue_genuine family Admissible genuine P bounded assignment base
      directions admissible)

/-! ### The literal quotient polynomial composed with the inner family -/

/-- The composed derivative family of the literal O14 polynomial with an
inner family: the sum of the five composed homogeneous parts. -/
def composedDerivative (cellLength : ℝ) (order : ℕ) (base : Input parameters)
    (directions : Fin order → Input parameters) : QuotientRows parameters :=
  partComposedDerivative family (quotientDegreeZeroPart parameters) order base directions +
    partComposedDerivative family (quotientDegreeOnePart parameters cellLength) order base
      directions +
    partComposedDerivative family (quotientDegreeTwoPart parameters cellLength) order base
      directions +
    partComposedDerivative family (quotientDegreeThreePart parameters) order base directions +
    partComposedDerivative family (quotientDegreeFourPart parameters) order base directions

/-- Order zero is the literal polynomial at the inner value. -/
theorem composedDerivative_zeroth (cellLength : ℝ) (base : Input parameters)
    (directions : Fin 0 → Input parameters) :
    composedDerivative family cellLength 0 base directions =
      quotientPolynomialRows parameters cellLength
        (family 0 base (fun position => position.elim0)) := by
  have rows := quotientRowsDerivative_zeroth (parameters := parameters) cellLength
    (family 0 base (fun position => position.elim0)) (fun position => position.elim0)
  unfold quotientRowsDerivative at rows
  rw [diagonalDerivative_zeroth, diagonalDerivative_zeroth, diagonalDerivative_zeroth,
    diagonalDerivative_zeroth, diagonalDerivative_zeroth] at rows
  unfold composedDerivative
  rw [partComposedDerivative_zeroth, partComposedDerivative_zeroth,
    partComposedDerivative_zeroth, partComposedDerivative_zeroth,
    partComposedDerivative_zeroth]
  exact rows

include genuine in
/-- The composed family differentiates genuinely along the newest direction
at every admissible base. -/
theorem composedDerivative_genuine (cellLength : ℝ) (order : ℕ) (base : Input parameters)
    (directions : Fin (order + 1) → Input parameters) (admissible : Admissible base) :
    IsRowsDirectionalDerivative
      (fun state => composedDerivative family cellLength order state
        (fun position => directions position.castSucc))
      base (directions (Fin.last order))
      (composedDerivative family cellLength (order + 1) base directions) := by
  unfold composedDerivative
  refine jointRows_add_rule _ _ _ _ _ _ (jointRows_add_rule _ _ _ _ _ _
    (jointRows_add_rule _ _ _ _ _ _ (jointRows_add_rule _ _ _ _ _ _ ?_ ?_) ?_) ?_) ?_
  · exact partComposedDerivative_genuine family Admissible genuine _
      (oneHighBounded_zero _) order base directions admissible
  · exact partComposedDerivative_genuine family Admissible genuine _
      (quotientDegreeOnePart_oneHighBounded cellLength) order base directions admissible
  · exact partComposedDerivative_genuine family Admissible genuine _
      (quotientDegreeTwoPart_oneHighBounded cellLength) order base directions admissible
  · exact partComposedDerivative_genuine family Admissible genuine _
      quotientDegreeThreePart_oneHighBounded order base directions admissible
  · exact partComposedDerivative_genuine family Admissible genuine _
      quotientDegreeFourPart_oneHighBounded order base directions admissible

end Composition

end Grad.MixedQuotientComposition

