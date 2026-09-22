import QY14MixedCompositionNorms

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.MixedQuotientComposition

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.Constraints
open Grad.NonlinearQuotientBounds

variable {parameters : PhaseParameters}

/-! The accepted finite homogeneous-part one-high proof on real mixed inputs.
Only the input direction norm and the STATE-only base size are specialized;
the literal quotient parts, assignment fibers and loss six are unchanged. -/

section Accounting

variable {order slots : ℕ}

theorem prod_fiberTuple_eq (assignment : Fin order → Fin slots) (slot : Fin slots)
    (directions : Fin order → Input parameters) (r : ℕ) :
    ∏ index, directionNorm r (fiberTuple assignment slot directions index) =
      ∏ position ∈ assignmentFiber assignment slot, directionNorm r (directions position) :=
  prod_fiber_eq assignment slot (fun position => directionNorm r (directions position))

theorem sum_fiberTuple_oneHigh_eq (assignment : Fin order → Fin slots) (slot : Fin slots)
    (directions : Fin order → Input parameters) (high low : ℕ) :
    ∑ index, directionNorm high (fiberTuple assignment slot directions index) *
        ∏ other ∈ Finset.univ.erase index, directionNorm low (fiberTuple assignment slot directions other) =
      ∑ position ∈ assignmentFiber assignment slot, directionNorm high (directions position) *
        ∏ other ∈ (assignmentFiber assignment slot).erase position, directionNorm low (directions other) :=
  sum_fiber_oneHigh_eq assignment slot (fun position => directionNorm high (directions position))
    (fun position => directionNorm low (directions position))


end Accounting

section Inner

variable (family : (order : ℕ) → Input parameters →
    (Fin order → Input parameters) → QuotientState parameters)
  (Admissible : Input parameters → Prop)

/-- Uniform constants over all block orders up to `order`. -/
theorem uniform_inner_bound
    (innerBound : ∀ (grade count : ℕ), ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (tuple : Fin count → Input parameters),
        Admissible base →
        stateNorm grade (family count base tuple) ≤ constant * inputOneHigh grade 4 base tuple)
    (grade order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (count : ℕ), count ≤ order →
      ∀ (base : Input parameters) (tuple : Fin count → Input parameters),
        Admissible base →
        stateNorm grade (family count base tuple) ≤ constant * inputOneHigh grade 4 base tuple := by
  choose constants nonneg bound using innerBound grade
  refine ⟨∑ count ∈ Finset.range (order + 1), constants count,
    Finset.sum_nonneg fun count _ => nonneg count, ?_⟩
  intro count countLe base tuple admissible
  refine (bound count base tuple admissible).trans
    (mul_le_mul_of_nonneg_right ?_ (inputOneHigh_nonneg _ _ _ _))
  exact Finset.single_le_sum (fun c _ => nonneg c) (Finset.mem_range.mpr (by omega))

/-- The grade-four joint one-high expression collapses to a product. -/
theorem inputOneHigh_low_eq (base : Input parameters) {count : ℕ}
    (tuple : Fin count → Input parameters) :
    inputOneHigh 4 4 base tuple =
      (1 + baseNorm 4 base + count) * ∏ position, directionNorm 4 (tuple position) := by
  unfold inputOneHigh
  have each : ∀ position : Fin count, directionNorm 4 (tuple position) *
      ∏ other ∈ Finset.univ.erase position, directionNorm 4 (tuple other) =
      ∏ other, directionNorm 4 (tuple other) :=
    fun position => Finset.mul_prod_erase Finset.univ (fun other => directionNorm 4 (tuple other))
      (Finset.mem_univ position)
  simp only [each, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Inner

/-! ### The term and part bounds -/

section Bounds

variable (family : (order : ℕ) → Input parameters →
    (Fin order → Input parameters) → QuotientState parameters)

/-- The one-high bound of a single term at a fixed base, from the inner
bounds at the high grade and at grade four. -/
theorem termValue_bound {order slots : ℕ}
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (constantP : ℝ) (constantP_nonneg : 0 ≤ constantP) (grade : ℕ)
    (boundP : ∀ arguments, rowsGradeNorm grade (P arguments) ≤
      constantP * oneHighArgumentSum grade arguments)
    (highC lowC : ℝ) (highC_nonneg : 0 ≤ highC) (lowC_one : 1 ≤ lowC)
    (base : Input parameters)
    (highBound : ∀ (count : ℕ), count ≤ order → ∀ tuple : Fin count → Input parameters,
      stateNorm (grade + 6) (family count base tuple) ≤
        highC * inputOneHigh (grade + 6) 4 base tuple)
    (lowBound : ∀ (count : ℕ), count ≤ order → ∀ tuple : Fin count → Input parameters,
      stateNorm 4 (family count base tuple) ≤ lowC * ∏ position, directionNorm 4 (tuple position))
    (assignment : Fin order → Fin slots) (directions : Fin order → Input parameters) :
    rowsGradeNorm grade (termValue family P assignment base directions) ≤
      constantP * ((slots : ℝ) * (highC * lowC ^ slots)) *
        inputOneHigh (grade + 6) 4 base directions := by
  have lowC_nonneg : 0 ≤ lowC := zero_le_one.trans lowC_one
  have powNonneg : 0 ≤ lowC ^ slots := pow_nonneg lowC_nonneg _
  have cardLe : ∀ other : Fin slots, (assignmentFiber assignment other).card ≤ order :=
    fun other => (Finset.card_le_univ _).trans (by rw [Fintype.card_fin])
  have perSlot : ∀ slot : Fin slots,
      stateNorm (grade + 6) (termArguments family assignment base directions slot) *
        ∏ other ∈ Finset.univ.erase slot,
          stateNorm 4 (termArguments family assignment base directions other) ≤
      highC * lowC ^ slots * inputOneHigh (grade + 6) 4 base directions := by
    intro slot
    have highForm : stateNorm (grade + 6) (termArguments family assignment base directions slot) ≤
        highC * ((1 + baseNorm (grade + 6) base) *
          ∏ position ∈ assignmentFiber assignment slot, directionNorm 4 (directions position) +
          ∑ position ∈ assignmentFiber assignment slot, directionNorm (grade + 6) (directions position) *
            ∏ other ∈ (assignmentFiber assignment slot).erase position,
              directionNorm 4 (directions other)) := by
      refine (highBound _ (cardLe slot) (fiberTuple assignment slot directions)).trans ?_
      unfold inputOneHigh
      rw [prod_fiberTuple_eq, sum_fiberTuple_oneHigh_eq]
    have lows : ∏ other ∈ Finset.univ.erase slot,
        stateNorm 4 (termArguments family assignment base directions other) ≤
        lowC ^ slots * ∏ position ∈ (assignmentFiber assignment slot)ᶜ,
          directionNorm 4 (directions position) := by
      calc ∏ other ∈ Finset.univ.erase slot,
            stateNorm 4 (termArguments family assignment base directions other)
          ≤ ∏ other ∈ Finset.univ.erase slot, (lowC *
              ∏ position ∈ assignmentFiber assignment other, directionNorm 4 (directions position)) := by
            apply Finset.prod_le_prod (fun _ _ => stateNorm_nonneg _ _)
            intro other _
            refine (lowBound _ (cardLe other) (fiberTuple assignment other directions)).trans ?_
            rw [prod_fiberTuple_eq]
        _ = lowC ^ (Finset.univ.erase slot).card * ∏ other ∈ Finset.univ.erase slot,
              ∏ position ∈ assignmentFiber assignment other, directionNorm 4 (directions position) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
        _ ≤ lowC ^ slots * ∏ position ∈ (assignmentFiber assignment slot)ᶜ,
              directionNorm 4 (directions position) := by
            rw [prod_erase_fibers]
            apply mul_le_mul_of_nonneg_right _
              (Finset.prod_nonneg fun _ _ => directionNorm_nonneg _ _)
            apply pow_le_pow_right₀ lowC_one
            exact (Finset.card_le_univ _).trans (by rw [Fintype.card_fin])
    have recombine : (1 + baseNorm (grade + 6) base) *
        (∏ position ∈ assignmentFiber assignment slot, directionNorm 4 (directions position)) *
        (∏ position ∈ (assignmentFiber assignment slot)ᶜ, directionNorm 4 (directions position)) +
        (∑ position ∈ assignmentFiber assignment slot, directionNorm (grade + 6) (directions position) *
          ∏ other ∈ (assignmentFiber assignment slot).erase position,
            directionNorm 4 (directions other)) *
        (∏ position ∈ (assignmentFiber assignment slot)ᶜ, directionNorm 4 (directions position)) ≤
        inputOneHigh (grade + 6) 4 base directions := by
      unfold inputOneHigh
      rw [mul_assoc, prod_fiber_mul_prod_compl, Finset.sum_mul]
      refine add_le_add le_rfl ?_
      calc ∑ position ∈ assignmentFiber assignment slot,
            directionNorm (grade + 6) (directions position) *
              (∏ other ∈ (assignmentFiber assignment slot).erase position,
                directionNorm 4 (directions other)) *
              ∏ position ∈ (assignmentFiber assignment slot)ᶜ, directionNorm 4 (directions position)
          = ∑ position ∈ assignmentFiber assignment slot,
              directionNorm (grade + 6) (directions position) *
                ∏ other ∈ Finset.univ.erase position, directionNorm 4 (directions other) := by
            apply Finset.sum_congr rfl
            intro position mem
            rw [mul_assoc, prod_erase_fiber_mul_prod_compl assignment slot _ position mem]
        _ ≤ ∑ position, directionNorm (grade + 6) (directions position) *
              ∏ other ∈ Finset.univ.erase position, directionNorm 4 (directions other) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun _ _ _ => mul_nonneg (directionNorm_nonneg _ _)
                (Finset.prod_nonneg fun _ _ => directionNorm_nonneg _ _))
    have highNonneg : 0 ≤ highC * ((1 + baseNorm (grade + 6) base) *
        ∏ position ∈ assignmentFiber assignment slot, directionNorm 4 (directions position) +
        ∑ position ∈ assignmentFiber assignment slot, directionNorm (grade + 6) (directions position) *
          ∏ other ∈ (assignmentFiber assignment slot).erase position,
            directionNorm 4 (directions other)) := by
      apply mul_nonneg highC_nonneg
      apply add_nonneg
      · exact mul_nonneg (by linarith [baseNorm_nonneg (grade + 6) base])
          (Finset.prod_nonneg fun _ _ => directionNorm_nonneg _ _)
      · exact Finset.sum_nonneg fun _ _ => mul_nonneg (directionNorm_nonneg _ _)
          (Finset.prod_nonneg fun _ _ => directionNorm_nonneg _ _)
    calc stateNorm (grade + 6) (termArguments family assignment base directions slot) *
          ∏ other ∈ Finset.univ.erase slot,
            stateNorm 4 (termArguments family assignment base directions other)
        ≤ (highC * ((1 + baseNorm (grade + 6) base) *
            ∏ position ∈ assignmentFiber assignment slot, directionNorm 4 (directions position) +
            ∑ position ∈ assignmentFiber assignment slot,
              directionNorm (grade + 6) (directions position) *
                ∏ other ∈ (assignmentFiber assignment slot).erase position,
                  directionNorm 4 (directions other))) *
          (lowC ^ slots * ∏ position ∈ (assignmentFiber assignment slot)ᶜ,
            directionNorm 4 (directions position)) :=
          mul_le_mul highForm lows (Finset.prod_nonneg fun _ _ => stateNorm_nonneg _ _) highNonneg
      _ = highC * lowC ^ slots * ((1 + baseNorm (grade + 6) base) *
            (∏ position ∈ assignmentFiber assignment slot, directionNorm 4 (directions position)) *
            (∏ position ∈ (assignmentFiber assignment slot)ᶜ, directionNorm 4 (directions position)) +
          (∑ position ∈ assignmentFiber assignment slot,
            directionNorm (grade + 6) (directions position) *
              ∏ other ∈ (assignmentFiber assignment slot).erase position,
                directionNorm 4 (directions other)) *
            (∏ position ∈ (assignmentFiber assignment slot)ᶜ,
              directionNorm 4 (directions position))) := by ring
      _ ≤ highC * lowC ^ slots * inputOneHigh (grade + 6) 4 base directions :=
          mul_le_mul_of_nonneg_left recombine (mul_nonneg highC_nonneg powNonneg)
  unfold termValue
  refine (boundP _).trans ?_
  rw [mul_assoc constantP]
  apply mul_le_mul_of_nonneg_left _ constantP_nonneg
  unfold oneHighArgumentSum
  refine (Finset.sum_le_sum fun slot _ => perSlot slot).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply le_of_eq
  ring

/-- The bound of the term sum of a part at a fixed base. -/
theorem partComposedDerivative_bound {order slots : ℕ}
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (constantP : ℝ) (constantP_nonneg : 0 ≤ constantP) (grade : ℕ)
    (boundP : ∀ arguments, rowsGradeNorm grade (P arguments) ≤
      constantP * oneHighArgumentSum grade arguments)
    (highC lowC : ℝ) (highC_nonneg : 0 ≤ highC) (lowC_one : 1 ≤ lowC)
    (base : Input parameters)
    (highBound : ∀ (count : ℕ), count ≤ order → ∀ tuple : Fin count → Input parameters,
      stateNorm (grade + 6) (family count base tuple) ≤
        highC * inputOneHigh (grade + 6) 4 base tuple)
    (lowBound : ∀ (count : ℕ), count ≤ order → ∀ tuple : Fin count → Input parameters,
      stateNorm 4 (family count base tuple) ≤ lowC * ∏ position, directionNorm 4 (tuple position))
    (directions : Fin order → Input parameters) :
    rowsGradeNorm grade (partComposedDerivative family P order base directions) ≤
      (Fintype.card (Fin order → Fin slots) : ℝ) *
        (constantP * ((slots : ℝ) * (highC * lowC ^ slots))) *
        inputOneHigh (grade + 6) 4 base directions := by
  unfold partComposedDerivative
  refine (rowsGradeNorm_sum_le grade _ _).trans ?_
  have total := Finset.sum_le_card_nsmul Finset.univ
    (fun assignment => rowsGradeNorm grade (termValue family P assignment base directions))
    (constantP * ((slots : ℝ) * (highC * lowC ^ slots)) * inputOneHigh (grade + 6) 4 base directions)
    (fun assignment _ => termValue_bound family P constantP constantP_nonneg grade boundP highC lowC
      highC_nonneg lowC_one base highBound lowBound assignment directions)
  rw [Finset.card_univ, nsmul_eq_mul, ← mul_assoc] at total
  exact total

/-- The constant part: bounded at order zero, literally zero above. -/
theorem partComposedDerivative_zero_slots_bound
    (P : MultilinearMap ℂ (fun _ : Fin 0 => QuotientState parameters) (QuotientRows parameters))
    (constant : ℝ) (nonneg : 0 ≤ constant) (grade : ℕ)
    (boundP : ∀ arguments, rowsGradeNorm grade (P arguments) ≤ constant) (order : ℕ)
    (base : Input parameters) (directions : Fin order → Input parameters) :
    rowsGradeNorm grade (partComposedDerivative family P order base directions) ≤
      constant * inputOneHigh (grade + 6) 4 base directions := by
  rcases order with _ | order
  · rw [partComposedDerivative_zeroth]
    refine (boundP _).trans ?_
    apply le_mul_of_one_le_right nonneg
    unfold inputOneHigh
    rw [Fin.prod_univ_zero, Fin.sum_univ_zero, mul_one, add_zero]
    linarith [baseNorm_nonneg (grade + 6) base]
  · unfold partComposedDerivative
    rw [Finset.univ_eq_empty, Finset.sum_empty, rowsGradeNorm_zero]
    exact mul_nonneg nonneg (inputOneHigh_nonneg _ _ _ _)

end Bounds

/-! ### The composed bound -/

section Composed

variable (family : (order : ℕ) → Input parameters →
    (Fin order → Input parameters) → QuotientState parameters)
  (Admissible : Input parameters → Prop)

/-- The Q22 one-high bound of the composed family on every admissible ball:
high grade `q + 6` on the base or on exactly one direction, grade four on
every other direction. -/
theorem composedDerivative_bound
    (innerBound : ∀ (grade count : ℕ), ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (tuple : Fin count → Input parameters),
        Admissible base →
        stateNorm grade (family count base tuple) ≤ constant * inputOneHigh grade 4 base tuple)
    (cellLength : ℝ) (grade order : ℕ) (ball : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : Input parameters) (directions : Fin order → Input parameters),
        Admissible base → baseNorm 4 base ≤ ball →
        rowsGradeNorm grade (composedDerivative family cellLength order base directions) ≤
          constant * inputOneHigh (grade + 6) 4 base directions := by
  obtain ⟨highC, highC_nonneg, highBound⟩ :=
    uniform_inner_bound family Admissible innerBound (grade + 6) order
  obtain ⟨low0, low0_nonneg, lowBound0⟩ := uniform_inner_bound family Admissible innerBound 4 order
  obtain ⟨zeroC, zeroC_nonneg, zeroBound⟩ :=
    quotientDegreeZeroPart_bound (parameters := parameters) grade
  obtain ⟨oneC, oneC_nonneg, oneBound⟩ :=
    quotientDegreeOnePart_bound (parameters := parameters) cellLength grade
  obtain ⟨twoC, twoC_nonneg, twoBound⟩ :=
    quotientDegreeTwoPart_bound (parameters := parameters) cellLength grade
  obtain ⟨threeC, threeC_nonneg, threeBound⟩ :=
    quotientDegreeThreePart_bound (parameters := parameters) grade
  obtain ⟨fourC, fourC_nonneg, fourBound⟩ :=
    quotientDegreeFourPart_bound (parameters := parameters) grade
  set lowC : ℝ := 1 + low0 * (1 + |ball| + order) with lowC_def
  have lowC_one : 1 ≤ lowC := by
    have : 0 ≤ low0 * (1 + |ball| + order) :=
      mul_nonneg low0_nonneg (by positivity)
    linarith
  refine ⟨zeroC +
    (Fintype.card (Fin order → Fin 1) : ℝ) * (oneC * ((1 : ℝ) * (highC * lowC ^ 1))) +
    (Fintype.card (Fin order → Fin 2) : ℝ) * (twoC * ((2 : ℝ) * (highC * lowC ^ 2))) +
    (Fintype.card (Fin order → Fin 3) : ℝ) * (threeC * ((3 : ℝ) * (highC * lowC ^ 3))) +
    (Fintype.card (Fin order → Fin 4) : ℝ) * (fourC * ((4 : ℝ) * (highC * lowC ^ 4))),
    by positivity, ?_⟩
  intro base directions admissible inBall
  have highAt : ∀ (count : ℕ), count ≤ order → ∀ tuple : Fin count → Input parameters,
      stateNorm (grade + 6) (family count base tuple) ≤
        highC * inputOneHigh (grade + 6) 4 base tuple :=
    fun count countLe tuple => highBound count countLe base tuple admissible
  have lowAt : ∀ (count : ℕ), count ≤ order → ∀ tuple : Fin count → Input parameters,
      stateNorm 4 (family count base tuple) ≤ lowC * ∏ position, directionNorm 4 (tuple position) := by
    intro count countLe tuple
    refine (lowBound0 count countLe base tuple admissible).trans ?_
    rw [inputOneHigh_low_eq]
    have prodNonneg : 0 ≤ ∏ position, directionNorm 4 (tuple position) :=
      Finset.prod_nonneg fun _ _ => directionNorm_nonneg _ _
    have countLe' : (count : ℝ) ≤ order := Nat.cast_le.mpr countLe
    have factor : 1 + baseNorm 4 base + count ≤ 1 + |ball| + order := by
      linarith [le_abs_self ball]
    have step : low0 * (1 + baseNorm 4 base + count) ≤ low0 * (1 + |ball| + order) :=
      mul_le_mul_of_nonneg_left factor low0_nonneg
    calc low0 * ((1 + baseNorm 4 base + count) * ∏ position, directionNorm 4 (tuple position))
        = (low0 * (1 + baseNorm 4 base + count)) * ∏ position, directionNorm 4 (tuple position) := by
          ring
      _ ≤ lowC * ∏ position, directionNorm 4 (tuple position) := by
          apply mul_le_mul_of_nonneg_right _ prodNonneg
          rw [lowC_def]
          linarith
  have exprNonneg := inputOneHigh_nonneg (grade + 6) 4 base directions
  have zeroPart := partComposedDerivative_zero_slots_bound family
    (quotientDegreeZeroPart parameters) zeroC zeroC_nonneg grade zeroBound order base directions
  have onePart := partComposedDerivative_bound family (quotientDegreeOnePart parameters cellLength)
    oneC oneC_nonneg grade oneBound highC lowC highC_nonneg lowC_one base highAt lowAt directions
  have twoPart := partComposedDerivative_bound family (quotientDegreeTwoPart parameters cellLength)
    twoC twoC_nonneg grade twoBound highC lowC highC_nonneg lowC_one base highAt lowAt directions
  have threePart := partComposedDerivative_bound family (quotientDegreeThreePart parameters)
    threeC threeC_nonneg grade threeBound highC lowC highC_nonneg lowC_one base highAt lowAt
    directions
  have fourPart := partComposedDerivative_bound family (quotientDegreeFourPart parameters)
    fourC fourC_nonneg grade fourBound highC lowC highC_nonneg lowC_one base highAt lowAt
    directions
  unfold composedDerivative
  refine (rowsGradeNorm_add_le grade _ _).trans ?_
  refine (add_le_add (rowsGradeNorm_add_le grade _ _) le_rfl).trans ?_
  refine (add_le_add (add_le_add (rowsGradeNorm_add_le grade _ _) le_rfl) le_rfl).trans ?_
  refine (add_le_add (add_le_add (add_le_add (rowsGradeNorm_add_le grade _ _) le_rfl) le_rfl)
    le_rfl).trans ?_
  have combined := add_le_add (add_le_add (add_le_add (add_le_add zeroPart onePart) twoPart)
    threePart) fourPart
  refine combined.trans (le_of_eq ?_)
  push_cast
  ring

end Composed

end Grad.MixedQuotientComposition

