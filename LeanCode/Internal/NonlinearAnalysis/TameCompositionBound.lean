import TameCompositionGenuine

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.Constraints

/-! # The one-high bound of the composed derivative family

Every term places the high norm in exactly one slot; the block of that slot
receives the inner one-high bound at the high grade and every other block the
inner bound at grade four, whose products recombine, by the fiber accounting
of the slot assignment, into the joint one-high expression of all directions. -/

variable {parameters : PhaseParameters}

/-! ### Fiber accounting -/

section Accounting

variable {order slots : ℕ}

/-- The fiber enumeration as an embedding. -/
def fiberEmbedding (assignment : Fin order → Fin slots) (slot : Fin slots) :
    Fin (assignmentFiber assignment slot).card ↪ Fin order :=
  ((assignmentFiber assignment slot).orderEmbOfFin rfl).toEmbedding

theorem map_univ_fiberEmbedding (assignment : Fin order → Fin slots) (slot : Fin slots) :
    Finset.univ.map (fiberEmbedding assignment slot) = assignmentFiber assignment slot := by
  apply Finset.eq_of_subset_of_card_le
  · intro position mem
    obtain ⟨index, _, rfl⟩ := Finset.mem_map.mp mem
    exact mem_assignmentFiber.mpr (fiberEnumeration_mem assignment slot index)
  · rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem prod_fiber_eq (assignment : Fin order → Fin slots) (slot : Fin slots) (f : Fin order → ℝ) :
    ∏ index, f (fiberEnumeration assignment slot index) =
      ∏ position ∈ assignmentFiber assignment slot, f position := by
  have := Finset.prod_map (Finset.univ : Finset (Fin (assignmentFiber assignment slot).card))
    (fiberEmbedding assignment slot) f
  rw [map_univ_fiberEmbedding] at this
  exact this.symm

theorem sum_fiber_oneHigh_eq (assignment : Fin order → Fin slots) (slot : Fin slots)
    (g f : Fin order → ℝ) :
    ∑ index, g (fiberEnumeration assignment slot index) *
        ∏ other ∈ Finset.univ.erase index, f (fiberEnumeration assignment slot other) =
      ∑ position ∈ assignmentFiber assignment slot, g position *
        ∏ other ∈ (assignmentFiber assignment slot).erase position, f other := by
  have total := Finset.sum_map (Finset.univ : Finset (Fin (assignmentFiber assignment slot).card))
    (fiberEmbedding assignment slot) (fun position => g position *
      ∏ other ∈ (assignmentFiber assignment slot).erase position, f other)
  rw [map_univ_fiberEmbedding] at total
  rw [total]
  apply Finset.sum_congr rfl
  intro index _
  have erase := Finset.prod_map ((Finset.univ : Finset (Fin (assignmentFiber assignment
    slot).card)).erase index) (fiberEmbedding assignment slot) f
  rw [Finset.map_erase, map_univ_fiberEmbedding] at erase
  show g (fiberEnumeration assignment slot index) * _ = g (fiberEmbedding assignment slot index) *
    ∏ other ∈ (assignmentFiber assignment slot).erase (fiberEmbedding assignment slot index), f other
  rw [erase]
  rfl

theorem prod_fiberTuple_eq (assignment : Fin order → Fin slots) (slot : Fin slots)
    (directions : Fin order → JointState parameters) (r : ℕ) :
    ∏ index, jointNorm r (fiberTuple assignment slot directions index) =
      ∏ position ∈ assignmentFiber assignment slot, jointNorm r (directions position) :=
  prod_fiber_eq assignment slot (fun position => jointNorm r (directions position))

theorem sum_fiberTuple_oneHigh_eq (assignment : Fin order → Fin slots) (slot : Fin slots)
    (directions : Fin order → JointState parameters) (high low : ℕ) :
    ∑ index, jointNorm high (fiberTuple assignment slot directions index) *
        ∏ other ∈ Finset.univ.erase index, jointNorm low (fiberTuple assignment slot directions other) =
      ∑ position ∈ assignmentFiber assignment slot, jointNorm high (directions position) *
        ∏ other ∈ (assignmentFiber assignment slot).erase position, jointNorm low (directions other) :=
  sum_fiber_oneHigh_eq assignment slot (fun position => jointNorm high (directions position))
    (fun position => jointNorm low (directions position))

/-- The blocks of the other slots exhaust the complement of one fiber. -/
theorem prod_erase_fibers (assignment : Fin order → Fin slots) (slot : Fin slots)
    (f : Fin order → ℝ) :
    ∏ other ∈ Finset.univ.erase slot, ∏ position ∈ assignmentFiber assignment other, f position =
      ∏ position ∈ (assignmentFiber assignment slot)ᶜ, f position := by
  have mapsTo : ∀ position ∈ (assignmentFiber assignment slot)ᶜ,
      assignment position ∈ Finset.univ.erase slot := by
    intro position mem
    rw [Finset.mem_compl, mem_assignmentFiber] at mem
    exact Finset.mem_erase.mpr ⟨mem, Finset.mem_univ _⟩
  rw [← Finset.prod_fiberwise_of_maps_to mapsTo f]
  apply Finset.prod_congr rfl
  intro other mem
  congr 1
  ext position
  rw [Finset.mem_filter, Finset.mem_compl, mem_assignmentFiber, mem_assignmentFiber]
  constructor
  · intro h
    refine ⟨?_, h⟩
    rw [h]
    exact Finset.ne_of_mem_erase mem
  · exact fun h => h.2

theorem prod_fiber_mul_prod_compl (assignment : Fin order → Fin slots) (slot : Fin slots)
    (f : Fin order → ℝ) :
    (∏ position ∈ assignmentFiber assignment slot, f position) *
        ∏ position ∈ (assignmentFiber assignment slot)ᶜ, f position =
      ∏ position, f position :=
  Finset.prod_mul_prod_compl _ f

theorem prod_erase_fiber_mul_prod_compl (assignment : Fin order → Fin slots) (slot : Fin slots)
    (f : Fin order → ℝ) (position : Fin order) (mem : position ∈ assignmentFiber assignment slot) :
    (∏ other ∈ (assignmentFiber assignment slot).erase position, f other) *
        ∏ other ∈ (assignmentFiber assignment slot)ᶜ, f other =
      ∏ other ∈ Finset.univ.erase position, f other := by
  have disjoint : Disjoint ((assignmentFiber assignment slot).erase position)
      (assignmentFiber assignment slot)ᶜ := by
    rw [Finset.disjoint_left]
    intro other inErase inCompl
    exact (Finset.mem_compl.mp inCompl) (Finset.mem_of_mem_erase inErase)
  rw [← Finset.prod_union disjoint]
  congr 1
  ext other
  rw [Finset.mem_union, Finset.mem_erase, Finset.mem_compl, Finset.mem_erase]
  constructor
  · rintro (⟨ne, _⟩ | notIn)
    · exact ⟨ne, Finset.mem_univ _⟩
    · refine ⟨?_, Finset.mem_univ _⟩
      rintro rfl
      exact notIn mem
  · rintro ⟨ne, _⟩
    by_cases inFiber : other ∈ assignmentFiber assignment slot
    · exact Or.inl ⟨ne, inFiber⟩
    · exact Or.inr inFiber

end Accounting

/-! ### Inner bounds in uniform form -/

section Inner

variable (family : (order : ℕ) → JointState parameters →
    (Fin order → JointState parameters) → QuotientState parameters)
  (Admissible : JointState parameters → Prop)

/-- Uniform constants over all block orders up to `order`. -/
theorem uniform_inner_bound
    (innerBound : ∀ (grade count : ℕ), ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : JointState parameters) (tuple : Fin count → JointState parameters),
        Admissible base →
        stateNorm grade (family count base tuple) ≤ constant * jointOneHigh grade 4 base tuple)
    (grade order : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (count : ℕ), count ≤ order →
      ∀ (base : JointState parameters) (tuple : Fin count → JointState parameters),
        Admissible base →
        stateNorm grade (family count base tuple) ≤ constant * jointOneHigh grade 4 base tuple := by
  choose constants nonneg bound using innerBound grade
  refine ⟨∑ count ∈ Finset.range (order + 1), constants count,
    Finset.sum_nonneg fun count _ => nonneg count, ?_⟩
  intro count countLe base tuple admissible
  refine (bound count base tuple admissible).trans
    (mul_le_mul_of_nonneg_right ?_ (jointOneHigh_nonneg _ _ _ _))
  exact Finset.single_le_sum (fun c _ => nonneg c) (Finset.mem_range.mpr (by omega))

/-- The grade-four joint one-high expression collapses to a product. -/
theorem jointOneHigh_low_eq (base : JointState parameters) {count : ℕ}
    (tuple : Fin count → JointState parameters) :
    jointOneHigh 4 4 base tuple =
      (1 + jointNorm 4 base + count) * ∏ position, jointNorm 4 (tuple position) := by
  unfold jointOneHigh
  have each : ∀ position : Fin count, jointNorm 4 (tuple position) *
      ∏ other ∈ Finset.univ.erase position, jointNorm 4 (tuple other) =
      ∏ other, jointNorm 4 (tuple other) :=
    fun position => Finset.mul_prod_erase Finset.univ (fun other => jointNorm 4 (tuple other))
      (Finset.mem_univ position)
  simp only [each, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end Inner

/-! ### The term and part bounds -/

section Bounds

variable (family : (order : ℕ) → JointState parameters →
    (Fin order → JointState parameters) → QuotientState parameters)

/-- The one-high bound of a single term at a fixed base, from the inner
bounds at the high grade and at grade four. -/
theorem termValue_bound {order slots : ℕ}
    (P : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters) (QuotientRows parameters))
    (constantP : ℝ) (constantP_nonneg : 0 ≤ constantP) (grade : ℕ)
    (boundP : ∀ arguments, rowsGradeNorm grade (P arguments) ≤
      constantP * oneHighArgumentSum grade arguments)
    (highC lowC : ℝ) (highC_nonneg : 0 ≤ highC) (lowC_one : 1 ≤ lowC)
    (base : JointState parameters)
    (highBound : ∀ (count : ℕ), count ≤ order → ∀ tuple : Fin count → JointState parameters,
      stateNorm (grade + 6) (family count base tuple) ≤
        highC * jointOneHigh (grade + 6) 4 base tuple)
    (lowBound : ∀ (count : ℕ), count ≤ order → ∀ tuple : Fin count → JointState parameters,
      stateNorm 4 (family count base tuple) ≤ lowC * ∏ position, jointNorm 4 (tuple position))
    (assignment : Fin order → Fin slots) (directions : Fin order → JointState parameters) :
    rowsGradeNorm grade (termValue family P assignment base directions) ≤
      constantP * ((slots : ℝ) * (highC * lowC ^ slots)) *
        jointOneHigh (grade + 6) 4 base directions := by
  have lowC_nonneg : 0 ≤ lowC := zero_le_one.trans lowC_one
  have powNonneg : 0 ≤ lowC ^ slots := pow_nonneg lowC_nonneg _
  have cardLe : ∀ other : Fin slots, (assignmentFiber assignment other).card ≤ order :=
    fun other => (Finset.card_le_univ _).trans (by rw [Fintype.card_fin])
  have perSlot : ∀ slot : Fin slots,
      stateNorm (grade + 6) (termArguments family assignment base directions slot) *
        ∏ other ∈ Finset.univ.erase slot,
          stateNorm 4 (termArguments family assignment base directions other) ≤
      highC * lowC ^ slots * jointOneHigh (grade + 6) 4 base directions := by
    intro slot
    have highForm : stateNorm (grade + 6) (termArguments family assignment base directions slot) ≤
        highC * ((1 + jointNorm (grade + 6) base) *
          ∏ position ∈ assignmentFiber assignment slot, jointNorm 4 (directions position) +
          ∑ position ∈ assignmentFiber assignment slot, jointNorm (grade + 6) (directions position) *
            ∏ other ∈ (assignmentFiber assignment slot).erase position,
              jointNorm 4 (directions other)) := by
      refine (highBound _ (cardLe slot) (fiberTuple assignment slot directions)).trans ?_
      unfold jointOneHigh
      rw [prod_fiberTuple_eq, sum_fiberTuple_oneHigh_eq]
    have lows : ∏ other ∈ Finset.univ.erase slot,
        stateNorm 4 (termArguments family assignment base directions other) ≤
        lowC ^ slots * ∏ position ∈ (assignmentFiber assignment slot)ᶜ,
          jointNorm 4 (directions position) := by
      calc ∏ other ∈ Finset.univ.erase slot,
            stateNorm 4 (termArguments family assignment base directions other)
          ≤ ∏ other ∈ Finset.univ.erase slot, (lowC *
              ∏ position ∈ assignmentFiber assignment other, jointNorm 4 (directions position)) := by
            apply Finset.prod_le_prod (fun _ _ => stateNorm_nonneg _ _)
            intro other _
            refine (lowBound _ (cardLe other) (fiberTuple assignment other directions)).trans ?_
            rw [prod_fiberTuple_eq]
        _ = lowC ^ (Finset.univ.erase slot).card * ∏ other ∈ Finset.univ.erase slot,
              ∏ position ∈ assignmentFiber assignment other, jointNorm 4 (directions position) := by
            rw [Finset.prod_mul_distrib, Finset.prod_const]
        _ ≤ lowC ^ slots * ∏ position ∈ (assignmentFiber assignment slot)ᶜ,
              jointNorm 4 (directions position) := by
            rw [prod_erase_fibers]
            apply mul_le_mul_of_nonneg_right _
              (Finset.prod_nonneg fun _ _ => jointNorm_nonneg _ _)
            apply pow_le_pow_right₀ lowC_one
            exact (Finset.card_le_univ _).trans (by rw [Fintype.card_fin])
    have recombine : (1 + jointNorm (grade + 6) base) *
        (∏ position ∈ assignmentFiber assignment slot, jointNorm 4 (directions position)) *
        (∏ position ∈ (assignmentFiber assignment slot)ᶜ, jointNorm 4 (directions position)) +
        (∑ position ∈ assignmentFiber assignment slot, jointNorm (grade + 6) (directions position) *
          ∏ other ∈ (assignmentFiber assignment slot).erase position,
            jointNorm 4 (directions other)) *
        (∏ position ∈ (assignmentFiber assignment slot)ᶜ, jointNorm 4 (directions position)) ≤
        jointOneHigh (grade + 6) 4 base directions := by
      unfold jointOneHigh
      rw [mul_assoc, prod_fiber_mul_prod_compl, Finset.sum_mul]
      refine add_le_add le_rfl ?_
      calc ∑ position ∈ assignmentFiber assignment slot,
            jointNorm (grade + 6) (directions position) *
              (∏ other ∈ (assignmentFiber assignment slot).erase position,
                jointNorm 4 (directions other)) *
              ∏ position ∈ (assignmentFiber assignment slot)ᶜ, jointNorm 4 (directions position)
          = ∑ position ∈ assignmentFiber assignment slot,
              jointNorm (grade + 6) (directions position) *
                ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other) := by
            apply Finset.sum_congr rfl
            intro position mem
            rw [mul_assoc, prod_erase_fiber_mul_prod_compl assignment slot _ position mem]
        _ ≤ ∑ position, jointNorm (grade + 6) (directions position) *
              ∏ other ∈ Finset.univ.erase position, jointNorm 4 (directions other) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
              (fun _ _ _ => mul_nonneg (jointNorm_nonneg _ _)
                (Finset.prod_nonneg fun _ _ => jointNorm_nonneg _ _))
    have highNonneg : 0 ≤ highC * ((1 + jointNorm (grade + 6) base) *
        ∏ position ∈ assignmentFiber assignment slot, jointNorm 4 (directions position) +
        ∑ position ∈ assignmentFiber assignment slot, jointNorm (grade + 6) (directions position) *
          ∏ other ∈ (assignmentFiber assignment slot).erase position,
            jointNorm 4 (directions other)) := by
      apply mul_nonneg highC_nonneg
      apply add_nonneg
      · exact mul_nonneg (by linarith [jointNorm_nonneg (grade + 6) base])
          (Finset.prod_nonneg fun _ _ => jointNorm_nonneg _ _)
      · exact Finset.sum_nonneg fun _ _ => mul_nonneg (jointNorm_nonneg _ _)
          (Finset.prod_nonneg fun _ _ => jointNorm_nonneg _ _)
    calc stateNorm (grade + 6) (termArguments family assignment base directions slot) *
          ∏ other ∈ Finset.univ.erase slot,
            stateNorm 4 (termArguments family assignment base directions other)
        ≤ (highC * ((1 + jointNorm (grade + 6) base) *
            ∏ position ∈ assignmentFiber assignment slot, jointNorm 4 (directions position) +
            ∑ position ∈ assignmentFiber assignment slot,
              jointNorm (grade + 6) (directions position) *
                ∏ other ∈ (assignmentFiber assignment slot).erase position,
                  jointNorm 4 (directions other))) *
          (lowC ^ slots * ∏ position ∈ (assignmentFiber assignment slot)ᶜ,
            jointNorm 4 (directions position)) :=
          mul_le_mul highForm lows (Finset.prod_nonneg fun _ _ => stateNorm_nonneg _ _) highNonneg
      _ = highC * lowC ^ slots * ((1 + jointNorm (grade + 6) base) *
            (∏ position ∈ assignmentFiber assignment slot, jointNorm 4 (directions position)) *
            (∏ position ∈ (assignmentFiber assignment slot)ᶜ, jointNorm 4 (directions position)) +
          (∑ position ∈ assignmentFiber assignment slot,
            jointNorm (grade + 6) (directions position) *
              ∏ other ∈ (assignmentFiber assignment slot).erase position,
                jointNorm 4 (directions other)) *
            (∏ position ∈ (assignmentFiber assignment slot)ᶜ,
              jointNorm 4 (directions position))) := by ring
      _ ≤ highC * lowC ^ slots * jointOneHigh (grade + 6) 4 base directions :=
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
    (base : JointState parameters)
    (highBound : ∀ (count : ℕ), count ≤ order → ∀ tuple : Fin count → JointState parameters,
      stateNorm (grade + 6) (family count base tuple) ≤
        highC * jointOneHigh (grade + 6) 4 base tuple)
    (lowBound : ∀ (count : ℕ), count ≤ order → ∀ tuple : Fin count → JointState parameters,
      stateNorm 4 (family count base tuple) ≤ lowC * ∏ position, jointNorm 4 (tuple position))
    (directions : Fin order → JointState parameters) :
    rowsGradeNorm grade (partComposedDerivative family P order base directions) ≤
      (Fintype.card (Fin order → Fin slots) : ℝ) *
        (constantP * ((slots : ℝ) * (highC * lowC ^ slots))) *
        jointOneHigh (grade + 6) 4 base directions := by
  unfold partComposedDerivative
  refine (rowsGradeNorm_sum_le grade _ _).trans ?_
  have total := Finset.sum_le_card_nsmul Finset.univ
    (fun assignment => rowsGradeNorm grade (termValue family P assignment base directions))
    (constantP * ((slots : ℝ) * (highC * lowC ^ slots)) * jointOneHigh (grade + 6) 4 base directions)
    (fun assignment _ => termValue_bound family P constantP constantP_nonneg grade boundP highC lowC
      highC_nonneg lowC_one base highBound lowBound assignment directions)
  rw [Finset.card_univ, nsmul_eq_mul, ← mul_assoc] at total
  exact total

/-- The constant part: bounded at order zero, literally zero above. -/
theorem partComposedDerivative_zero_slots_bound
    (P : MultilinearMap ℂ (fun _ : Fin 0 => QuotientState parameters) (QuotientRows parameters))
    (constant : ℝ) (nonneg : 0 ≤ constant) (grade : ℕ)
    (boundP : ∀ arguments, rowsGradeNorm grade (P arguments) ≤ constant) (order : ℕ)
    (base : JointState parameters) (directions : Fin order → JointState parameters) :
    rowsGradeNorm grade (partComposedDerivative family P order base directions) ≤
      constant * jointOneHigh (grade + 6) 4 base directions := by
  rcases order with _ | order
  · rw [partComposedDerivative_zeroth]
    refine (boundP _).trans ?_
    apply le_mul_of_one_le_right nonneg
    unfold jointOneHigh
    rw [Fin.prod_univ_zero, Fin.sum_univ_zero, mul_one, add_zero]
    linarith [jointNorm_nonneg (grade + 6) base]
  · unfold partComposedDerivative
    rw [Finset.univ_eq_empty, Finset.sum_empty, rowsGradeNorm_zero]
    exact mul_nonneg nonneg (jointOneHigh_nonneg _ _ _ _)

end Bounds

/-! ### The composed bound -/

section Composed

variable (family : (order : ℕ) → JointState parameters →
    (Fin order → JointState parameters) → QuotientState parameters)
  (Admissible : JointState parameters → Prop)

/-- The Q22 one-high bound of the composed family on every admissible ball:
high grade `q + 6` on the base or on exactly one direction, grade four on
every other direction. -/
theorem composedDerivative_bound
    (innerBound : ∀ (grade count : ℕ), ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : JointState parameters) (tuple : Fin count → JointState parameters),
        Admissible base →
        stateNorm grade (family count base tuple) ≤ constant * jointOneHigh grade 4 base tuple)
    (cellLength : ℝ) (grade order : ℕ) (ball : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : JointState parameters) (directions : Fin order → JointState parameters),
        Admissible base → jointNorm 4 base ≤ ball →
        rowsGradeNorm grade (composedDerivative family cellLength order base directions) ≤
          constant * jointOneHigh (grade + 6) 4 base directions := by
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
  have highAt : ∀ (count : ℕ), count ≤ order → ∀ tuple : Fin count → JointState parameters,
      stateNorm (grade + 6) (family count base tuple) ≤
        highC * jointOneHigh (grade + 6) 4 base tuple :=
    fun count countLe tuple => highBound count countLe base tuple admissible
  have lowAt : ∀ (count : ℕ), count ≤ order → ∀ tuple : Fin count → JointState parameters,
      stateNorm 4 (family count base tuple) ≤ lowC * ∏ position, jointNorm 4 (tuple position) := by
    intro count countLe tuple
    refine (lowBound0 count countLe base tuple admissible).trans ?_
    rw [jointOneHigh_low_eq]
    have prodNonneg : 0 ≤ ∏ position, jointNorm 4 (tuple position) :=
      Finset.prod_nonneg fun _ _ => jointNorm_nonneg _ _
    have countLe' : (count : ℝ) ≤ order := Nat.cast_le.mpr countLe
    have factor : 1 + jointNorm 4 base + count ≤ 1 + |ball| + order := by
      linarith [le_abs_self ball]
    have step : low0 * (1 + jointNorm 4 base + count) ≤ low0 * (1 + |ball| + order) :=
      mul_le_mul_of_nonneg_left factor low0_nonneg
    calc low0 * ((1 + jointNorm 4 base + count) * ∏ position, jointNorm 4 (tuple position))
        = (low0 * (1 + jointNorm 4 base + count)) * ∏ position, jointNorm 4 (tuple position) := by
          ring
      _ ≤ lowC * ∏ position, jointNorm 4 (tuple position) := by
          apply mul_le_mul_of_nonneg_right _ prodNonneg
          rw [lowC_def]
          linarith
  have exprNonneg := jointOneHigh_nonneg (grade + 6) 4 base directions
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

end Grad.NonlinearQuotientBounds
