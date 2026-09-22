import QuotientWrapBounds

noncomputable section

open scoped BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

variable {parameters : PhaseParameters}

/-- The exact recombination of the argument one-high sum along an injective
placement: base slots are bounded by the low norm bound, direction slots
reproduce the Q4 right-hand side. -/
theorem slotAssign_oneHigh_bound {order slots : ℕ} {insertion : Fin order → Fin slots}
    (membership : insertion ∈ slotInjections order slots) (grade : ℕ)
    (base : QuotientState parameters) (directions : Fin order → QuotientState parameters)
    (bound : ℝ) (baseBounded : stateNorm 4 base ≤ bound) :
    oneHighArgumentSum grade (slotAssign insertion base directions) ≤
      (slots : ℝ) * (1 + bound) ^ slots * oneHighStateExpression grade base directions := by
  have injective := mem_slotInjections.mp membership
  have boundNonneg : (0 : ℝ) ≤ bound := (stateNorm_nonneg 4 base).trans baseBounded
  have onePlusOne : (1 : ℝ) ≤ 1 + bound := by linarith
  have powerNonneg : (0 : ℝ) ≤ (1 + bound) ^ slots := pow_nonneg (by linarith) slots
  have basePower : ∀ subset : Finset (Fin slots),
      (∏ _slot ∈ subset, stateNorm 4 base) ≤ (1 + bound) ^ slots := by
    intro subset
    rw [Finset.prod_const]
    have cardLe : subset.card ≤ slots := by
      have le := Finset.card_le_card (Finset.subset_univ subset)
      rwa [Finset.card_univ, Fintype.card_fin] at le
    calc stateNorm 4 base ^ subset.card ≤ bound ^ subset.card :=
        pow_le_pow_left₀ (stateNorm_nonneg 4 base) baseBounded subset.card
      _ ≤ (1 + bound) ^ subset.card :=
        pow_le_pow_left₀ boundNonneg (by linarith) subset.card
      _ ≤ (1 + bound) ^ slots := pow_le_pow_right₀ onePlusOne cardLe
  have perSlot : ∀ slot : Fin slots,
      stateNorm (grade + 6) (slotAssign insertion base directions slot) *
        ∏ other ∈ Finset.univ.erase slot,
          stateNorm 4 (slotAssign insertion base directions other) ≤
      (1 + bound) ^ slots * oneHighStateExpression grade base directions := by
    intro slot
    by_cases occupied : ∃ position, insertion position = slot
    · obtain ⟨positionZero, rfl⟩ := occupied
      have highValue : stateNorm (grade + 6)
          (slotAssign insertion base directions (insertion positionZero)) =
          stateNorm (grade + 6) (directions positionZero) := by
        rw [slotAssign_occupied injective]
      have partition : (Finset.univ.erase (insertion positionZero) : Finset (Fin slots)) =
          freeSlots insertion ∪ (Finset.univ.erase positionZero).image insertion := by
        ext target
        rw [Finset.mem_erase, Finset.mem_union, mem_freeSlots, Finset.mem_image]
        constructor
        · intro paired
          by_cases free : ∀ position, insertion position ≠ target
          · exact Or.inl free
          · push Not at free
            obtain ⟨position, rfl⟩ := free
            refine Or.inr ⟨position, ?_, rfl⟩
            rw [Finset.mem_erase]
            exact ⟨fun collide => paired.1 (by rw [collide]), Finset.mem_univ _⟩
        · intro parts
          rcases parts with free | ⟨position, positionMembership, rfl⟩
          · exact ⟨fun collide => free positionZero collide.symm, Finset.mem_univ _⟩
          · rw [Finset.mem_erase] at positionMembership
            exact ⟨fun collide => positionMembership.1 (injective collide),
              Finset.mem_univ _⟩
      have disjointParts : Disjoint (freeSlots insertion)
          ((Finset.univ.erase positionZero).image insertion) := by
        rw [Finset.disjoint_left]
        intro target freeMembership imageMembership
        obtain ⟨position, _, rfl⟩ := Finset.mem_image.mp imageMembership
        exact mem_freeSlots.mp freeMembership position rfl
      have productSplit : (∏ other ∈ Finset.univ.erase (insertion positionZero),
          stateNorm 4 (slotAssign insertion base directions other)) =
          (∏ other ∈ freeSlots insertion,
            stateNorm 4 (slotAssign insertion base directions other)) *
          ∏ other ∈ (Finset.univ.erase positionZero).image insertion,
            stateNorm 4 (slotAssign insertion base directions other) := by
        rw [partition, Finset.prod_union disjointParts]
      have freeProduct : (∏ other ∈ freeSlots insertion,
          stateNorm 4 (slotAssign insertion base directions other)) ≤ (1 + bound) ^ slots := by
        have congruent : (∏ other ∈ freeSlots insertion,
            stateNorm 4 (slotAssign insertion base directions other)) =
            ∏ _other ∈ freeSlots insertion, stateNorm 4 base :=
          Finset.prod_congr rfl (fun other otherMembership => by
            rw [slotAssign_free base directions (mem_freeSlots.mp otherMembership)])
        rw [congruent]
        exact basePower _
      have imageProduct : (∏ other ∈ (Finset.univ.erase positionZero).image insertion,
          stateNorm 4 (slotAssign insertion base directions other)) =
          ∏ position ∈ Finset.univ.erase positionZero,
            stateNorm 4 (directions position) := by
        rw [Finset.prod_image (fun left _ right _ equal => injective equal)]
        exact Finset.prod_congr rfl (fun position _ => by
          rw [slotAssign_occupied injective])
      have directionsNonneg : (0 : ℝ) ≤ ∏ position ∈ Finset.univ.erase positionZero,
          stateNorm 4 (directions position) :=
        Finset.prod_nonneg (fun _ _ => stateNorm_nonneg _ _)
      have summandLe : stateNorm (grade + 6) (directions positionZero) *
          ∏ position ∈ Finset.univ.erase positionZero,
            stateNorm 4 (directions position) ≤
          oneHighStateExpression grade base directions := by
        have inSum : stateNorm (grade + 6) (directions positionZero) *
            ∏ position ∈ Finset.univ.erase positionZero,
              stateNorm 4 (directions position) ≤
            oneHighArgumentSum grade directions :=
          Finset.single_le_sum (f := fun position => stateNorm (grade + 6)
            (directions position) * ∏ other ∈ Finset.univ.erase position,
              stateNorm 4 (directions other))
            (fun position _ => mul_nonneg (stateNorm_nonneg _ _)
              (Finset.prod_nonneg (fun _ _ => stateNorm_nonneg _ _)))
            (Finset.mem_univ positionZero)
        apply inSum.trans
        unfold oneHighStateExpression
        have firstNonneg : (0 : ℝ) ≤ (1 + stateNorm (grade + 6) base) *
            ∏ position, stateNorm 4 (directions position) := by
          have s6 := stateNorm_nonneg (grade + 6) base
          have prodNonneg : (0 : ℝ) ≤ ∏ position, stateNorm 4 (directions position) :=
            Finset.prod_nonneg (fun _ _ => stateNorm_nonneg _ _)
          nlinarith
        linarith
      rw [highValue, productSplit, imageProduct]
      calc stateNorm (grade + 6) (directions positionZero) *
            ((∏ other ∈ freeSlots insertion,
              stateNorm 4 (slotAssign insertion base directions other)) *
              ∏ position ∈ Finset.univ.erase positionZero,
                stateNorm 4 (directions position)) ≤
          stateNorm (grade + 6) (directions positionZero) *
            ((1 + bound) ^ slots * ∏ position ∈ Finset.univ.erase positionZero,
              stateNorm 4 (directions position)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right freeProduct
              directionsNonneg) (stateNorm_nonneg _ _)
        _ = (1 + bound) ^ slots * (stateNorm (grade + 6) (directions positionZero) *
              ∏ position ∈ Finset.univ.erase positionZero,
                stateNorm 4 (directions position)) := by ring
        _ ≤ (1 + bound) ^ slots * oneHighStateExpression grade base directions :=
            mul_le_mul_of_nonneg_left summandLe powerNonneg
    · push Not at occupied
      have highValue : stateNorm (grade + 6)
          (slotAssign insertion base directions slot) = stateNorm (grade + 6) base := by
        rw [slotAssign_free base directions occupied]
      have partition : (Finset.univ.erase slot : Finset (Fin slots)) =
          (freeSlots insertion).erase slot ∪ Finset.univ.image insertion := by
        ext target
        rw [Finset.mem_erase, Finset.mem_union, Finset.mem_erase, mem_freeSlots,
          Finset.mem_image]
        constructor
        · intro paired
          by_cases free : ∀ position, insertion position ≠ target
          · exact Or.inl ⟨paired.1, free⟩
          · push Not at free
            obtain ⟨position, rfl⟩ := free
            exact Or.inr ⟨position, Finset.mem_univ _, rfl⟩
        · intro parts
          rcases parts with ⟨notSlot, _⟩ | ⟨position, _, rfl⟩
          · exact ⟨notSlot, Finset.mem_univ _⟩
          · exact ⟨fun collide => occupied position collide, Finset.mem_univ _⟩
      have disjointParts : Disjoint ((freeSlots insertion).erase slot)
          (Finset.univ.image insertion) := by
        rw [Finset.disjoint_left]
        intro target freeMembership imageMembership
        obtain ⟨position, _, rfl⟩ := Finset.mem_image.mp imageMembership
        exact mem_freeSlots.mp (Finset.mem_of_mem_erase freeMembership) position rfl
      have productSplit : (∏ other ∈ Finset.univ.erase slot,
          stateNorm 4 (slotAssign insertion base directions other)) =
          (∏ other ∈ (freeSlots insertion).erase slot,
            stateNorm 4 (slotAssign insertion base directions other)) *
          ∏ other ∈ Finset.univ.image insertion,
            stateNorm 4 (slotAssign insertion base directions other) := by
        rw [partition, Finset.prod_union disjointParts]
      have freeProduct : (∏ other ∈ (freeSlots insertion).erase slot,
          stateNorm 4 (slotAssign insertion base directions other)) ≤ (1 + bound) ^ slots := by
        have congruent : (∏ other ∈ (freeSlots insertion).erase slot,
            stateNorm 4 (slotAssign insertion base directions other)) =
            ∏ _other ∈ (freeSlots insertion).erase slot, stateNorm 4 base :=
          Finset.prod_congr rfl (fun other otherMembership => by
            rw [slotAssign_free base directions
              (mem_freeSlots.mp (Finset.mem_of_mem_erase otherMembership))])
        rw [congruent]
        exact basePower _
      have imageProduct : (∏ other ∈ Finset.univ.image insertion,
          stateNorm 4 (slotAssign insertion base directions other)) =
          ∏ position, stateNorm 4 (directions position) := by
        rw [Finset.prod_image (fun left _ right _ equal => injective equal)]
        exact Finset.prod_congr rfl (fun position _ => by
          rw [slotAssign_occupied injective])
      have directionsNonneg : (0 : ℝ) ≤ ∏ position, stateNorm 4 (directions position) :=
        Finset.prod_nonneg (fun _ _ => stateNorm_nonneg _ _)
      have summandLe : stateNorm (grade + 6) base *
          ∏ position, stateNorm 4 (directions position) ≤
          oneHighStateExpression grade base directions := by
        unfold oneHighStateExpression
        have sumNonneg := oneHighArgumentSum_nonneg grade directions
        nlinarith [stateNorm_nonneg (grade + 6) base, directionsNonneg]
      rw [highValue, productSplit, imageProduct]
      calc stateNorm (grade + 6) base *
            ((∏ other ∈ (freeSlots insertion).erase slot,
              stateNorm 4 (slotAssign insertion base directions other)) *
              ∏ position, stateNorm 4 (directions position)) ≤
          stateNorm (grade + 6) base * ((1 + bound) ^ slots *
            ∏ position, stateNorm 4 (directions position)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right freeProduct
              directionsNonneg) (stateNorm_nonneg _ _)
        _ = (1 + bound) ^ slots * (stateNorm (grade + 6) base *
              ∏ position, stateNorm 4 (directions position)) := by ring
        _ ≤ (1 + bound) ^ slots * oneHighStateExpression grade base directions :=
            mul_le_mul_of_nonneg_left summandLe powerNonneg
  unfold oneHighArgumentSum
  apply (Finset.sum_le_sum (fun slot _ => perSlot slot)).trans
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply le_of_eq
  ring

/-- The complete Q4 one-high bound for the exact derivative family, at every
grade and order, with the low norm of the base state bounded. -/
theorem quotientRowsDerivative_bound (cellLength : ℝ) (boundGrade order : ℕ) (bound : ℝ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base : QuotientState parameters)
        (directions : Fin order → QuotientState parameters),
        stateNorm 4 base ≤ bound →
        rowsGradeNorm boundGrade
            (quotientRowsDerivative parameters cellLength order base directions) ≤
          constant * oneHighStateExpression boundGrade base directions := by
  obtain ⟨zeroC, zeroNonneg, zeroBound⟩ :=
    quotientDegreeZeroPart_bound (parameters := parameters) boundGrade
  obtain ⟨oneC, oneNonneg, oneBound⟩ :=
    quotientDegreeOnePart_bound (parameters := parameters) cellLength boundGrade
  obtain ⟨twoC, twoNonneg, twoBound⟩ :=
    quotientDegreeTwoPart_bound (parameters := parameters) cellLength boundGrade
  obtain ⟨threeC, threeNonneg, threeBound⟩ :=
    quotientDegreeThreePart_bound (parameters := parameters) boundGrade
  obtain ⟨fourC, fourNonneg, fourBound⟩ :=
    quotientDegreeFourPart_bound (parameters := parameters) boundGrade
  refine ⟨|zeroC +
    (1 : ℝ) ^ order * (oneC * ((1 : ℝ) * (1 + bound) ^ 1)) +
    (2 : ℝ) ^ order * (twoC * ((2 : ℝ) * (1 + bound) ^ 2)) +
    (3 : ℝ) ^ order * (threeC * ((3 : ℝ) * (1 + bound) ^ 3)) +
    (4 : ℝ) ^ order * (fourC * ((4 : ℝ) * (1 + bound) ^ 4))|, abs_nonneg _, ?_⟩
  intro base directions baseBounded
  have exprNonneg := oneHighStateExpression_nonneg boundGrade base directions
  have boundNonneg : (0 : ℝ) ≤ bound := (stateNorm_nonneg 4 base).trans baseBounded
  have diagBound : ∀ {slots : ℕ}
      (part : MultilinearMap ℂ (fun _ : Fin slots => QuotientState parameters)
        (QuotientRows parameters)) (partConstant : ℝ), 0 ≤ partConstant →
      (∀ argumentsTuple, rowsGradeNorm boundGrade (part argumentsTuple) ≤
        partConstant * oneHighArgumentSum boundGrade argumentsTuple) →
      rowsGradeNorm boundGrade (diagonalDerivative part order base directions) ≤
        (slots : ℝ) ^ order * (partConstant * ((slots : ℝ) * (1 + bound) ^ slots)) *
          oneHighStateExpression boundGrade base directions := by
    intro slots part partConstant partNonneg partBound
    unfold diagonalDerivative
    apply (rowsGradeNorm_sum_le boundGrade _ _).trans
    have perInsertion : ∀ insertion ∈ slotInjections order slots,
        rowsGradeNorm boundGrade (part (slotAssign insertion base directions)) ≤
          partConstant * ((slots : ℝ) * (1 + bound) ^ slots) *
            oneHighStateExpression boundGrade base directions := by
      intro insertion membership
      apply (partBound _).trans
      have assignBound := slotAssign_oneHigh_bound membership boundGrade base directions
        bound baseBounded
      calc partConstant * oneHighArgumentSum boundGrade
            (slotAssign insertion base directions) ≤
          partConstant * ((slots : ℝ) * (1 + bound) ^ slots *
            oneHighStateExpression boundGrade base directions) :=
            mul_le_mul_of_nonneg_left assignBound partNonneg
        _ = partConstant * ((slots : ℝ) * (1 + bound) ^ slots) *
            oneHighStateExpression boundGrade base directions := by ring
    apply (Finset.sum_le_sum perInsertion).trans
    rw [Finset.sum_const, nsmul_eq_mul]
    have cardLe : ((slotInjections order slots).card : ℝ) ≤ (slots : ℝ) ^ order := by
      have finsetCard := Finset.card_le_card (Finset.subset_univ (slotInjections order slots))
      rw [Finset.card_univ] at finsetCard
      have functionCard : Fintype.card (Fin order → Fin slots) = slots ^ order := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
      rw [functionCard] at finsetCard
      calc ((slotInjections order slots).card : ℝ) ≤ ((slots ^ order : ℕ) : ℝ) :=
          Nat.cast_le.mpr finsetCard
        _ = (slots : ℝ) ^ order := by push_cast; ring
    have termNonneg : (0 : ℝ) ≤ partConstant * ((slots : ℝ) * (1 + bound) ^ slots) *
        oneHighStateExpression boundGrade base directions :=
      mul_nonneg (mul_nonneg partNonneg (mul_nonneg (Nat.cast_nonneg _)
        (pow_nonneg (by linarith) _))) exprNonneg
    calc ((slotInjections order slots).card : ℝ) *
          (partConstant * ((slots : ℝ) * (1 + bound) ^ slots) *
            oneHighStateExpression boundGrade base directions) ≤
        (slots : ℝ) ^ order * (partConstant * ((slots : ℝ) * (1 + bound) ^ slots) *
          oneHighStateExpression boundGrade base directions) :=
          mul_le_mul_of_nonneg_right cardLe termNonneg
      _ = (slots : ℝ) ^ order * (partConstant * ((slots : ℝ) * (1 + bound) ^ slots)) *
          oneHighStateExpression boundGrade base directions := by ring
  have zeroDiag : rowsGradeNorm boundGrade (diagonalDerivative
      (quotientDegreeZeroPart parameters) order base directions) ≤
      zeroC * oneHighStateExpression boundGrade base directions := by
    rcases Nat.eq_zero_or_pos order with rfl | positive
    · rw [diagonalDerivative_zeroth]
      apply (zeroBound _).trans
      apply le_mul_of_one_le_right zeroNonneg
      unfold oneHighStateExpression oneHighArgumentSum
      rw [Finset.univ_eq_empty, Finset.prod_empty, Finset.sum_empty, mul_one, add_zero]
      have s6 := stateNorm_nonneg (boundGrade + 6) base
      linarith
    · rw [diagonalDerivative_zero_of_lt _ _ _ _ positive, rowsGradeNorm_zero]
      exact mul_nonneg zeroNonneg exprNonneg
  have oneDiag := diagBound (quotientDegreeOnePart parameters cellLength) oneC
    oneNonneg oneBound
  have twoDiag := diagBound (quotientDegreeTwoPart parameters cellLength) twoC
    twoNonneg twoBound
  have threeDiag := diagBound (quotientDegreeThreePart parameters) threeC
    threeNonneg threeBound
  have fourDiag := diagBound (quotientDegreeFourPart parameters) fourC
    fourNonneg fourBound
  unfold quotientRowsDerivative
  apply (rowsGradeNorm_add_le boundGrade _ _).trans
  apply (add_le_add ((rowsGradeNorm_add_le boundGrade _ _).trans (add_le_add
    ((rowsGradeNorm_add_le boundGrade _ _).trans (add_le_add
      ((rowsGradeNorm_add_le boundGrade _ _).trans (add_le_add zeroDiag oneDiag))
      twoDiag)) threeDiag)) fourDiag).trans
  apply le_trans (le_of_eq (by push_cast; ring))
    (mul_le_mul_of_nonneg_right (le_abs_self _) exprNonneg)

end Grad.NonlinearQuotientBounds
