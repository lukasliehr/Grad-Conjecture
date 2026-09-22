import GC10Raw
import OM1Proof
import SP1Words
import COR01Topology

noncomputable section

set_option maxHeartbeats 1000000

open Set
open Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets
open Grad.GaugeCoefficients.Envelope
open scoped BigOperators ContDiff ENNReal Topology

namespace Grad.GaugeCoefficients.Algebra

open Grad.OrderedMultiplicity

/-- Restriction of a word on the concatenated Cartesian directions to the two
coordinate blocks. -/
def splitWordEquiv (firstOrder secondOrder : ℕ) :
    (Fin (firstOrder + secondOrder) → Fin 2) ≃
      (Fin firstOrder → Fin 2) × (Fin secondOrder → Fin 2) where
  toFun word :=
    (fun position => word (Fin.castAdd secondOrder position),
      fun position => word (Fin.natAdd firstOrder position))
  invFun pair := Fin.addCases pair.1 pair.2
  left_inv word := by
    funext position
    refine Fin.addCases ?_ ?_ position
    · intro first
      simp
    · intro second
      simp
  right_inv pair := by
    apply Prod.ext <;> funext position <;> simp

/-- A selected set of positions is equivalently a pair of binary words, one
on each Cartesian coordinate block; zeros mark selected positions. -/
def selectionWordPairEquiv (firstOrder secondOrder : ℕ) :
    Finset (Fin (firstOrder + secondOrder)) ≃
      (Fin firstOrder → Fin 2) × (Fin secondOrder → Fin 2) :=
  (wordSubsetEquiv (firstOrder + secondOrder)).symm.trans
    (splitWordEquiv firstOrder secondOrder)

theorem selectionWordPairEquiv_left_zero_iff (firstOrder secondOrder : ℕ)
    (selected : Finset (Fin (firstOrder + secondOrder))) (position : Fin firstOrder) :
    (selectionWordPairEquiv firstOrder secondOrder selected).1 position = 0 ↔
      Fin.castAdd secondOrder position ∈ selected := by
  simp [selectionWordPairEquiv, splitWordEquiv, wordSubsetEquiv]

theorem selectionWordPairEquiv_right_zero_iff (firstOrder secondOrder : ℕ)
    (selected : Finset (Fin (firstOrder + secondOrder))) (position : Fin secondOrder) :
    (selectionWordPairEquiv firstOrder secondOrder selected).2 position = 0 ↔
      Fin.natAdd firstOrder position ∈ selected := by
  simp [selectionWordPairEquiv, splitWordEquiv, wordSubsetEquiv]

theorem sum_word_count {Value : Type*} [AddCommMonoid Value]
    (rank : ℕ) (family : Fin (rank + 1) → Value) :
    ∑ word : Fin rank → Fin 2, family (countZeros word) =
      ∑ zeros : Fin (rank + 1), rank.choose zeros.val • family zeros := by
  rw [← Fintype.sum_fiberwise' (@countZeros rank) family]
  apply Finset.sum_congr rfl
  intro zeros _membership
  simp only [Finset.sum_const, Finset.card_univ]
  rw [fiber_card]

theorem sum_word_pair_count {Value : Type*} [AddCommMonoid Value]
    (firstOrder secondOrder : ℕ)
    (family : Fin (firstOrder + 1) → Fin (secondOrder + 1) → Value) :
    ∑ pair : (Fin firstOrder → Fin 2) × (Fin secondOrder → Fin 2),
        family (countZeros pair.1) (countZeros pair.2) =
      ∑ firstCount : Fin (firstOrder + 1),
        ∑ secondCount : Fin (secondOrder + 1),
          (firstOrder.choose firstCount.val * secondOrder.choose secondCount.val) •
            family firstCount secondCount := by
  rw [Fintype.sum_prod_type]
  calc
    (∑ firstWord : Fin firstOrder → Fin 2,
        ∑ secondWord : Fin secondOrder → Fin 2,
          family (countZeros firstWord) (countZeros secondWord)) =
      ∑ firstWord : Fin firstOrder → Fin 2,
        ∑ secondCount : Fin (secondOrder + 1),
          secondOrder.choose secondCount.val •
            family (countZeros firstWord) secondCount := by
      apply Finset.sum_congr rfl
      intro firstWord _membership
      exact sum_word_count secondOrder
        (fun secondCount => family (countZeros firstWord) secondCount)
    _ = ∑ firstCount : Fin (firstOrder + 1),
        firstOrder.choose firstCount.val •
          ∑ secondCount : Fin (secondOrder + 1),
            secondOrder.choose secondCount.val • family firstCount secondCount := by
      exact sum_word_count firstOrder (fun firstCount =>
        ∑ secondCount : Fin (secondOrder + 1),
          secondOrder.choose secondCount.val • family firstCount secondCount)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro firstCount _membership
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro secondCount _membership
      rw [smul_smul]

open Grad.RepresentedKernel.SpatialProduct
open Grad.WeakTesting.Commutation

def selectedCartesianSubword (index : CartesianMultiIndex)
    (selected : Finset (Fin (cartesianOrder index))) : Word selected.card :=
  subword (cartesianMultiIndexWord index) selected

def selectedZeroFiberEquiv (index : CartesianMultiIndex)
    (selected : Finset (Fin (cartesianOrder index))) :
    {position : Fin selected.card // selectedCartesianSubword index selected position = 0} ≃
      {position : Fin index.1 //
        (selectionWordPairEquiv index.1 index.2 selected).1 position = 0} := by
  let forward := fun position :
      {position : Fin selected.card // selectedCartesianSubword index selected position = 0} => by
    let original : selected := selected.orderIsoOfFin rfl position.val
    have zero : (original.val : ℕ) < index.1 := by
      have property := position.property
      change (if (original.val : ℕ) < index.1 then (0 : Fin 2) else 1) = 0 at property
      split at property <;> simp_all
    refine (⟨⟨original.val, zero⟩, ?_⟩ :
      {position : Fin index.1 //
        (selectionWordPairEquiv index.1 index.2 selected).1 position = 0})
    apply (selectionWordPairEquiv_left_zero_iff index.1 index.2 selected _).2
    have equality : Fin.castAdd index.2 ⟨original.val, zero⟩ = original.val := Fin.ext rfl
    rw [equality]
    exact original.property
  apply Equiv.ofBijective forward
  constructor
  · intro first second equality
    apply Subtype.ext
    apply (selected.orderIsoOfFin rfl).injective
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun value => value.val.val) equality
  · intro target
    have membership : Fin.castAdd index.2 target.val ∈ selected :=
      (selectionWordPairEquiv_left_zero_iff index.1 index.2 selected target.val).1
        target.property
    let original : selected := ⟨Fin.castAdd index.2 target.val, membership⟩
    let sourcePosition := (selected.orderIsoOfFin rfl).symm original
    have sourceProperty : selectedCartesianSubword index selected sourcePosition = 0 := by
      change cartesianMultiIndexWord index
        (selected.orderEmbOfFin rfl sourcePosition) = 0
      rw [← selected.coe_orderIsoOfFin_apply]
      simp [sourcePosition, original, cartesianMultiIndexWord]
    refine ⟨⟨sourcePosition, sourceProperty⟩, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    change (↑((selected.orderIsoOfFin rfl) sourcePosition) : Fin (cartesianOrder index)).val =
      target.val.val
    rw [(selected.orderIsoOfFin rfl).apply_symm_apply]
    rfl

def selectedOneFiberEquiv (index : CartesianMultiIndex)
    (selected : Finset (Fin (cartesianOrder index))) :
    {position : Fin selected.card // selectedCartesianSubword index selected position = 1} ≃
      {position : Fin index.2 //
        (selectionWordPairEquiv index.1 index.2 selected).2 position = 0} := by
  let forward := fun position :
      {position : Fin selected.card // selectedCartesianSubword index selected position = 1} => by
    let original : selected := selected.orderIsoOfFin rfl position.val
    have lower : index.1 ≤ (original.val : ℕ) := by
      have property := position.property
      change (if (original.val : ℕ) < index.1 then (0 : Fin 2) else 1) = 1 at property
      split at property <;> simp_all
    have upper : (original.val : ℕ) - index.1 < index.2 := by
      have bound := original.val.isLt
      change (original.val : ℕ) < index.1 + index.2 at bound
      omega
    refine (⟨⟨(original.val : ℕ) - index.1, upper⟩, ?_⟩ :
      {position : Fin index.2 //
        (selectionWordPairEquiv index.1 index.2 selected).2 position = 0})
    apply (selectionWordPairEquiv_right_zero_iff index.1 index.2 selected _).2
    have equality : Fin.natAdd index.1
        ⟨(original.val : ℕ) - index.1, upper⟩ = original.val := by
      apply Fin.ext
      change index.1 + ((original.val : ℕ) - index.1) = original.val
      omega
    rw [equality]
    exact original.property
  apply Equiv.ofBijective forward
  constructor
  · intro first second equality
    apply Subtype.ext
    apply (selected.orderIsoOfFin rfl).injective
    apply Subtype.ext
    apply Fin.ext
    have firstLower : index.1 ≤
        ((selected.orderIsoOfFin rfl first.val).val : ℕ) := by
      have property := first.property
      change (if ((selected.orderIsoOfFin rfl first.val).val : ℕ) < index.1
        then (0 : Fin 2) else 1) = 1 at property
      split at property <;> simp_all
    have secondLower : index.1 ≤
        ((selected.orderIsoOfFin rfl second.val).val : ℕ) := by
      have property := second.property
      change (if ((selected.orderIsoOfFin rfl second.val).val : ℕ) < index.1
        then (0 : Fin 2) else 1) = 1 at property
      split at property <;> simp_all
    have valueEquality :
        ((selected.orderIsoOfFin rfl first.val).val : ℕ) - index.1 =
          ((selected.orderIsoOfFin rfl second.val).val : ℕ) - index.1 := by
      exact congrArg (fun value => value.val.val) equality
    change ((selected.orderIsoOfFin rfl first.val).val : ℕ) =
      ((selected.orderIsoOfFin rfl second.val).val : ℕ)
    omega
  · intro target
    have membership : Fin.natAdd index.1 target.val ∈ selected :=
      (selectionWordPairEquiv_right_zero_iff index.1 index.2 selected target.val).1
        target.property
    let original : selected := ⟨Fin.natAdd index.1 target.val, membership⟩
    let sourcePosition := (selected.orderIsoOfFin rfl).symm original
    have sourceProperty : selectedCartesianSubword index selected sourcePosition = 1 := by
      change cartesianMultiIndexWord index
        (selected.orderEmbOfFin rfl sourcePosition) = 1
      rw [← selected.coe_orderIsoOfFin_apply]
      simp [sourcePosition, original, cartesianMultiIndexWord]
    refine ⟨⟨sourcePosition, sourceProperty⟩, ?_⟩
    apply Subtype.ext
    apply Fin.ext
    change ((↑((selected.orderIsoOfFin rfl) sourcePosition) :
      Fin (cartesianOrder index)).val - index.1) = target.val
    rw [(selected.orderIsoOfFin rfl).apply_symm_apply]
    change index.1 + target.val - index.1 = target.val
    omega

theorem selectedCartesianSubword_zero_count (index : CartesianMultiIndex)
    (selected : Finset (Fin (cartesianOrder index))) :
    directionCount (selectedCartesianSubword index selected) 0 =
      (countZeros (selectionWordPairEquiv index.1 index.2 selected).1).val := by
  unfold directionCount countZeros zeroPositions
  rw [Fintype.card_congr (selectedZeroFiberEquiv index selected)]
  simp only [Fintype.card_subtype]

theorem selectedCartesianSubword_one_count (index : CartesianMultiIndex)
    (selected : Finset (Fin (cartesianOrder index))) :
    directionCount (selectedCartesianSubword index selected) 1 =
      (countZeros (selectionWordPairEquiv index.1 index.2 selected).2).val := by
  unfold directionCount countZeros zeroPositions
  rw [Fintype.card_congr (selectedOneFiberEquiv index selected)]
  simp only [Fintype.card_subtype]

theorem selectionWordPairEquiv_compl_left_count (firstOrder secondOrder : ℕ)
    (selected : Finset (Fin (firstOrder + secondOrder))) :
    (countZeros (selectionWordPairEquiv firstOrder secondOrder selectedᶜ).1).val =
      firstOrder - (countZeros (selectionWordPairEquiv firstOrder secondOrder selected).1).val := by
  unfold countZeros
  have zeroPositions_compl :
      zeroPositions (selectionWordPairEquiv firstOrder secondOrder selectedᶜ).1 =
        (zeroPositions (selectionWordPairEquiv firstOrder secondOrder selected).1)ᶜ := by
    ext position
    simp only [zeroPositions, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_compl]
    rw [selectionWordPairEquiv_left_zero_iff,
      selectionWordPairEquiv_left_zero_iff]
    simp
  change (zeroPositions (selectionWordPairEquiv firstOrder secondOrder selectedᶜ).1).card =
    firstOrder -
      (zeroPositions (selectionWordPairEquiv firstOrder secondOrder selected).1).card
  rw [zeroPositions_compl, Finset.card_compl, Fintype.card_fin]

theorem selectionWordPairEquiv_compl_right_count (firstOrder secondOrder : ℕ)
    (selected : Finset (Fin (firstOrder + secondOrder))) :
    (countZeros (selectionWordPairEquiv firstOrder secondOrder selectedᶜ).2).val =
      secondOrder - (countZeros (selectionWordPairEquiv firstOrder secondOrder selected).2).val := by
  unfold countZeros
  have zeroPositions_compl :
      zeroPositions (selectionWordPairEquiv firstOrder secondOrder selectedᶜ).2 =
        (zeroPositions (selectionWordPairEquiv firstOrder secondOrder selected).2)ᶜ := by
    ext position
    simp only [zeroPositions, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_compl]
    rw [selectionWordPairEquiv_right_zero_iff,
      selectionWordPairEquiv_right_zero_iff]
    simp
  change (zeroPositions (selectionWordPairEquiv firstOrder secondOrder selectedᶜ).2).card =
    secondOrder -
      (zeroPositions (selectionWordPairEquiv firstOrder secondOrder selected).2).card
  rw [zeroPositions_compl, Finset.card_compl, Fintype.card_fin]

def selectionDerivativeSplit {grade : ℕ} (index : DerivativeIndex grade)
    (selected : Finset (Fin (cartesianOrder (derivativeMultiIndex index)))) :
    DerivativeSplit index :=
  (countZeros (selectionWordPairEquiv index.1.1 index.1.2 selected).1,
    countZeros (selectionWordPairEquiv index.1.1 index.1.2 selected).2)

theorem selectedCartesianSubword_compl_zero_count {grade : ℕ}
    (index : DerivativeIndex grade)
    (selected : Finset (Fin (cartesianOrder (derivativeMultiIndex index)))) :
    directionCount
        (selectedCartesianSubword (derivativeMultiIndex index) selectedᶜ) 0 =
      (upperDerivativeIndex index (selectionDerivativeSplit index selected)).1.1 := by
  rw [selectedCartesianSubword_zero_count]
  exact selectionWordPairEquiv_compl_left_count index.1.1 index.1.2 selected

theorem selectedCartesianSubword_compl_one_count {grade : ℕ}
    (index : DerivativeIndex grade)
    (selected : Finset (Fin (cartesianOrder (derivativeMultiIndex index)))) :
    directionCount
        (selectedCartesianSubword (derivativeMultiIndex index) selectedᶜ) 1 =
      (upperDerivativeIndex index (selectionDerivativeSplit index selected)).1.2 := by
  rw [selectedCartesianSubword_one_count]
  exact selectionWordPairEquiv_compl_right_count index.1.1 index.1.2 selected

theorem word_direction_count_total (rank : ℕ) (word : Word rank) :
    directionCount word 0 + directionCount word 1 = rank := by
  have cardinality := Fintype.card_congr (Equiv.sigmaFiberEquiv word)
  simpa only [Fintype.card_sigma, Fin.sum_univ_two, Fintype.card_fin,
    directionCount] using cardinality

theorem wordDerivative_cartesianMultiDerivative
    {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {domain : Set Spatial} (openDomain : IsOpen domain) (rank : ℕ) (word : Word rank)
    (function : Spatial → Value) (smooth : ContDiffOn ℝ ∞ function domain)
    (point : Spatial) (inside : point ∈ domain) :
    wordDerivative rank word function point =
      cartesianMultiDerivative (directionCount word 0, directionCount word 1)
        function point := by
  generalize zeroCount : directionCount word 0 = zeros
  generalize oneCount : directionCount word 1 = ones
  have cardinality : zeros + ones = rank := by
    rw [← zeroCount, ← oneCount]
    exact word_direction_count_total rank word
  subst rank
  have canonical := wordDerivative_canonical openDomain zeros ones word
    zeroCount oneCount smooth inside
  change wordDerivative (zeros + ones) word function point =
    wordDerivative (zeros + ones)
      (Grad.WeakTesting.Commutation.canonicalWord zeros ones) function point
  exact canonical

theorem sum_selectionDerivativeSplit {grade : ℕ} {Value : Type*}
    [AddCommMonoid Value] (index : DerivativeIndex grade)
    (family : DerivativeSplit index → Value) :
    ∑ selected : Finset (Fin (cartesianOrder (derivativeMultiIndex index))),
        family (selectionDerivativeSplit index selected) =
      ∑ split : DerivativeSplit index,
        splitMultiplicity index split • family split := by
  let equivalence := selectionWordPairEquiv index.1.1 index.1.2
  calc
    (∑ selected : Finset (Fin (cartesianOrder (derivativeMultiIndex index))),
        family (selectionDerivativeSplit index selected)) =
      ∑ pair : (Fin index.1.1 → Fin 2) × (Fin index.1.2 → Fin 2),
        family (countZeros pair.1, countZeros pair.2) :=
      Fintype.sum_equiv equivalence _ _ (fun selected => rfl)
    _ = ∑ firstCount : Fin (index.1.1 + 1),
        ∑ secondCount : Fin (index.1.2 + 1),
          ((index.1.1 : ℕ).choose firstCount.val *
            (index.1.2 : ℕ).choose secondCount.val) •
            family (firstCount, secondCount) :=
      sum_word_pair_count index.1.1 index.1.2
        (fun firstCount secondCount => family (firstCount, secondCount))
    _ = _ := by
      rw [Fintype.sum_prod_type]
      rfl

end Grad.GaugeCoefficients.Algebra
