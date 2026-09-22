import OM1Proof
import WTCInterface

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Grad.OrderedMultiplicity.Weak

open Grad.GenericCarriers
open Grad.PDEBootstrap (Spatial)
open Grad.WeakTesting.Commutation (HasWeakOrderedDerivative SameCounts directionCount)

theorem directionCount_zero (rank : ℕ) (word : Fin rank → Fin 2) :
    directionCount word 0 = (countZeros word).val := by
  change Fintype.card {position : Fin rank // word position = 0} = (zeroPositions word).card
  rw [Fintype.card_subtype]
  rfl

theorem directionCount_one (rank : ℕ) (word : Fin rank → Fin 2) :
    directionCount word 1 = rank - (countZeros word).val := one_count rank word

theorem sameCounts_canonical (rank : ℕ) (word : Fin rank → Fin 2) :
    SameCounts word (canonicalWord rank (countZeros word)) := by
  intro direction
  fin_cases direction
  · change directionCount word 0 = directionCount (canonicalWord rank (countZeros word)) 0
    rw [directionCount_zero, directionCount_zero, canonical_count]
  · change directionCount word 1 = directionCount (canonicalWord rank (countZeros word)) 1
    rw [directionCount_one, directionCount_one, canonical_count]

def IsWeakDerivativeFamily (dimension rank : ℕ) (domain : Set Spatial)
    (field : FieldL2 dimension domain) (derivatives : OrderedFields dimension rank domain) : Prop :=
  ∀ word : Fin rank → Fin 2,
    HasWeakOrderedDerivative dimension domain rank word field (derivatives word)

def canonicalFamily (dimension rank : ℕ) (domain : Set Spatial)
    (derivatives : OrderedFields dimension rank domain) : Fin (rank + 1) → FieldL2 dimension domain :=
  fun zeros => derivatives (canonicalWord rank zeros)

def canonicalMultiIndexFamily (dimension rank : ℕ) (domain : Set Spatial)
    (derivatives : OrderedFields dimension rank domain) : TopMultiIndex rank → FieldL2 dimension domain :=
  fun beta => canonicalFamily dimension rank domain derivatives ((multiIndexEquiv rank).symm beta)

def IdentificationGoal : Prop :=
  ∀ (dimension rank : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ (field : FieldL2 dimension domain) (derivatives : OrderedFields dimension rank domain),
      IsWeakDerivativeFamily dimension rank domain field derivatives →
        (∀ word : Fin rank → Fin 2, derivatives word =
          canonicalFamily dimension rank domain derivatives (countZeros word)) ∧
        derivatives = orderedTensor rank (canonicalFamily dimension rank domain derivatives)

def MultiplicityGoal : Prop :=
  ∀ (dimension rank : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ (field : FieldL2 dimension domain) (derivatives : OrderedFields dimension rank domain),
      IsWeakDerivativeFamily dimension rank domain field derivatives →
        (∑ word : Fin rank → Fin 2, ‖derivatives word‖ ^ 2 =
          ∑ zeros : Fin (rank + 1), (rank.choose zeros.val : ℝ) *
            ‖canonicalFamily dimension rank domain derivatives zeros‖ ^ 2) ∧
        ‖derivatives‖ ^ 2 = ∑ zeros : Fin (rank + 1), (rank.choose zeros.val : ℝ) *
          ‖canonicalFamily dimension rank domain derivatives zeros‖ ^ 2

def MultiIndexGoal : Prop :=
  ∀ (dimension rank : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ (field : FieldL2 dimension domain) (derivatives : OrderedFields dimension rank domain),
      IsWeakDerivativeFamily dimension rank domain field derivatives →
        ∑ word : Fin rank → Fin 2, ‖derivatives word‖ ^ 2 =
          ∑ beta : TopMultiIndex rank, (rank.choose beta.val.1 : ℝ) *
            ‖canonicalMultiIndexFamily dimension rank domain derivatives beta‖ ^ 2

def NormGoal : Prop :=
  ∀ (dimension rank : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ (field : FieldL2 dimension domain) (derivatives : OrderedFields dimension rank domain),
      IsWeakDerivativeFamily dimension rank domain field derivatives →
        ‖multiTensor rank (canonicalFamily dimension rank domain derivatives)‖ ≤ ‖derivatives‖ ∧
        ‖derivatives‖ ≤ Real.sqrt (rank.factorial : ℝ) *
          ‖multiTensor rank (canonicalFamily dimension rank domain derivatives)‖

def ZeroGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ (field : FieldL2 dimension domain) (derivatives : OrderedFields dimension 0 domain),
      IsWeakDerivativeFamily dimension 0 domain field derivatives →
        (∀ word : Fin 0 → Fin 2, derivatives word = field) ∧
        ‖derivatives‖ = ‖field‖ ∧
        ‖multiTensor 0 (canonicalFamily dimension 0 domain derivatives)‖ = ‖field‖

def BlockGoal : Prop := IdentificationGoal ∧ MultiplicityGoal ∧ MultiIndexGoal ∧ NormGoal ∧ ZeroGoal

end Grad.OrderedMultiplicity.Weak
