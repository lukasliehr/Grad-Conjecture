import GC1Proof
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Basic

noncomputable section

open scoped BigOperators

namespace Grad.OrderedMultiplicity

open Grad.GenericCarriers

universe valueUniverse

def zeroPositions {rank : ℕ} (word : Fin rank → Fin 2) : Finset (Fin rank) :=
  Finset.univ.filter (fun position => word position = 0)

def countZeros {rank : ℕ} (word : Fin rank → Fin 2) : Fin (rank + 1) :=
  ⟨(zeroPositions word).card, by
    have bound := Finset.card_le_card (Finset.filter_subset
      (fun position => word position = 0) (Finset.univ : Finset (Fin rank)))
    simpa only [zeroPositions, Finset.card_univ, Fintype.card_fin] using Nat.lt_succ_of_le bound⟩

def canonicalWord (rank : ℕ) (zeros : Fin (rank + 1)) : Fin rank → Fin 2 :=
  fun position => if position.val < zeros.val then 0 else 1

def TopMultiIndex (rank : ℕ) := {beta : ℕ × ℕ // beta.1 + beta.2 = rank}

def multiIndexEquiv (rank : ℕ) : Fin (rank + 1) ≃ TopMultiIndex rank where
  toFun zeros := ⟨(zeros.val, rank - zeros.val), Nat.add_sub_of_le (Nat.le_of_lt_succ zeros.isLt)⟩
  invFun beta := ⟨beta.val.1, by have degree := beta.property; omega⟩
  left_inv zeros := by apply Fin.ext; rfl
  right_inv beta := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have degree := beta.property
      dsimp
      omega

instance topMultiIndexFintype (rank : ℕ) : Fintype (TopMultiIndex rank) :=
  Fintype.ofEquiv (Fin (rank + 1)) (multiIndexEquiv rank)

def orderedTensor {Value : Type*} [NormedAddCommGroup Value] (rank : ℕ)
    (family : Fin (rank + 1) → Value) : Tensor rank Value :=
  tensorOfCoordinates rank (fun word => family (countZeros word))

def multiTensor {Value : Type*} [NormedAddCommGroup Value] (rank : ℕ)
    (family : Fin (rank + 1) → Value) : PiLp 2 (fun _ : Fin (rank + 1) => Value) :=
  WithLp.toLp 2 family

def topOrdered {Value : Type*} [NormedAddCommGroup Value] (rank : ℕ)
    (family : Fin (rank + 1) → Value) : ℝ := ‖orderedTensor rank family‖

def topMulti {Value : Type*} [NormedAddCommGroup Value] (rank : ℕ)
    (family : Fin (rank + 1) → Value) : ℝ := ‖multiTensor rank family‖

def CombinatorialGoal : Prop :=
  (∀ (rank : ℕ) (zeros : Fin (rank + 1)),
    Fintype.card {word : Fin rank → Fin 2 // countZeros word = zeros} = rank.choose zeros.val) ∧
  (∀ (rank : ℕ) (zeros : Fin (rank + 1)), countZeros (canonicalWord rank zeros) = zeros) ∧
  (∀ (rank : ℕ) (zeros : Fin (rank + 1)),
    (multiIndexEquiv rank zeros).val = (zeros.val, rank - zeros.val)) ∧
  (∀ (rank : ℕ) (word : Fin rank → Fin 2),
    Fintype.card {position : Fin rank // word position = 1} = rank - (countZeros word).val)

def MultiplicityGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    (rank : ℕ) (family : Fin (rank + 1) → Value),
    ∑ word : Fin rank → Fin 2, ‖family (countZeros word)‖ ^ 2 =
      ∑ zeros : Fin (rank + 1), (rank.choose zeros.val : ℝ) * ‖family zeros‖ ^ 2

def MultiIndexGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    (rank : ℕ) (family : TopMultiIndex rank → Value),
    ∑ word : Fin rank → Fin 2, ‖family (multiIndexEquiv rank (countZeros word))‖ ^ 2 =
      ∑ beta : TopMultiIndex rank, (rank.choose beta.val.1 : ℝ) * ‖family beta‖ ^ 2

def NormGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    (rank : ℕ) (family : Fin (rank + 1) → Value),
    topMulti rank family ^ 2 = ∑ zeros : Fin (rank + 1), ‖family zeros‖ ^ 2 ∧
    topOrdered rank family ^ 2 = ∑ word : Fin rank → Fin 2, ‖family (countZeros word)‖ ^ 2 ∧
    topMulti rank family ≤ topOrdered rank family ∧
    topOrdered rank family ≤ Real.sqrt (rank.factorial : ℝ) * topMulti rank family

def ZeroGoal : Prop :=
  ∀ (Value : Type valueUniverse) [NormedAddCommGroup Value] [InnerProductSpace ℂ Value]
    (family : Fin 1 → Value), topMulti 0 family = ‖family 0‖ ∧ topOrdered 0 family = ‖family 0‖

def AlgebraBlockGoal : Prop :=
  CombinatorialGoal ∧ MultiplicityGoal.{valueUniverse} ∧ MultiIndexGoal.{valueUniverse} ∧
    NormGoal.{valueUniverse} ∧ ZeroGoal.{valueUniverse}

end Grad.OrderedMultiplicity
