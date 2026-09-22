import JRConsumer
import OMWProof

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2 OrderedFields)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.Ordered

def topIndex {rank order : ℕ} (bound : rank ≤ order) (zeros : Fin (rank + 1)) : JetIndex order :=
  ⟨(zeros.val, rank - zeros.val),
    (Nat.add_sub_of_le (Nat.le_of_lt_succ zeros.isLt)).le.trans bound⟩

def wordIndex {rank order : ℕ} (bound : rank ≤ order) (word : Fin rank → Fin 2) : JetIndex order :=
  topIndex bound (Grad.OrderedMultiplicity.countZeros word)

theorem topIndex_degree {rank order : ℕ} (bound : rank ≤ order) (zeros : Fin (rank + 1)) :
    degree (topIndex bound zeros) = rank := Nat.add_sub_of_le (Nat.le_of_lt_succ zeros.isLt)

theorem wordIndex_degree {rank order : ℕ} (bound : rank ≤ order) (word : Fin rank → Fin 2) :
    degree (wordIndex bound word) = rank := topIndex_degree bound _

def jetCanonicalWord {rank order : ℕ} (bound : rank ≤ order) (word : Fin rank → Fin 2) :
    Fin rank → Fin 2 :=
  fun position => derivativeWord (wordIndex bound word) (Fin.cast (wordIndex_degree bound word).symm position)

def orderedDerivative (dimension order rank : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (bound : rank ≤ order) :
    WJet dimension order domain exponent →L[ℂ] OrderedFields dimension rank domain :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin rank → Fin 2 => FieldL2 dimension domain)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun word => Realization.recoveredDerivative dimension order domain exponent (wordIndex bound word)))

def canonicalFamily (dimension order rank : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (bound : rank ≤ order)
    (jet : WJet dimension order domain exponent) : Fin (rank + 1) → FieldL2 dimension domain :=
  fun zeros => Realization.recoveredDerivative dimension order domain exponent (topIndex bound zeros) jet

def IndexGoal : Prop :=
  ∀ (rank order : ℕ) (bound : rank ≤ order) (word : Fin rank → Fin 2),
    (wordIndex bound word).val =
      ((Grad.OrderedMultiplicity.countZeros word).val, rank - (Grad.OrderedMultiplicity.countZeros word).val) ∧
    degree (wordIndex bound word) = rank ∧
    jetCanonicalWord bound word = Grad.OrderedMultiplicity.canonicalWord rank (Grad.OrderedMultiplicity.countZeros word) ∧
    Grad.WeakTesting.Commutation.SameCounts word (jetCanonicalWord bound word)

def AssemblyGoal : Prop :=
  ∀ (dimension order rank : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (bound : rank ≤ order) (jet : WJet dimension order domain exponent),
    (∀ word : Fin rank → Fin 2,
      orderedDerivative dimension order rank domain exponent bound jet word =
        Realization.recoveredDerivative dimension order domain exponent (wordIndex bound word) jet) ∧
    ‖orderedDerivative dimension order rank domain exponent bound jet‖ ^ 2 =
      ∑ word : Fin rank → Fin 2,
        ‖Realization.recoveredDerivative dimension order domain exponent (wordIndex bound word) jet‖ ^ 2 ∧
    orderedDerivative dimension order rank domain exponent bound jet =
      Grad.OrderedMultiplicity.orderedTensor rank (canonicalFamily dimension order rank domain exponent bound jet) ∧
    Grad.OrderedMultiplicity.Weak.canonicalFamily dimension rank domain
        (orderedDerivative dimension order rank domain exponent bound jet) =
      canonicalFamily dimension order rank domain exponent bound jet

def WeakGoal : Prop :=
  ∀ (dimension order rank : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (bound : rank ≤ order) (jet : WJet dimension order domain exponent),
    (∀ word : Fin rank → Fin 2,
      Grad.WeakTesting.Commutation.HasWeakOrderedDerivative dimension domain rank word
        (base dimension order domain exponent jet)
        (orderedDerivative dimension order rank domain exponent bound jet word)) ∧
    Grad.OrderedMultiplicity.Weak.IsWeakDerivativeFamily dimension rank domain
      (base dimension order domain exponent jet)
      (orderedDerivative dimension order rank domain exponent bound jet)

def IntegralGoal : Prop :=
  ∀ (dimension order rank : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (bound : rank ≤ order) (jet : WJet dimension order domain exponent)
    (word : Fin rank → Fin 2) (cell : ℤ) (vector : PhysicalValue dimension)
    (test : Spatial → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test → tsupport test ⊆ domain →
      (∫ point in domain, test point •
        inner ℂ vector (orderedDerivative dimension order rank domain exponent bound jet word point cell)) =
        (-1 : ℂ) ^ rank * ∫ point in domain,
          Grad.WeakTesting.orderedTestDerivative rank word test point •
            inner ℂ vector (base dimension order domain exponent jet point cell)

def MultiplicityGoal : Prop :=
  ∀ (dimension order rank : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (bound : rank ≤ order) (jet : WJet dimension order domain exponent),
    (∑ word : Fin rank → Fin 2, ‖orderedDerivative dimension order rank domain exponent bound jet word‖ ^ 2) =
      ∑ zeros : Fin (rank + 1), (rank.choose zeros.val : ℝ) *
        ‖canonicalFamily dimension order rank domain exponent bound jet zeros‖ ^ 2 ∧
    ‖orderedDerivative dimension order rank domain exponent bound jet‖ ^ 2 =
      ∑ zeros : Fin (rank + 1), (rank.choose zeros.val : ℝ) *
        ‖canonicalFamily dimension order rank domain exponent bound jet zeros‖ ^ 2

def NormGoal : Prop :=
  ∀ (dimension order rank : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ (exponent : JetIndex order → ℕ) (bound : rank ≤ order) (jet : WJet dimension order domain exponent),
      ‖Grad.OrderedMultiplicity.multiTensor rank (canonicalFamily dimension order rank domain exponent bound jet)‖ ≤
        ‖orderedDerivative dimension order rank domain exponent bound jet‖ ∧
      ‖orderedDerivative dimension order rank domain exponent bound jet‖ ≤ Real.sqrt (rank.factorial : ℝ) *
        ‖Grad.OrderedMultiplicity.multiTensor rank (canonicalFamily dimension order rank domain exponent bound jet)‖

def BoundGoal : Prop :=
  ∀ (dimension order rank : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (bound : rank ≤ order),
    (∀ jet : WJet dimension order domain exponent,
      ‖Grad.OrderedMultiplicity.multiTensor rank (canonicalFamily dimension order rank domain exponent bound jet)‖ ≤ ‖jet‖) ∧
    (∀ jet : WJet dimension order domain exponent,
      ‖orderedDerivative dimension order rank domain exponent bound jet‖ ≤ Real.sqrt (rank.factorial : ℝ) * ‖jet‖) ∧
    ‖orderedDerivative dimension order rank domain exponent bound‖ ≤ Real.sqrt (rank.factorial : ℝ)

def ZeroGoal : Prop :=
  ∀ (dimension order : ℕ) (domain : Set Spatial) (exponent : JetIndex order → ℕ)
    (jet : WJet dimension order domain exponent),
    (∀ word : Fin 0 → Fin 2,
      orderedDerivative dimension order 0 domain exponent (Nat.zero_le order) jet word =
        base dimension order domain exponent jet) ∧
    ‖orderedDerivative dimension order 0 domain exponent (Nat.zero_le order) jet‖ =
      ‖base dimension order domain exponent jet‖

def CoherenceGoal : Prop :=
  ∀ (dimension lower higher rank : ℕ) (domain : Set Spatial) (gap : ℕ)
    (rankBound : rank ≤ lower) (orderBound : lower ≤ higher)
    (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ)
    (compatible : Inclusions.Compatible orderBound gap source target),
    (orderedDerivative dimension lower rank domain target rankBound).comp
        (Inclusions.inclusion dimension lower higher domain gap orderBound source target compatible) =
      orderedDerivative dimension higher rank domain source (rankBound.trans orderBound)

def BlockGoal : Prop :=
  IndexGoal ∧ AssemblyGoal ∧ WeakGoal ∧ IntegralGoal ∧ MultiplicityGoal ∧ NormGoal ∧ BoundGoal ∧
    ZeroGoal ∧ CoherenceGoal

end Grad.WeightedJets.Ordered
