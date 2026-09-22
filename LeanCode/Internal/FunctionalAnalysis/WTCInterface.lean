import GC1Proof
import WT2Proof
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.List.FinRange

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open scoped ContDiff

namespace Grad.WeakTesting.Commutation

def directionCount {rank : ℕ} (word : Fin rank → Fin 2) (direction : Fin 2) : ℕ :=
  Fintype.card {position : Fin rank // word position = direction}

def SameCounts {rank : ℕ} (first second : Fin rank → Fin 2) : Prop :=
  ∀ direction : Fin 2, directionCount first direction = directionCount second direction

def canonicalWord (zeros ones : ℕ) : Fin (zeros + ones) → Fin 2 :=
  fun position => if position.val < zeros then 0 else 1

def signedDerivativePairing (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Grad.GenericCarriers.PhysicalValue dimension) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test)
    (rank : ℕ) (word : Fin rank → Fin 2) :
    Grad.GenericCarriers.FieldL2 dimension domain →L[ℂ] ℂ :=
  ((-1 : ℂ) ^ rank) •
    orderedDerivativePairing dimension domain cell vector test smoothness compactSupport rank word

def HasWeakOrderedDerivative (dimension : ℕ) (domain : Set Spatial) (rank : ℕ)
    (word : Fin rank → Fin 2) (field derivative : Grad.GenericCarriers.FieldL2 dimension domain) :
    Prop :=
  ∀ (cell : ℤ) (vector : Grad.GenericCarriers.PhysicalValue dimension) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test),
    tsupport test ⊆ domain →
      compactPairing dimension domain cell vector test smoothness compactSupport derivative =
        signedDerivativePairing dimension domain cell vector test smoothness compactSupport rank word
          field

def WordPermutationGoal : Prop :=
  ∀ (rank : ℕ) (first second : Fin rank → Fin 2), SameCounts first second →
    ∃ permutation : Equiv.Perm (Fin rank), second = first ∘ permutation

def SmoothGoal : Prop :=
  (∀ (rank : ℕ) (word : Fin rank → Fin 2) (permutation : Equiv.Perm (Fin rank))
    (test : Spatial → ℝ), ContDiff ℝ ∞ test →
      orderedTestDerivative rank (word ∘ permutation) test = orderedTestDerivative rank word test) ∧
  (∀ (rank : ℕ) (first second : Fin rank → Fin 2), SameCounts first second →
    ∀ test : Spatial → ℝ, ContDiff ℝ ∞ test →
      orderedTestDerivative rank first test = orderedTestDerivative rank second test)

def PairingGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Grad.GenericCarriers.PhysicalValue dimension) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test)
    (rank : ℕ) (first second : Fin rank → Fin 2), SameCounts first second →
      signedDerivativePairing dimension domain cell vector test smoothness compactSupport rank first =
        signedDerivativePairing dimension domain cell vector test smoothness compactSupport rank second

def TransportGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial) (rank : ℕ) (first second : Fin rank → Fin 2),
    SameCounts first second → ∀ field derivative : Grad.GenericCarriers.FieldL2 dimension domain,
      HasWeakOrderedDerivative dimension domain rank first field derivative ↔
        HasWeakOrderedDerivative dimension domain rank second field derivative

def WeakEqualityGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ (rank : ℕ) (first second : Fin rank → Fin 2), SameCounts first second →
      ∀ field firstDerivative secondDerivative : Grad.GenericCarriers.FieldL2 dimension domain,
        HasWeakOrderedDerivative dimension domain rank first field firstDerivative →
        HasWeakOrderedDerivative dimension domain rank second field secondDerivative →
          firstDerivative = secondDerivative

def RepresentativeGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ (rank : ℕ) (firstWord secondWord : Fin rank → Fin 2), SameCounts firstWord secondWord →
      ∀ (field : Grad.GenericCarriers.FieldL2 dimension domain)
        (first second : Spatial → Grad.GenericCarriers.CellValues dimension)
        (firstMembership : MemLp first 2 (volume.restrict domain))
        (secondMembership : MemLp second 2 (volume.restrict domain)),
        HasWeakOrderedDerivative dimension domain rank firstWord field
          (firstMembership.toLp first) →
        HasWeakOrderedDerivative dimension domain rank secondWord field
          (secondMembership.toLp second) → first =ᵐ[volume.restrict domain] second

def CanonicalGoal : Prop :=
  ∀ zeros ones : ℕ,
    directionCount (canonicalWord zeros ones) 0 = zeros ∧
    directionCount (canonicalWord zeros ones) 1 = ones ∧
    ∀ word : Fin (zeros + ones) → Fin 2,
      directionCount word 0 = zeros → directionCount word 1 = ones →
      ∀ test : Spatial → ℝ, ContDiff ℝ ∞ test →
        orderedTestDerivative (zeros + ones) word test =
          orderedTestDerivative (zeros + ones) (canonicalWord zeros ones) test

def ZeroGoal : Prop :=
  ∀ (dimension : ℕ) (domain : Set Spatial), IsOpen domain →
    ∀ (word : Fin 0 → Fin 2) (field derivative : Grad.GenericCarriers.FieldL2 dimension domain),
      HasWeakOrderedDerivative dimension domain 0 word field derivative ↔ derivative = field

def BlockGoal : Prop :=
  WordPermutationGoal ∧ SmoothGoal ∧ PairingGoal ∧ TransportGoal ∧ WeakEqualityGoal ∧
    RepresentativeGoal ∧ CanonicalGoal ∧ ZeroGoal

end Grad.WeakTesting.Commutation
