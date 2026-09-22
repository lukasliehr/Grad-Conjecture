import OJIndices

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2 OrderedFields)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.Ordered

theorem hasWeakOrderedDerivative_cast (dimension : ℕ) (domain : Set Spatial)
    (firstRank secondRank : ℕ) (rankEquality : firstRank = secondRank)
    (word : Fin firstRank → Fin 2) (field derivative : FieldL2 dimension domain) :
    Grad.WeakTesting.Commutation.HasWeakOrderedDerivative dimension domain firstRank word field derivative ↔
      Grad.WeakTesting.Commutation.HasWeakOrderedDerivative dimension domain secondRank
        (fun position => word (Fin.cast rankEquality.symm position)) field derivative := by
  subst secondRank
  rfl

theorem recoveredDerivative_hasWeak (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (index : JetIndex order)
    (jet : WJet dimension order domain exponent) :
    Grad.WeakTesting.Commutation.HasWeakOrderedDerivative dimension domain (degree index) (derivativeWord index)
      (base dimension order domain exponent jet)
      (Realization.recoveredDerivative dimension order domain exponent index jet) := by
  intro cell vector test smooth compact supported
  exact Realization.recoveredDerivative_weak dimension order domain exponent index jet cell vector
    ⟨test, smooth, compact, supported⟩

theorem orderedDerivative_hasWeak (dimension order rank : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (bound : rank ≤ order)
    (jet : WJet dimension order domain exponent) (word : Fin rank → Fin 2) :
    Grad.WeakTesting.Commutation.HasWeakOrderedDerivative dimension domain rank word
      (base dimension order domain exponent jet)
      (orderedDerivative dimension order rank domain exponent bound jet word) := by
  rw [orderedDerivative_apply]
  apply (Grad.WeakTesting.Commutation.transport dimension domain rank word (jetCanonicalWord bound word)
    (word_sameCounts bound word) (base dimension order domain exponent jet)
    (Realization.recoveredDerivative dimension order domain exponent (wordIndex bound word) jet)).mpr
  exact (hasWeakOrderedDerivative_cast dimension domain (degree (wordIndex bound word)) rank
    (wordIndex_degree bound word) (derivativeWord (wordIndex bound word))
    (base dimension order domain exponent jet)
    (Realization.recoveredDerivative dimension order domain exponent (wordIndex bound word) jet)).mp
      (recoveredDerivative_hasWeak dimension order domain exponent (wordIndex bound word) jet)

theorem orderedDerivative_weakFamily (dimension order rank : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (bound : rank ≤ order)
    (jet : WJet dimension order domain exponent) :
    Grad.OrderedMultiplicity.Weak.IsWeakDerivativeFamily dimension rank domain
      (base dimension order domain exponent jet)
      (orderedDerivative dimension order rank domain exponent bound jet) :=
  orderedDerivative_hasWeak dimension order rank domain exponent bound jet

theorem orderedDerivative_integral (dimension order rank : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (bound : rank ≤ order)
    (jet : WJet dimension order domain exponent) (word : Fin rank → Fin 2)
    (cell : ℤ) (vector : PhysicalValue dimension) (test : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test) (supported : tsupport test ⊆ domain) :
    (∫ point in domain, test point •
      inner ℂ vector (orderedDerivative dimension order rank domain exponent bound jet word point cell)) =
      (-1 : ℂ) ^ rank * ∫ point in domain,
        Grad.WeakTesting.orderedTestDerivative rank word test point •
          inner ℂ vector (base dimension order domain exponent jet point cell) :=
  (Grad.WeakTesting.Commutation.hasWeakOrderedDerivative_iff_integral dimension domain rank word
    (base dimension order domain exponent jet)
    (orderedDerivative dimension order rank domain exponent bound jet word)).mp
      (orderedDerivative_hasWeak dimension order rank domain exponent bound jet word)
        cell vector test smooth compact supported

end Grad.WeightedJets.Ordered
