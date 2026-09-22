import OJInterface

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2 OrderedFields)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.Ordered

theorem topIndex_injective {rank order : ℕ} (bound : rank ≤ order) :
    Function.Injective (topIndex bound) := by
  intro first second equality
  apply Fin.ext
  exact congrArg (fun index : JetIndex order => index.val.1) equality

theorem wordIndex_pair {rank order : ℕ} (bound : rank ≤ order) (word : Fin rank → Fin 2) :
    (wordIndex bound word).val =
      ((Grad.OrderedMultiplicity.countZeros word).val, rank - (Grad.OrderedMultiplicity.countZeros word).val) := rfl

theorem jetCanonicalWord_eq {rank order : ℕ} (bound : rank ≤ order) (word : Fin rank → Fin 2) :
    jetCanonicalWord bound word =
      Grad.OrderedMultiplicity.canonicalWord rank (Grad.OrderedMultiplicity.countZeros word) := rfl

theorem word_sameCounts {rank order : ℕ} (bound : rank ≤ order) (word : Fin rank → Fin 2) :
    Grad.WeakTesting.Commutation.SameCounts word (jetCanonicalWord bound word) :=
  Grad.OrderedMultiplicity.Weak.sameCounts_canonical rank word

theorem orderedDerivative_apply (dimension order rank : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (bound : rank ≤ order)
    (jet : WJet dimension order domain exponent) (word : Fin rank → Fin 2) :
    orderedDerivative dimension order rank domain exponent bound jet word =
      Realization.recoveredDerivative dimension order domain exponent (wordIndex bound word) jet := rfl

theorem orderedDerivative_norm_sq (dimension order rank : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (bound : rank ≤ order)
    (jet : WJet dimension order domain exponent) :
    ‖orderedDerivative dimension order rank domain exponent bound jet‖ ^ 2 =
      ∑ word : Fin rank → Fin 2,
        ‖Realization.recoveredDerivative dimension order domain exponent (wordIndex bound word) jet‖ ^ 2 :=
  Grad.GenericCarriers.tensor_norm_sq rank (orderedDerivative dimension order rank domain exponent bound jet)

theorem orderedDerivative_eq_orderedTensor (dimension order rank : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (bound : rank ≤ order)
    (jet : WJet dimension order domain exponent) :
    orderedDerivative dimension order rank domain exponent bound jet =
      Grad.OrderedMultiplicity.orderedTensor rank (canonicalFamily dimension order rank domain exponent bound jet) := rfl

theorem canonicalFamily_identification (dimension order rank : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (bound : rank ≤ order)
    (jet : WJet dimension order domain exponent) :
    Grad.OrderedMultiplicity.Weak.canonicalFamily dimension rank domain
        (orderedDerivative dimension order rank domain exponent bound jet) =
      canonicalFamily dimension order rank domain exponent bound jet := by
  funext zeros
  change Realization.recoveredDerivative dimension order domain exponent
    (topIndex bound (Grad.OrderedMultiplicity.countZeros (Grad.OrderedMultiplicity.canonicalWord rank zeros))) jet = _
  rw [Grad.OrderedMultiplicity.canonical_count]
  rfl

theorem wordIndex_zero {order : ℕ} (bound : 0 ≤ order) (word : Fin 0 → Fin 2) :
    wordIndex bound word = zeroIndex order := by
  have countZero : Grad.OrderedMultiplicity.countZeros word = 0 := by
    apply Fin.ext
    have countBound := (Grad.OrderedMultiplicity.countZeros word).isLt
    change (Grad.OrderedMultiplicity.countZeros word).val = 0
    omega
  change topIndex bound (Grad.OrderedMultiplicity.countZeros word) = zeroIndex order
  rw [countZero]
  rfl

theorem wordIndex_inclusion {rank lower higher : ℕ} (rankBound : rank ≤ lower)
    (orderBound : lower ≤ higher) (word : Fin rank → Fin 2) :
    Inclusions.indexInclusion orderBound (wordIndex rankBound word) =
      wordIndex (rankBound.trans orderBound) word := rfl

theorem orderedDerivative_inclusion_apply (dimension lower higher rank : ℕ) (domain : Set Spatial)
    (gap : ℕ) (rankBound : rank ≤ lower) (orderBound : lower ≤ higher)
    (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ)
    (compatible : Inclusions.Compatible orderBound gap source target)
    (jet : WJet dimension higher domain source) :
    orderedDerivative dimension lower rank domain target rankBound
        (Inclusions.inclusion dimension lower higher domain gap orderBound source target compatible jet) =
      orderedDerivative dimension higher rank domain source (rankBound.trans orderBound) jet := by
  apply PiLp.ext
  intro word
  exact Realization.recoveredDerivative_inclusion_apply dimension lower higher domain gap orderBound
    source target compatible (wordIndex rankBound word) jet

theorem orderedDerivative_inclusion (dimension lower higher rank : ℕ) (domain : Set Spatial)
    (gap : ℕ) (rankBound : rank ≤ lower) (orderBound : lower ≤ higher)
    (source : JetIndex higher → ℕ) (target : JetIndex lower → ℕ)
    (compatible : Inclusions.Compatible orderBound gap source target) :
    (orderedDerivative dimension lower rank domain target rankBound).comp
        (Inclusions.inclusion dimension lower higher domain gap orderBound source target compatible) =
      orderedDerivative dimension higher rank domain source (rankBound.trans orderBound) := by
  apply ContinuousLinearMap.ext
  intro jet
  exact orderedDerivative_inclusion_apply dimension lower higher rank domain gap rankBound orderBound
    source target compatible jet

end Grad.WeightedJets.Ordered
