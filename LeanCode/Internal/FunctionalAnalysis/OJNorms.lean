import OJWeak

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (PhysicalValue FieldL2 OrderedFields)
open scoped BigOperators ContDiff

namespace Grad.WeightedJets.Ordered

theorem orderedDerivative_multiplicity_sum (dimension order rank : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (bound : rank ≤ order)
    (jet : WJet dimension order domain exponent) :
    (∑ word : Fin rank → Fin 2, ‖orderedDerivative dimension order rank domain exponent bound jet word‖ ^ 2) =
      ∑ zeros : Fin (rank + 1), (rank.choose zeros.val : ℝ) *
        ‖canonicalFamily dimension order rank domain exponent bound jet zeros‖ ^ 2 :=
  Grad.OrderedMultiplicity.multiplicity_formula rank (canonicalFamily dimension order rank domain exponent bound jet)

theorem orderedDerivative_multiplicity_norm (dimension order rank : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (bound : rank ≤ order)
    (jet : WJet dimension order domain exponent) :
    ‖orderedDerivative dimension order rank domain exponent bound jet‖ ^ 2 =
      ∑ zeros : Fin (rank + 1), (rank.choose zeros.val : ℝ) *
        ‖canonicalFamily dimension order rank domain exponent bound jet zeros‖ ^ 2 :=
  (Grad.GenericCarriers.tensor_norm_sq rank (orderedDerivative dimension order rank domain exponent bound jet)).trans
    (orderedDerivative_multiplicity_sum dimension order rank domain exponent bound jet)

theorem orderedDerivative_normComparison (dimension order rank : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (exponent : JetIndex order → ℕ) (bound : rank ≤ order)
    (jet : WJet dimension order domain exponent) :
    ‖Grad.OrderedMultiplicity.multiTensor rank (canonicalFamily dimension order rank domain exponent bound jet)‖ ≤
      ‖orderedDerivative dimension order rank domain exponent bound jet‖ ∧
    ‖orderedDerivative dimension order rank domain exponent bound jet‖ ≤ Real.sqrt (rank.factorial : ℝ) *
      ‖Grad.OrderedMultiplicity.multiTensor rank (canonicalFamily dimension order rank domain exponent bound jet)‖ := by
  have comparison := Grad.OrderedMultiplicity.Weak.normComparison dimension rank domain openDomain
    (base dimension order domain exponent jet) (orderedDerivative dimension order rank domain exponent bound jet)
    (orderedDerivative_weakFamily dimension order rank domain exponent bound jet)
  rw [canonicalFamily_identification] at comparison
  exact comparison

theorem canonical_norm_le (dimension order rank : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (bound : rank ≤ order)
    (jet : WJet dimension order domain exponent) :
    ‖Grad.OrderedMultiplicity.multiTensor rank (canonicalFamily dimension order rank domain exponent bound jet)‖ ≤ ‖jet‖ := by
  classical
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  change Grad.OrderedMultiplicity.topMulti rank (canonicalFamily dimension order rank domain exponent bound jet) ^ 2 ≤ ‖jet‖ ^ 2
  rw [Grad.OrderedMultiplicity.topMulti_sq, jet_norm_sq]
  calc
    _ ≤ ∑ zeros : Fin (rank + 1), ‖jet.val (topIndex bound zeros)‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro zeros _inside
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
        (Inclusions.inverse_norm_le dimension domain (exponent (topIndex bound zeros)) (jet.val (topIndex bound zeros)))
    _ = ∑ index ∈ Finset.univ.image (topIndex bound), ‖jet.val index‖ ^ 2 := by
      rw [Finset.sum_image]
      intro first _first second _second equality
      exact topIndex_injective bound equality
    _ ≤ ∑ index : JetIndex order, ‖jet.val index‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun index _inside _outside => sq_nonneg ‖jet.val index‖)

theorem orderedDerivative_norm_le (dimension order rank : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (bound : rank ≤ order)
    (jet : WJet dimension order domain exponent) :
    ‖orderedDerivative dimension order rank domain exponent bound jet‖ ≤ Real.sqrt (rank.factorial : ℝ) * ‖jet‖ := by
  change Grad.OrderedMultiplicity.topOrdered rank (canonicalFamily dimension order rank domain exponent bound jet) ≤ _
  exact (Grad.OrderedMultiplicity.norm_comparison rank
    (canonicalFamily dimension order rank domain exponent bound jet)).2.trans
      (mul_le_mul_of_nonneg_left (canonical_norm_le dimension order rank domain exponent bound jet) (Real.sqrt_nonneg _))

theorem orderedDerivative_opNorm_le (dimension order rank : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (bound : rank ≤ order) :
    ‖orderedDerivative dimension order rank domain exponent bound‖ ≤ Real.sqrt (rank.factorial : ℝ) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _)
  intro jet
  exact orderedDerivative_norm_le dimension order rank domain exponent bound jet

theorem orderedDerivative_zero (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order domain exponent)
    (word : Fin 0 → Fin 2) :
    orderedDerivative dimension order 0 domain exponent (Nat.zero_le order) jet word =
      base dimension order domain exponent jet := by
  rw [orderedDerivative_apply, wordIndex_zero, Realization.recoveredDerivative_zero]

theorem orderedDerivative_zero_norm (dimension order : ℕ) (domain : Set Spatial)
    (exponent : JetIndex order → ℕ) (jet : WJet dimension order domain exponent) :
    ‖orderedDerivative dimension order 0 domain exponent (Nat.zero_le order) jet‖ =
      ‖base dimension order domain exponent jet‖ := by
  change Grad.OrderedMultiplicity.topOrdered 0
    (canonicalFamily dimension order 0 domain exponent (Nat.zero_le order) jet) = _
  rw [Grad.OrderedMultiplicity.topOrdered_zero]
  change ‖Realization.recoveredDerivative dimension order domain exponent (zeroIndex order) jet‖ = _
  rw [Realization.recoveredDerivative_zero]

end Grad.WeightedJets.Ordered
