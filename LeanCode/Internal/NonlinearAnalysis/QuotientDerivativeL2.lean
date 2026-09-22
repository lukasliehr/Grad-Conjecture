import QuotientDerivativeJet
import TangentialZeroJets
import ProductDiskL2

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.AnalyticWeights.Higher

def closedValueL2Linear {dimension : ℕ} :
    C(ClosedDisk, ComplexEuclidean dimension) →ₗ[ℂ] DiskL2 dimension where
  toFun := closedContinuousToDiskL2
  map_add' := closedContinuousToDiskL2_add
  map_smul' := closedContinuousToDiskL2_smul

theorem smoothScalarWeightedJet_derivative {dimension rank : ℕ}
    (scalar : SpatialPlane → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (field : ClosedJet dimension) (word : CartesianWord rank) :
    closedDerivative (smoothScalarWeightedJet scalar smooth field) rank word =
      smoothScalarDerivativeExtension scalar smooth field rank word := by
  symm
  apply cartesianExtension_unique
  exact smoothScalarDerivativeExtension_spec scalar smooth field rank word

theorem phasePartial_multiplier_L2 {dimension rank : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (direction : Fin 2) (field : ClosedJet dimension) (word : CartesianWord rank) :
    ‖closedContinuousToDiskL2 (closedDerivative
      (smoothScalarWeightedJet (spatialPartial direction (cartesianPhase parameters cell))
        (spatialPartial_smooth direction (cartesianPhase_contDiff parameters cell)) field) rank word)‖ ≤
      ∑ selected : Finset (Fin rank),
        (profileConstant (selected.card + 1) * cellFrequency cell ^ (selected.card + 1)) *
          ‖closedContinuousToDiskL2 (closedDerivative field selectedᶜ.card (subword word selectedᶜ))‖ := by
  rw [smoothScalarWeightedJet_derivative]
  apply closedDiskL2_norm_le_finite_majorant _
    (fun selected : Finset (Fin rank) => closedDerivative field selectedᶜ.card (subword word selectedᶜ))
    (fun selected => profileConstant (selected.card + 1) * cellFrequency cell ^ (selected.card + 1))
    (fun selected => mul_nonneg (profileConstant_nonnegative _) (pow_nonneg (cellFrequency_pos _).le _))
  intro point
  change ‖∑ selected : Finset (Fin rank),
    smoothScalarDerivativeFactor _ _ rank word selected point •
      closedDerivative field selectedᶜ.card (subword word selectedᶜ) point‖ ≤ _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro selected _
  rw [norm_smul]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact phasePartial_derivative_bound parameters cell direction (subword word selected) point.val

theorem partialJet_weighted_L2 {dimension rank : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (direction : Fin 2) (field : ClosedJet dimension) (word : CartesianWord rank) :
    ‖closedContinuousToDiskL2 (closedDerivative
      (phaseWeightedJet parameters cell (partialJet direction field)) rank word)‖ ≤
      ‖closedContinuousToDiskL2 (closedDerivative (phaseWeightedJet parameters cell field)
        (rank + 1) (Fin.append word (fun _ => direction)))‖ +
      ∑ selected : Finset (Fin rank),
        (profileConstant (selected.card + 1) * cellFrequency cell ^ (selected.card + 1)) *
          ‖closedContinuousToDiskL2 (closedDerivative (phaseWeightedJet parameters cell field)
            selectedᶜ.card (subword word selectedᶜ))‖ := by
  rw [phaseWeighted_partialJet]
  change ‖closedValueL2Linear (closedDerivativeLinear rank word (_ - _))‖ ≤ _
  rw [map_sub, map_sub]
  apply (norm_sub_le _ _).trans
  apply add_le_add
  · rw [show closedDerivativeLinear rank word
        (partialJet direction (phaseWeightedJet parameters cell field)) =
      closedDerivative (phaseWeightedJet parameters cell field) (rank + 1)
        (Fin.append word (fun _ => direction)) from partialJet_closedDerivative direction _ word]
    exact le_rfl
  · exact phasePartial_multiplier_L2 parameters cell direction (phaseWeightedJet parameters cell field) word

end Grad.NonlinearQuotientBounds
