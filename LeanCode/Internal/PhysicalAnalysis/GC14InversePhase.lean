import NGP01CoordinateBound
import GC13Proof

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open Set MeasureTheory
open scoped BigOperators Topology

namespace Grad.CartesianState

open Grad.ClosedJets
open Grad.AnalyticWeights.Higher

/-- The inverse-phase derivative cost retains the fixed original phase. -/
def inversePhaseDerivativeConstant (parameters : PhaseParameters) (rank : ℕ) : ℝ :=
  commonConstant rank * weightCost rank parameters.gamma 1

theorem inversePhaseDerivativeConstant_nonnegative (parameters : PhaseParameters)
    (rank : ℕ) : 0 ≤ inversePhaseDerivativeConstant parameters rank := by
  apply mul_nonneg (commonConstant_pos rank).le
  have gammaNonnegative := parameters.gamma_pos.le
  unfold weightCost
  split_ifs <;> positivity

theorem phaseInverseWeightedJet_derivative {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) :
    closedDerivative (phaseInverseWeightedJet parameters cell field) order word =
      smoothScalarDerivativeExtension (cartesianInverseWeight parameters cell)
        (cartesianInverseWeight_contDiff parameters cell) field order word := by
  symm
  apply cartesianExtension_unique
  exact smoothScalarDerivativeExtension_spec (cartesianInverseWeight parameters cell)
    (cartesianInverseWeight_contDiff parameters cell) field order word

/-- Original weight cancellation for every Cartesian derivative of its inverse. -/
theorem originalWeight_inverseDerivative_bound
    (parameters : PhaseParameters) (cell : ℤ) (rank : ℕ)
    (word : CartesianWord rank) (point : SpatialPlane) :
    cartesianWeight parameters cell point *
        ‖orderedDerivative rank word (cartesianInverseWeight parameters cell) point‖ ≤
      inversePhaseDerivativeConstant parameters rank * cellFrequency cell ^ rank := by
  have weightPositive := cartesianWeight_pos parameters cell point
  by_cases zeroRank : rank = 0
  · subst rank
    change cartesianWeight parameters cell point *
      ‖cartesianInverseWeight parameters cell point‖ ≤ _
    have inverseNonnegative : 0 ≤ cartesianInverseWeight parameters cell point := by
      unfold cartesianInverseWeight
      rw [Grad.AnalyticWeights.Calculus.inverseWeight_exp]
      exact (Real.exp_pos _).le
    rw [Real.norm_of_nonneg inverseNonnegative, cartesianWeight_mul_inverse]
    simp [inversePhaseDerivativeConstant, commonConstant_zero, weightCost]
  · have positiveRank : 1 ≤ rank := Nat.one_le_iff_ne_zero.mpr zeroRank
    have normBound :=
      (weightGoal parameters.sigma0 parameters.gamma 1 parameters.gamma_pos.le
        zero_le_one rank positiveRank cell point).2.1
    have orderedBound :
        ‖orderedDerivative rank word (cartesianInverseWeight parameters cell) point‖ ≤
          commonConstant rank * weightCost rank parameters.gamma 1 *
            cartesianInverseWeight parameters cell point * cellFrequency cell ^ rank :=
      (orderedDerivative_norm_le rank word (cartesianInverseWeight parameters cell) point).trans
        normBound
    calc
      _ ≤ cartesianWeight parameters cell point *
        (commonConstant rank * weightCost rank parameters.gamma 1 *
          cartesianInverseWeight parameters cell point * cellFrequency cell ^ rank) :=
        mul_le_mul_of_nonneg_left orderedBound weightPositive.le
      _ = (cartesianWeight parameters cell point * cartesianInverseWeight parameters cell point) *
          (inversePhaseDerivativeConstant parameters rank * cellFrequency cell ^ rank) := by
        unfold inversePhaseDerivativeConstant
        ring
      _ = inversePhaseDerivativeConstant parameters rank * cellFrequency cell ^ rank := by
        rw [cartesianWeight_mul_inverse, one_mul]

theorem originalWeight_inverseFactor_bound
    (parameters : PhaseParameters) (cell : ℤ) (rank : ℕ)
    (word : CartesianWord rank) (selected : Finset (Fin rank)) (point : ClosedDisk) :
    cartesianWeight parameters cell point.val *
        ‖smoothScalarDerivativeFactor (cartesianInverseWeight parameters cell)
          (cartesianInverseWeight_contDiff parameters cell) rank word selected point‖ ≤
      inversePhaseDerivativeConstant parameters selected.card * cellFrequency cell ^ selected.card := by
  exact originalWeight_inverseDerivative_bound parameters cell selected.card
    (Grad.RepresentedKernel.SpatialProduct.subword word selected) point.val

/-- Every original closed derivative is explicitly obtained by differentiating
the inverse phase against the weighted closed jet. -/
theorem original_closedDerivative_expansion {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) (point : ClosedDisk) :
    closedDerivative field order word point =
      ∑ selected : Finset (Fin order),
        smoothScalarDerivativeFactor (cartesianInverseWeight parameters cell)
          (cartesianInverseWeight_contDiff parameters cell) order word selected point •
          closedDerivative (phaseWeightedJet parameters cell field) selectedᶜ.card
            (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ) point := by
  rw [← phaseWeightedJet_inverse_right parameters cell field,
    phaseInverseWeightedJet_derivative, phaseWeightedJet_inverse_left]
  rfl

theorem originalWeight_closedDerivative_point_bound {dimension : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (order : ℕ) (word : CartesianWord order) (point : ClosedDisk) :
    cartesianWeight parameters cell point.val * ‖closedDerivative field order word point‖ ≤
      ∑ selected : Finset (Fin order),
        inversePhaseDerivativeConstant parameters selected.card *
          cellFrequency cell ^ selected.card *
          ‖closedDerivative (phaseWeightedJet parameters cell field) selectedᶜ.card
            (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ)‖ := by
  rw [original_closedDerivative_expansion parameters cell field order word point]
  have weightPositive := cartesianWeight_pos parameters cell point.val
  calc
    _ ≤ cartesianWeight parameters cell point.val *
        ∑ selected : Finset (Fin order),
          ‖smoothScalarDerivativeFactor (cartesianInverseWeight parameters cell)
            (cartesianInverseWeight_contDiff parameters cell) order word selected point •
            closedDerivative (phaseWeightedJet parameters cell field) selectedᶜ.card
              (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ) point‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) weightPositive.le
    _ ≤ _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro selected _membership
      rw [norm_smul, ← mul_assoc]
      exact mul_le_mul
        (originalWeight_inverseFactor_bound parameters cell order word selected point)
        (ContinuousMap.norm_coe_le_norm _ point) (norm_nonneg _)
        (mul_nonneg (inversePhaseDerivativeConstant_nonnegative parameters selected.card)
          (pow_nonneg (cellFrequency_pos cell).le _))

end Grad.CartesianState
