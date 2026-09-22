import SCD6AveragedDerivatives

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollarDivision
open Grad.RepresentedKernel.SpatialProduct

def sourceOrigin : ClosedDisk := ⟨0, by change ‖(0 : SpatialPlane)‖ ≤ 1; norm_num⟩

/-- Vanishing of the actual Cartesian jets of orders strictly below `depth`. -/
def VanishingJets {dimension : ℕ} (depth : ℕ) (field : ClosedJet dimension) : Prop :=
  ∀ order < depth, ∀ word : CartesianWord order, closedDerivative field order word sourceOrigin = 0

theorem VanishingJets.value {dimension depth : ℕ} {field : ClosedJet dimension}
    (flat : VanishingJets (depth + 1) field) : field.value (ambientClosedDisk 0) = 0 := by
  have origin : ambientClosedDisk (0 : SpatialPlane) = sourceOrigin := ambientClosedDisk_coe sourceOrigin
  rw [origin]
  simpa only [closedDerivative_zero_order] using flat 0 (by omega) emptyCartesianWord

theorem VanishingJets.phaseWeighted {dimension depth : ℕ}
    (parameters : PhaseParameters) (cell : ℤ) {field : ClosedJet dimension}
    (flat : VanishingJets depth field) : VanishingJets depth (phaseWeightedJet parameters cell field) := by
  intro order smaller word
  rw [phaseWeightedJet_derivative]
  change (∑ selected : Finset (Fin order), _ •
    closedDerivative field selectedᶜ.card (subword word selectedᶜ) sourceOrigin) = 0
  apply Finset.sum_eq_zero
  intro selected _
  rw [flat selectedᶜ.card (lt_of_le_of_lt (by simpa using selectedᶜ.card_le_univ) smaller), smul_zero]

def hadamardChild {dimension : ℕ} (field : ClosedJet dimension) (coordinate : Fin 2) : ClosedJet dimension :=
  rayAverageJet (shiftedClosedJet field (fun _ : Fin 1 => coordinate))

theorem hadamardChild_derivative_bound {dimension order : ℕ}
    (field : ClosedJet dimension) (coordinate : Fin 2) (word : CartesianWord order) :
    ‖closedDerivative (hadamardChild field coordinate) order word‖ ≤
      ‖closedDerivative field (order + 1) (Fin.append word (fun _ => coordinate))‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro point
  exact (rayAverage_derivative_bound _ word point).trans_eq
    (congrArg norm (shiftedClosedJet_closedDerivative field _ order word))

theorem VanishingJets.hadamardChild {dimension depth : ℕ}
    {field : ClosedJet dimension} (flat : VanishingJets (depth + 1) field)
    (coordinate : Fin 2) : VanishingJets depth (hadamardChild field coordinate) := by
  intro order smaller word
  rw [Grad.ExhaustionSourceAllocation.hadamardChild, rayAverage_derivative]
  trans ∫ _scale in (0 : ℝ)..1, (0 : ComplexEuclidean dimension)
  · apply intervalIntegral.integral_congr
    intro scale _
    have original := smoothClosedExtension_derivative
      (shiftedClosedJet field (fun _ : Fin 1 => coordinate)) word sourceOrigin
    change cartesianDerivative order word (smoothClosedExtension _) 0 = _ at original
    simp only [sourceOrigin, smul_zero]
    rw [original, shiftedClosedJet_closedDerivative, flat (order + 1) (by omega), smul_zero]
  · simp

end Grad.ExhaustionSourceAllocation
