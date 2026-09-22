import QuotientDerivativeL2

noncomputable section

open Set
open scoped ContDiff BigOperators

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

def coordinateLinear (coordinate : Fin 2) : SpatialPlane →L[ℝ] ℝ :=
  PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) coordinate

theorem linear_list_derivative_nonempty (mapping : SpatialPlane →L[ℝ] ℝ)
    (direction : Fin 2) (rest : List (Fin 2)) :
    cartesianListDerivative (direction :: rest) mapping =
      fun _ => if rest = [] then mapping (spatialBasis direction) else 0 := by
  induction rest generalizing direction with
  | nil =>
    funext point
    simp [cartesianListDerivative, mapping.fderiv]
  | cons next tail inductionHypothesis =>
    change spatialPartial direction (cartesianListDerivative (next :: tail) mapping) = _
    rw [inductionHypothesis]
    funext point
    simp [spatialPartial]

theorem coordinate_derivative_bound (coordinate : Fin 2) {rank : ℕ}
    (word : CartesianWord rank) (point : ClosedDisk) :
    ‖cartesianDerivative rank word (coordinateLinear coordinate) point.val‖ ≤ 1 := by
  cases rank with
  | zero =>
    change ‖point.val coordinate‖ ≤ 1
    exact (PiLp.norm_apply_le point.val coordinate).trans point.property
  | succ rank =>
    rw [← cartesianListDerivative_ofFn isOpen_univ (rank + 1) word
      (coordinateLinear coordinate).contDiff.contDiffOn (mem_univ point.val),
      List.ofFn_succ, linear_list_derivative_nonempty]
    split_ifs
    · change ‖spatialBasis (word 0) coordinate‖ ≤ 1
      exact (PiLp.norm_apply_le (spatialBasis (word 0)) coordinate).trans_eq
        (by simp [spatialBasis, PiLp.norm_single])
    · simp

def coordinateJet {dimension : ℕ} (coordinate : Fin 2) (field : ClosedJet dimension) : ClosedJet dimension :=
  smoothScalarWeightedJet (coordinateLinear coordinate) (coordinateLinear coordinate).contDiff field

theorem coordinateJet_value {dimension : ℕ} (coordinate : Fin 2) (field : ClosedJet dimension)
    (point : ClosedDisk) :
    (coordinateJet coordinate field).value point = point.val coordinate • field.value point := rfl

theorem coordinateJet_weighted {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (coordinate : Fin 2) (field : ClosedJet dimension) :
    phaseWeightedJet parameters cell (coordinateJet coordinate field) =
      coordinateJet coordinate (phaseWeightedJet parameters cell field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change cartesianWeight parameters cell point.val • (point.val coordinate • field.value point) =
    point.val coordinate • (cartesianWeight parameters cell point.val • field.value point)
  exact smul_comm _ _ _

theorem coordinateJet_weighted_L2 {dimension rank : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (coordinate : Fin 2) (field : ClosedJet dimension) (word : CartesianWord rank) :
    ‖closedContinuousToDiskL2 (closedDerivative
      (phaseWeightedJet parameters cell (coordinateJet coordinate field)) rank word)‖ ≤
      ∑ selected : Finset (Fin rank),
        ‖closedContinuousToDiskL2 (closedDerivative (phaseWeightedJet parameters cell field)
          selectedᶜ.card (Grad.AnalyticWeights.Higher.subword word selectedᶜ))‖ := by
  rw [coordinateJet_weighted]
  unfold coordinateJet
  rw [smoothScalarWeightedJet_derivative]
  have bound := closedDiskL2_norm_le_finite_majorant
    (smoothScalarDerivativeExtension (coordinateLinear coordinate) (coordinateLinear coordinate).contDiff
      (phaseWeightedJet parameters cell field) rank word)
    (fun selected : Finset (Fin rank) => closedDerivative (phaseWeightedJet parameters cell field)
      selectedᶜ.card (Grad.AnalyticWeights.Higher.subword word selectedᶜ))
    (fun _ => (1 : ℝ)) (fun _ => zero_le_one)
  simp only [one_mul] at bound
  apply bound
  intro point
  change ‖∑ selected : Finset (Fin rank),
    smoothScalarDerivativeFactor _ _ rank word selected point •
      closedDerivative (phaseWeightedJet parameters cell field) selectedᶜ.card
        (Grad.AnalyticWeights.Higher.subword word selectedᶜ) point‖ ≤ _
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro selected _
  rw [norm_smul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (coordinate_derivative_bound coordinate (Grad.AnalyticWeights.Higher.subword word selected) point)

end Grad.NonlinearQuotientBounds
