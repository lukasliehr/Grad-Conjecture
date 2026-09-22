import QuotientDerivativeInterface
import ProductPhaseDerivative

noncomputable section

open Set
open scoped ContDiff

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.AnalyticWeights.Higher

def spatialPartial {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (direction : Fin 2) (field : SpatialPlane → Value) (point : SpatialPlane) : Value :=
  fderiv ℝ field point (spatialBasis direction)

theorem spatialPartial_smooth {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (direction : Fin 2) {field : SpatialPlane → Value} (smooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (spatialPartial direction field) :=
  (smooth.fderiv_right (by simp)).clm_apply contDiff_const

theorem spatialPartial_eq_ordered {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (direction : Fin 2) (field : SpatialPlane → Value) :
    spatialPartial direction field = cartesianDerivative 1 (fun _ => direction) field := by
  funext point
  simp [spatialPartial, cartesianDerivative, iteratedFDeriv_one_apply]

theorem cartesianDerivative_spatialPartial {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (direction : Fin 2) {field : SpatialPlane → Value}
    (smooth : ContDiff ℝ ∞ field) {rank : ℕ} (word : CartesianWord rank) (point : SpatialPlane) :
    cartesianDerivative rank word (spatialPartial direction field) point =
      cartesianDerivative (rank + 1) (Fin.append word (fun _ => direction)) field point := by
  rw [← cartesianListDerivative_ofFn isOpen_univ rank word
    (spatialPartial_smooth direction smooth).contDiffOn (mem_univ point)]
  change cartesianListDerivative (List.ofFn word)
    (cartesianListDerivative (List.ofFn (fun _ : Fin 1 => direction)) field) point = _
  rw [← cartesianListDerivative_append, ← List.ofFn_fin_append]
  exact cartesianListDerivative_ofFn isOpen_univ (rank + 1)
    (Fin.append word (fun _ => direction)) smooth.contDiffOn (mem_univ point)

theorem phasePartial_derivative_bound (parameters : PhaseParameters) (cell : ℤ)
    (direction : Fin 2) {rank : ℕ} (word : CartesianWord rank) (point : SpatialPlane) :
    ‖cartesianDerivative rank word (spatialPartial direction (cartesianPhase parameters cell)) point‖ ≤
      profileConstant (rank + 1) * cellFrequency cell ^ (rank + 1) := by
  rw [cartesianDerivative_spatialPartial direction (cartesianPhase_contDiff parameters cell)]
  exact (orderedDerivative_norm_le (rank + 1) (Fin.append word (fun _ => direction)) _ point).trans
    (cartesianPhase_iterated_bound parameters cell (rank + 1) (by omega) point)

def partialJet {dimension : ℕ} (direction : Fin 2) (field : ClosedJet dimension) : ClosedJet dimension :=
  shiftedClosedJet field (fun _ : Fin 1 => direction)

@[simp] theorem partialJet_value {dimension : ℕ} (direction : Fin 2) (field : ClosedJet dimension) :
    (partialJet direction field).value = partialCoefficient direction field := rfl

theorem partialJet_closedDerivative {dimension rank : ℕ} (direction : Fin 2)
    (field : ClosedJet dimension) (word : CartesianWord rank) :
    closedDerivative (partialJet direction field) rank word =
      closedDerivative field (rank + 1) (Fin.append word (fun _ => direction)) :=
  shiftedClosedJet_closedDerivative field _ _ word

theorem weightPartial (parameters : PhaseParameters) (cell : ℤ)
    (direction : Fin 2) (point : SpatialPlane) :
    spatialPartial direction (cartesianWeight parameters cell) point =
      cartesianWeight parameters cell point *
        spatialPartial direction (cartesianPhase parameters cell) point := by
  have identity : cartesianWeight parameters cell = fun point => Real.exp (cartesianPhase parameters cell point) :=
    funext (cartesianWeight_exp parameters cell)
  rw [identity]
  unfold spatialPartial
  rw [fderiv_exp ((cartesianPhase_contDiff parameters cell).differentiable (by simp)).differentiableAt]
  rfl

theorem phaseWeighted_partial_value {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (direction : Fin 2) (field : ClosedJet dimension) (point : ClosedDisk) :
    partialCoefficient direction (phaseWeightedJet parameters cell field) point =
      spatialPartial direction (cartesianPhase parameters cell) point.val •
        (phaseWeightedJet parameters cell field).value point +
      cartesianWeight parameters cell point.val • partialCoefficient direction field point := by
  let weighted := fun source => cartesianWeight parameters cell source • smoothClosedExtension field source
  have weightedSmooth : ContDiff ℝ ∞ weighted :=
    (cartesianWeight_contDiff parameters cell).smul (smoothClosedExtension_smooth field)
  have restriction : globalClosedJet weighted weightedSmooth = phaseWeightedJet parameters cell field := by
    apply globalClosedJet_eq_of_restriction
    intro source
    dsimp only [weighted]
    rw [smoothClosedExtension_value, phaseWeightedJet_spec]
  unfold partialCoefficient
  rw [← restriction, globalClosedJet_derivative, ← spatialPartial_eq_ordered]
  change fderiv ℝ weighted point.val (spatialBasis direction) = _
  rw [fderiv_fun_smul ((cartesianWeight_contDiff parameters cell).differentiable (by simp)).differentiableAt
    ((smoothClosedExtension_smooth field).differentiable (by simp)).differentiableAt]
  change cartesianWeight parameters cell point.val •
      spatialPartial direction (smoothClosedExtension field) point.val +
        spatialPartial direction (cartesianWeight parameters cell) point.val •
          smoothClosedExtension field point.val = _
  rw [weightPartial, smoothClosedExtension_value, spatialPartial_eq_ordered,
    smoothClosedExtension_derivative, restriction, phaseWeightedJet_spec]
  rw [smul_smul, mul_comm]
  abel

theorem phaseWeighted_partialJet {dimension : ℕ} (parameters : PhaseParameters) (cell : ℤ)
    (direction : Fin 2) (field : ClosedJet dimension) :
    phaseWeightedJet parameters cell (partialJet direction field) =
      partialJet direction (phaseWeightedJet parameters cell field) -
        smoothScalarWeightedJet (spatialPartial direction (cartesianPhase parameters cell))
          (spatialPartial_smooth direction (cartesianPhase_contDiff parameters cell))
          (phaseWeightedJet parameters cell field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    ContinuousMap.add_apply, ContinuousMap.neg_apply]
  change cartesianWeight parameters cell point.val • partialCoefficient direction field point =
    partialCoefficient direction (phaseWeightedJet parameters cell field) point +
      -(spatialPartial direction (cartesianPhase parameters cell) point.val •
        (phaseWeightedJet parameters cell field).value point)
  rw [phaseWeighted_partial_value]
  abel

end Grad.NonlinearQuotientBounds
