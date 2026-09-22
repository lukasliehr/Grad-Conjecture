import AKN1HigherFlatWeightedJets
import SCD7PolarGeometryBounds

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollarDivision

/-- Iterated Hadamard remainder of the whole weighted jet. It is smooth also
at radius zero and involves no singular division. -/
def polarTaylorRemainder {dimension : ℕ} (depth : ℕ) : ClosedJet dimension → (ℝ × ℝ → ComplexEuclidean dimension) :=
  Nat.rec (fun field point => smoothClosedExtension field (polarPlane point))
    (fun _ remainder field point => ∑ coordinate : Fin 2, polarAngularFactor coordinate point •
      remainder (hadamardChild field coordinate) point) depth

theorem polarTaylorRemainder_smooth {dimension : ℕ} (depth : ℕ) (field : ClosedJet dimension) :
    ContDiff ℝ ∞ (polarTaylorRemainder depth field) := by
  induction depth generalizing field with
  | zero => exact (smoothClosedExtension_smooth field).comp polarPlane_smooth
  | succ depth inductionHypothesis =>
    apply ContDiff.sum
    intro coordinate _
    exact (polarAngularFactor_smooth coordinate).smul (inductionHypothesis _)

theorem polarTaylorRemainder_periodic {dimension : ℕ} (depth : ℕ) (field : ClosedJet dimension) :
    Function.Periodic (polarTaylorRemainder depth field) (0, 2 * Real.pi) := by
  induction depth generalizing field with
  | zero =>
    intro point
    change smoothClosedExtension field (polarPlane _) = smoothClosedExtension field (polarPlane point)
    rw [polarPlane_periodic point]
  | succ depth inductionHypothesis =>
    intro point
    simp only [polarTaylorRemainder, polarAngularFactor, Prod.snd_add]
    rw [radialDirection_periodic point.2]
    apply Finset.sum_congr rfl
    intro coordinate _
    exact congrArg (fun value => (radialDirection point.2).ofLp coordinate • value)
      (inductionHypothesis (hadamardChild field coordinate) point)

theorem polarTaylorRemainder_multiply {dimension : ℕ} (depth : ℕ)
    (field : ClosedJet dimension) (flat : VanishingJets depth field)
    (radius angle : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    radius ^ depth • polarTaylorRemainder depth field (radius, angle) =
      field.value (polarClosedPoint radius angle nonnegative bounded) := by
  induction depth generalizing field with
  | zero =>
    simp only [polarTaylorRemainder, pow_zero, one_smul]
    convert smoothClosedExtension_value field (polarClosedPoint radius angle nonnegative bounded) using 1
    rfl
  | succ depth inductionHypothesis =>
    have hadamard := closedJet_hadamard field (polarClosedPoint radius angle nonnegative bounded)
    rw [flat.value, sub_zero] at hadamard
    calc
      _ = ∑ coordinate : Fin 2, (radius * radialDirection angle coordinate) •
          (radius ^ depth • polarTaylorRemainder depth (hadamardChild field coordinate) (radius, angle)) := by
        rw [polarTaylorRemainder, Finset.smul_sum]
        apply Finset.sum_congr rfl
        intro coordinate _
        simp only [polarAngularFactor, smul_smul, pow_succ]
        congr 1
        ring
      _ = ∑ coordinate : Fin 2, (polarPlane (radius, angle) coordinate) •
          rayAverageValue (shiftedClosedJet field (fun _ : Fin 1 => coordinate)) (polarPlane (radius, angle)) := by
        apply Finset.sum_congr rfl
        intro coordinate _
        rw [inductionHypothesis _ (flat.hadamardChild coordinate)]
        simp only [hadamardChild, rayAverageJet, globalClosedJet_value, polarClosedPoint]
        rw [polarPlane_eq]
        rfl
      _ = _ := hadamard.symm

theorem polarTaylorRemainder_weighted {dimension : ℕ} (depth : ℕ)
    (parameters : PhaseParameters) (cell : ℤ) (field : ClosedJet dimension)
    (flat : VanishingJets depth field) (radius angle : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    radius ^ depth • polarTaylorRemainder depth (phaseWeightedJet parameters cell field) (radius, angle) =
      cartesianWeight parameters cell (polarPlane (radius, angle)) •
        field.value (polarClosedPoint radius angle nonnegative bounded) := by
  exact polarTaylorRemainder_multiply depth _ (flat.phaseWeighted parameters cell)
    radius angle nonnegative bounded

end Grad.ExhaustionSourceAllocation
