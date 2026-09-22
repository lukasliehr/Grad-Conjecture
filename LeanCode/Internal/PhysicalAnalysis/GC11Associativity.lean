import GC11Algebra

noncomputable section

set_option maxHeartbeats 3000000

open Grad.GenericCarriers Grad.ClosedJets Grad.GaugeCoefficients.Envelope
open scoped BigOperators Topology

namespace Grad.GaugeCoefficients.Neumann

open Grad.GaugeCoefficients.Algebra

/-- Reindex three independent cells by their total and the first two cells. -/
def tripleConvolutionEquiv : (ℤ × (ℤ × ℤ)) ≃ ((ℤ × ℤ) × ℤ) where
  toFun pair := ((pair.2.1, pair.2.2), pair.1 - pair.2.1 - pair.2.2)
  invFun triple := (triple.1.1 + triple.1.2 + triple.2, triple.1)
  left_inv pair := by
    rcases pair with ⟨total, ⟨first, second⟩⟩
    apply Prod.ext
    · dsimp
      omega
    · rfl
  right_inv triple := by
    rcases triple with ⟨⟨first, second⟩, third⟩
    apply Prod.ext
    · rfl
    · dsimp
      omega

theorem tripleCoefficientNorm_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (first second third : BaseCoefficient L sigma gamma ell dimension)
    (point : ClosedDisk) :
    Summable (fun triple : (ℤ × ℤ) × ℤ =>
      ‖coefficientValue first triple.1.1 point‖ *
        ‖coefficientValue second triple.1.2 point‖ *
          ‖coefficientValue third triple.2 point‖) := by
  have firstSummable := coefficientValue_point_norm_summable admissible first point
  have secondSummable := coefficientValue_point_norm_summable admissible second point
  have thirdSummable := coefficientValue_point_norm_summable admissible third point
  have pairSummable : Summable (fun pair : ℤ × ℤ =>
      ‖coefficientValue first pair.1 point‖ *
        ‖coefficientValue second pair.2 point‖) :=
    firstSummable.mul_of_nonneg secondSummable
      (fun cell => norm_nonneg (coefficientValue first cell point))
      (fun cell => norm_nonneg (coefficientValue second cell point))
  exact pairSummable.mul_of_nonneg thirdSummable
    (fun pair => mul_nonneg
      (norm_nonneg (coefficientValue first pair.1 point))
      (norm_nonneg (coefficientValue second pair.2 point)))
    (fun cell => norm_nonneg (coefficientValue third cell point))

theorem tripleCoefficientNorm_fixed_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (first second third : BaseCoefficient L sigma gamma ell dimension)
    (cell : ℤ) (point : ClosedDisk) :
    Summable (fun pair : ℤ × ℤ =>
      ‖coefficientValue first pair.1 point‖ *
        ‖coefficientValue second pair.2 point‖ *
          ‖coefficientValue third (cell - pair.1 - pair.2) point‖) := by
  have reindexed := tripleConvolutionEquiv.summable_iff.mpr
    (tripleCoefficientNorm_summable admissible first second third point)
  exact reindexed.prod_factor cell

theorem coefficientTripleComposition_summable {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (first second third : BaseCoefficient L sigma gamma ell dimension)
    (cell : ℤ) (point : ClosedDisk) :
    Summable (fun pair : ℤ × ℤ =>
      ((coefficientValue first pair.1 point).comp
        (coefficientValue second pair.2 point)).comp
          (coefficientValue third (cell - pair.1 - pair.2) point)) := by
  apply Summable.of_norm
  exact Summable.of_nonneg_of_le
    (fun pair => norm_nonneg
      (((coefficientValue first pair.1 point).comp
        (coefficientValue second pair.2 point)).comp
          (coefficientValue third (cell - pair.1 - pair.2) point)))
    (fun pair => by
      calc
        ‖((coefficientValue first pair.1 point).comp
            (coefficientValue second pair.2 point)).comp
              (coefficientValue third (cell - pair.1 - pair.2) point)‖ ≤
            ‖(coefficientValue first pair.1 point).comp
              (coefficientValue second pair.2 point)‖ *
                ‖coefficientValue third (cell - pair.1 - pair.2) point‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (‖coefficientValue first pair.1 point‖ *
              ‖coefficientValue second pair.2 point‖) *
                ‖coefficientValue third (cell - pair.1 - pair.2) point‖ :=
          mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_comp_le _ _)
            (norm_nonneg _))
    (tripleCoefficientNorm_fixed_summable admissible first second third cell point)

theorem coefficientComposition_associative {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {dimension : ℕ}
    (first second third : BaseCoefficient L sigma gamma ell dimension) :
    coefficientComposition admissible 0
        (coefficientComposition admissible 0 first second) third =
      coefficientComposition admissible 0 first
        (coefficientComposition admissible 0 second third) := by
  apply baseCoefficient_ext
  intro cell point
  rw [coefficientComposition_value, coefficientComposition_value]
  simp_rw [coefficientComposition_value admissible]
  let composition := ContinuousLinearMap.compL ℂ
    (PhysicalValue dimension) (PhysicalValue dimension) (PhysicalValue dimension)
  have normalizedSummable :=
    coefficientTripleComposition_summable admissible first second third cell point
  have leftPairSummable : Summable (fun pair : ℤ × ℤ =>
      ((coefficientValue first pair.2 point).comp
        (coefficientValue second (pair.1 - pair.2) point)).comp
          (coefficientValue third (cell - pair.1) point)) := by
    apply (cellConvolutionEquiv.summable_iff.mpr normalizedSummable).congr
    intro pair
    apply ContinuousLinearMap.ext
    intro value
    dsimp [cellConvolutionEquiv]
    rw [show cell - pair.2 - (pair.1 - pair.2) = cell - pair.1 by omega]
  have rightPairSummable : Summable (fun pair : ℤ × ℤ =>
      (coefficientValue first pair.1 point).comp
        ((coefficientValue second pair.2 point).comp
          (coefficientValue third (cell - pair.1 - pair.2) point))) := by
    apply normalizedSummable.congr
    intro pair
    apply ContinuousLinearMap.ext
    intro value
    rfl
  calc
    (∑' outerCell : ℤ,
        (∑' middleCell : ℤ,
          (coefficientValue first middleCell point).comp
            (coefficientValue second (outerCell - middleCell) point)).comp
              (coefficientValue third (cell - outerCell) point)) =
      ∑' outerCell : ℤ, ∑' middleCell : ℤ,
        ((coefficientValue first middleCell point).comp
          (coefficientValue second (outerCell - middleCell) point)).comp
            (coefficientValue third (cell - outerCell) point) := by
      apply tsum_congr
      intro outerCell
      let composeRight :=
        (ContinuousLinearMap.apply ℂ (OperatorValue dimension dimension)
          (coefficientValue third (cell - outerCell) point)).comp composition
      have pairSummable := coefficientValueComposition_fixed_summable admissible
        first second outerCell point
      change composeRight (∑' middleCell : ℤ,
          (coefficientValue first middleCell point).comp
            (coefficientValue second (outerCell - middleCell) point)) =
        ∑' middleCell : ℤ, composeRight
          ((coefficientValue first middleCell point).comp
            (coefficientValue second (outerCell - middleCell) point))
      rw [composeRight.map_tsum pairSummable]
    _ = ∑' pair : ℤ × ℤ,
        ((coefficientValue first pair.2 point).comp
          (coefficientValue second (pair.1 - pair.2) point)).comp
            (coefficientValue third (cell - pair.1) point) :=
      leftPairSummable.tsum_prod.symm
    _ = ∑' pair : ℤ × ℤ,
        ((coefficientValue first pair.1 point).comp
          (coefficientValue second pair.2 point)).comp
            (coefficientValue third (cell - pair.1 - pair.2) point) := by
      let term := fun pair : ℤ × ℤ =>
        ((coefficientValue first pair.1 point).comp
          (coefficientValue second pair.2 point)).comp
            (coefficientValue third (cell - pair.1 - pair.2) point)
      calc
        _ = ∑' pair : ℤ × ℤ, term (cellConvolutionEquiv pair) := by
          apply tsum_congr
          intro pair
          apply ContinuousLinearMap.ext
          intro value
          dsimp [term, cellConvolutionEquiv]
          rw [show cell - pair.2 - (pair.1 - pair.2) = cell - pair.1 by omega]
        _ = ∑' pair : ℤ × ℤ, term pair :=
          cellConvolutionEquiv.tsum_eq term
    _ = ∑' pair : ℤ × ℤ,
        (coefficientValue first pair.1 point).comp
          ((coefficientValue second pair.2 point).comp
            (coefficientValue third (cell - pair.1 - pair.2) point)) := by
      apply tsum_congr
      intro pair
      apply ContinuousLinearMap.ext
      intro value
      rfl
    _ = ∑' outerCell : ℤ, ∑' middleCell : ℤ,
        (coefficientValue first outerCell point).comp
          ((coefficientValue second middleCell point).comp
            (coefficientValue third (cell - outerCell - middleCell) point)) :=
      rightPairSummable.tsum_prod
    _ = ∑' outerCell : ℤ,
        (coefficientValue first outerCell point).comp
          (∑' middleCell : ℤ,
            (coefficientValue second middleCell point).comp
              (coefficientValue third ((cell - outerCell) - middleCell) point)) := by
      apply tsum_congr
      intro outerCell
      have pairSummable := coefficientValueComposition_fixed_summable admissible
        second third (cell - outerCell) point
      let composeLeft := composition (coefficientValue first outerCell point)
      change (∑' middleCell : ℤ, composeLeft
          ((coefficientValue second middleCell point).comp
            (coefficientValue third (cell - outerCell - middleCell) point))) =
        composeLeft (∑' middleCell : ℤ,
          (coefficientValue second middleCell point).comp
            (coefficientValue third (cell - outerCell - middleCell) point))
      exact (composeLeft.map_tsum pairSummable).symm

end Grad.GaugeCoefficients.Neumann
