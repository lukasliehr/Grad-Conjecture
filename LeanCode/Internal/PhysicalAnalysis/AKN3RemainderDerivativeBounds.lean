import AKN2HigherPolarRemainder

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.ExhaustionSourceAllocation

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollarDivision
open Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.BoundaryTrace

theorem closedJet_tensor_of_word_bound {dimension order : ℕ}
    (field : ClosedJet dimension) (bound : ℝ)
    (words : ∀ word : CartesianWord order, ‖closedDerivative field order word‖ ≤ bound)
    (point : ClosedDisk) :
    ‖iteratedFDeriv ℝ order (smoothClosedExtension field) point.val‖ ≤
      planarWordCoefficientSum order * bound := by
  have tensor := jetOperatorDerivative_point_bound (order := order) field point
  rw [jetOperatorDerivative_eq_closedPlane, ← smoothClosedExtension_higherDerivative] at tensor
  apply tensor.trans
  rw [planarWordCoefficientSum, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro word _
  exact mul_le_mul_of_nonneg_left ((ContinuousMap.norm_coe_le_norm _ _).trans (words word))
    (norm_nonneg _)

def wordEnvelopeConstant (order : ℕ) : ℝ :=
  ∑ rank ∈ Finset.range (order + 1), planarWordCoefficientSum rank

theorem wordEnvelopeConstant_nonnegative (order : ℕ) : 0 ≤ wordEnvelopeConstant order :=
  Finset.sum_nonneg (fun rank _ => planarWordCoefficientSum_nonnegative rank)

theorem closedJet_envelope_of_word_bound {dimension : ℕ}
    (field : ClosedJet dimension) (order : ℕ) (bound : ℝ)
    (words : ∀ rank ≤ order, ∀ word : CartesianWord rank, ‖closedDerivative field rank word‖ ≤ bound)
    (point : ClosedDisk) :
    spatialJetEnvelope (smoothClosedExtension field) order point.val ≤
      wordEnvelopeConstant order * bound := by
  rw [spatialJetEnvelope, wordEnvelopeConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro rank member
  exact closedJet_tensor_of_word_bound field bound (words rank (by have := Finset.mem_range.mp member; omega)) point

def remainderDerivativeConstant (depth : ℕ) : ℕ → ℝ :=
  Nat.rec (fun order => order.factorial * wordEnvelopeConstant order * polarGeometryBound order ^ order)
    (fun _ remainder order => 2 * ∑ index ∈ Finset.range (order + 1),
      (order.choose index : ℝ) * polarGeometryBound order * remainder (order - index)) depth

theorem remainderDerivativeConstant_nonnegative (depth order : ℕ) :
    0 ≤ remainderDerivativeConstant depth order := by
  have geometry (order : ℕ) : 0 ≤ polarGeometryBound order :=
    zero_le_one.trans (polarGeometryBound_one_le order)
  induction depth generalizing order with
  | zero =>
    exact mul_nonneg (mul_nonneg (by positivity) (wordEnvelopeConstant_nonnegative _))
      (pow_nonneg (geometry _) _)
  | succ depth inductionHypothesis =>
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun index _ => mul_nonneg
      (mul_nonneg (by positivity) (geometry _)) (inductionHypothesis _))

/-- All polar derivatives of the smooth remainder use exactly `depth`
additional Cartesian derivatives. The estimate includes radius zero. -/
theorem polarTaylorRemainder_derivative_bound {dimension : ℕ}
    (depth order : ℕ) (field : ClosedJet dimension) (bound : ℝ) (_nonnegative : 0 ≤ bound)
    (words : ∀ rank ≤ order + depth, ∀ word : CartesianWord rank,
      ‖closedDerivative field rank word‖ ≤ bound)
    (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    ‖iteratedFDeriv ℝ order (polarTaylorRemainder depth field) point‖ ≤
      remainderDerivativeConstant depth order * bound := by
  induction depth generalizing order field with
  | zero =>
    have composite := polarComposite_derivative_bound (smoothClosedExtension field)
      (smoothClosedExtension_smooth field) order order le_rfl point inside
    have envelope := closedJet_envelope_of_word_bound field order bound
      (fun rank smaller => words rank (by omega))
      (polarClosedPoint point.1 point.2 inside.1.1 inside.1.2)
    change spatialJetEnvelope _ order (polarPlane point) ≤ _ at envelope
    apply composite.trans
    have geometry : 0 ≤ polarGeometryBound order := zero_le_one.trans (polarGeometryBound_one_le order)
    calc
      _ ≤ order.factorial * (wordEnvelopeConstant order * bound) * polarGeometryBound order ^ order := by gcongr
      _ = _ := by
        change _ = (order.factorial * wordEnvelopeConstant order * polarGeometryBound order ^ order) * bound
        ring
  | succ depth inductionHypothesis =>
    have geometry : 0 ≤ polarGeometryBound order := zero_le_one.trans (polarGeometryBound_one_le order)
    let part (coordinate : Fin 2) : ℝ × ℝ → ComplexEuclidean dimension := fun point =>
      polarAngularFactor coordinate point • polarTaylorRemainder depth (hadamardChild field coordinate) point
    have partSmooth (coordinate : Fin 2) : ContDiff ℝ ∞ (part coordinate) :=
      (polarAngularFactor_smooth coordinate).smul (polarTaylorRemainder_smooth depth _)
    have expression : polarTaylorRemainder (depth + 1) field = ∑ coordinate, part coordinate := by
      funext point
      simp only [polarTaylorRemainder, Finset.sum_apply, part]
    have partBound (coordinate : Fin 2) :
        ‖iteratedFDeriv ℝ order (part coordinate) point‖ ≤
          (∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
            polarGeometryBound order * remainderDerivativeConstant depth (order - index)) * bound := by
      have product := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) (N := ∞) (n := order)
        (s := univ) (polarAngularFactor_smooth coordinate).contDiffOn
        (polarTaylorRemainder_smooth depth (hadamardChild field coordinate)).contDiffOn
        uniqueDiffOn_univ (mem_univ point) (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
      simp only [iteratedFDerivWithin_univ] at product
      apply product.trans
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro index member
      have indexBound : index ≤ order := by have := Finset.mem_range.mp member; omega
      have scalar := (polarGeometry_derivatives_le order index indexBound point inside).2 coordinate
      have remaining := inductionHypothesis (order - index) (hadamardChild field coordinate)
        (fun rank smaller word => (hadamardChild_derivative_bound field coordinate word).trans
          (words (rank + 1) (by omega) _))
      calc
        _ ≤ (order.choose index : ℝ) * polarGeometryBound order *
            (remainderDerivativeConstant depth (order - index) * bound) := by gcongr
        _ = _ := by ring
    rw [expression, iteratedFDeriv_sum_apply]
    · calc
        _ ≤ ∑ coordinate : Fin 2, ‖iteratedFDeriv ℝ order (part coordinate) point‖ := norm_sum_le _ _
        _ ≤ ∑ _coordinate : Fin 2, (∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) *
            polarGeometryBound order * remainderDerivativeConstant depth (order - index)) * bound :=
          Finset.sum_le_sum (fun coordinate _ => partBound coordinate)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          remainderDerivativeConstant]; ring
    · intro coordinate _
      exact (partSmooth coordinate).contDiffAt.of_le
        (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))

end Grad.ExhaustionSourceAllocation
