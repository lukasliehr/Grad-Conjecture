import ARC8FiniteProfileEnergy

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CollarCartesian
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift

/-- Compactness controls an arbitrary smooth cutoff; no rotation law is required. -/
theorem exists_polarCutoffBound (cutoff : ℝ × ℝ → ℝ) (smooth : ContDiff ℝ ∞ cutoff)
    (grade : ℕ) : ∃ bound : ℝ, 0 ≤ bound ∧ ∀ order, order ≤ grade →
      ∀ point ∈ halfCollarRectangle, ‖iteratedFDeriv ℝ order cutoff point‖ ≤ bound := by
  have envelopeContinuous : Continuous (polarJetEnvelope cutoff grade) := by
    apply continuous_finsetSum
    intro order _
    exact (smooth.continuous_iteratedFDeriv
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm
  obtain ⟨bound, property⟩ := bddAbove_def.mp
    ((isCompact_Icc.prod isCompact_Icc).bddAbove_image envelopeContinuous.continuousOn)
  refine ⟨max 0 bound, le_max_left _ _, ?_⟩
  intro order upper point inside
  exact (polarJetEnvelope_bound cutoff grade order upper point).trans
    ((property _ ⟨point, inside, rfl⟩).trans (le_max_right _ _))

def cutoffOrderConstant (bound : ℝ) (grade order : ℕ) : ℝ :=
  ((∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ)) * bound) ^ 2 * (grade + 1 : ℝ)

def cutoffDensityConstant (bound : ℝ) (grade : ℕ) : ℝ :=
  ∑ order ∈ Finset.range (grade + 1), cutoffOrderConstant bound grade order

theorem cutoffDensityConstant_nonnegative (bound : ℝ) (grade : ℕ) :
    0 ≤ cutoffDensityConstant bound grade := by
  apply Finset.sum_nonneg
  intro order _
  unfold cutoffOrderConstant
  positivity

theorem cutoff_derivative_bound {dimension : ℕ} (cutoff : ℝ × ℝ → ℝ)
    (cutoffSmooth : ContDiff ℝ ∞ cutoff) (field : ℝ × ℝ → ComplexEuclidean dimension)
    (fieldSmooth : ContDiff ℝ ∞ field) (grade order : ℕ) (upper : order ≤ grade)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) (point : ℝ × ℝ)
    (bounds : ∀ index, index ≤ grade → ‖iteratedFDeriv ℝ index cutoff point‖ ≤ bound) :
    ‖iteratedFDeriv ℝ order (fun point => cutoff point • field point) point‖ ≤
      ((∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ)) * bound) *
        polarJetEnvelope field grade point := by
  have product := norm_iteratedFDeriv_smul_le (𝕜 := ℝ) (N := ∞) (n := order)
    cutoffSmooth fieldSmooth point
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  apply product.trans
  calc
    _ ≤ ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) * bound *
        polarJetEnvelope field grade point := by
      apply Finset.sum_le_sum
      intro index inside
      have indexUpper : index ≤ grade := by have := Finset.mem_range.mp inside; omega
      have otherUpper : order - index ≤ grade := (Nat.sub_le _ _).trans upper
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (bounds index indexUpper) (Nat.cast_nonneg _))
        (polarJetEnvelope_bound field grade (order - index) otherUpper point)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) boundNonnegative)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]

theorem cutoff_derivative_sq_bound {dimension : ℕ} (cutoff : ℝ × ℝ → ℝ)
    (cutoffSmooth : ContDiff ℝ ∞ cutoff) (field : ℝ × ℝ → ComplexEuclidean dimension)
    (fieldSmooth : ContDiff ℝ ∞ field) (grade order : ℕ) (upper : order ≤ grade)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) (point : ℝ × ℝ)
    (bounds : ∀ index, index ≤ grade → ‖iteratedFDeriv ℝ index cutoff point‖ ≤ bound) :
    ‖iteratedFDeriv ℝ order (fun point => cutoff point • field point) point‖ ^ 2 ≤
      cutoffOrderConstant bound grade order * polarJetSquaredDensity field grade point := by
  have estimate := cutoff_derivative_bound cutoff cutoffSmooth field fieldSmooth grade order upper
    bound boundNonnegative point bounds
  calc
    _ ≤ (((∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ)) * bound) *
        polarJetEnvelope field grade point) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) estimate 2
    _ = ((∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ)) * bound) ^ 2 *
        polarJetEnvelope field grade point ^ 2 := mul_pow _ _ _
    _ ≤ ((∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ)) * bound) ^ 2 *
        ((grade + 1 : ℝ) * polarJetSquaredDensity field grade point) :=
      mul_le_mul_of_nonneg_left (polarJetEnvelope_sq_le field grade point) (sq_nonneg _)
    _ = _ := by unfold cutoffOrderConstant; ring

theorem cutoff_density_bound {dimension : ℕ} (cutoff : ℝ × ℝ → ℝ)
    (cutoffSmooth : ContDiff ℝ ∞ cutoff) (field : ℝ × ℝ → ComplexEuclidean dimension)
    (fieldSmooth : ContDiff ℝ ∞ field) (grade : ℕ)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) (point : ℝ × ℝ)
    (bounds : ∀ index, index ≤ grade → ‖iteratedFDeriv ℝ index cutoff point‖ ≤ bound) :
    polarJetSquaredDensity (fun point => cutoff point • field point) grade point ≤
      cutoffDensityConstant bound grade * polarJetSquaredDensity field grade point := by
  rw [polarJetSquaredDensity, cutoffDensityConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro order inside
  exact cutoff_derivative_sq_bound cutoff cutoffSmooth field fieldSmooth grade order
    (by have := Finset.mem_range.mp inside; omega) bound boundNonnegative point bounds

end Grad.CollarCartesian
