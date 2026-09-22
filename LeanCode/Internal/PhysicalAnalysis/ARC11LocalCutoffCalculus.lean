import ARC10FiniteCartesianConsumer

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace Grad.CollarCartesian
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.Constraints Grad.BoundaryLift

theorem cutoff_derivative_bound_on {dimension : ℕ} (cutoff : ℝ × ℝ → ℝ)
    (domain : Set (ℝ × ℝ)) (domainOpen : IsOpen domain) (cutoffSmooth : ContDiffOn ℝ ∞ cutoff domain) (field : ℝ × ℝ → ComplexEuclidean dimension)
    (fieldSmooth : ContDiffOn ℝ ∞ field domain) (grade order : ℕ) (upper : order ≤ grade)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) (point : ℝ × ℝ) (pointIn : point ∈ domain)
    (bounds : ∀ index, index ≤ grade → ‖iteratedFDeriv ℝ index cutoff point‖ ≤ bound) :
    ‖iteratedFDeriv ℝ order (fun point => cutoff point • field point) point‖ ≤
      ((∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ)) * bound) *
        polarJetEnvelope field grade point := by
  have product := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) (N := ∞) (n := order)
    cutoffSmooth fieldSmooth domainOpen.uniqueDiffOn pointIn
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  simp_rw [iteratedFDerivWithin_of_isOpen _ domainOpen pointIn] at product
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

theorem cutoff_derivative_sq_bound_on {dimension : ℕ} (cutoff : ℝ × ℝ → ℝ)
    (domain : Set (ℝ × ℝ)) (domainOpen : IsOpen domain) (cutoffSmooth : ContDiffOn ℝ ∞ cutoff domain) (field : ℝ × ℝ → ComplexEuclidean dimension)
    (fieldSmooth : ContDiffOn ℝ ∞ field domain) (grade order : ℕ) (upper : order ≤ grade)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) (point : ℝ × ℝ) (pointIn : point ∈ domain)
    (bounds : ∀ index, index ≤ grade → ‖iteratedFDeriv ℝ index cutoff point‖ ≤ bound) :
    ‖iteratedFDeriv ℝ order (fun point => cutoff point • field point) point‖ ^ 2 ≤
      cutoffOrderConstant bound grade order * polarJetSquaredDensity field grade point := by
  have estimate := cutoff_derivative_bound_on cutoff domain domainOpen cutoffSmooth field fieldSmooth grade order upper
    bound boundNonnegative point pointIn bounds
  calc
    _ ≤ (((∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ)) * bound) *
        polarJetEnvelope field grade point) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) estimate 2
    _ = ((∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ)) * bound) ^ 2 *
        polarJetEnvelope field grade point ^ 2 := mul_pow _ _ _
    _ ≤ ((∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ)) * bound) ^ 2 *
        ((grade + 1 : ℝ) * polarJetSquaredDensity field grade point) :=
      mul_le_mul_of_nonneg_left (polarJetEnvelope_sq_le field grade point) (sq_nonneg _)
    _ = _ := by unfold cutoffOrderConstant; ring

theorem cutoff_density_bound_on {dimension : ℕ} (cutoff : ℝ × ℝ → ℝ)
    (domain : Set (ℝ × ℝ)) (domainOpen : IsOpen domain) (cutoffSmooth : ContDiffOn ℝ ∞ cutoff domain) (field : ℝ × ℝ → ComplexEuclidean dimension)
    (fieldSmooth : ContDiffOn ℝ ∞ field domain) (grade : ℕ)
    (bound : ℝ) (boundNonnegative : 0 ≤ bound) (point : ℝ × ℝ) (pointIn : point ∈ domain)
    (bounds : ∀ index, index ≤ grade → ‖iteratedFDeriv ℝ index cutoff point‖ ≤ bound) :
    polarJetSquaredDensity (fun point => cutoff point • field point) grade point ≤
      cutoffDensityConstant bound grade * polarJetSquaredDensity field grade point := by
  rw [polarJetSquaredDensity, cutoffDensityConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro order inside
  exact cutoff_derivative_sq_bound_on cutoff domain domainOpen cutoffSmooth field fieldSmooth grade order
    (by have := Finset.mem_range.mp inside; omega) bound boundNonnegative point pointIn bounds


end Grad.CollarCartesian
