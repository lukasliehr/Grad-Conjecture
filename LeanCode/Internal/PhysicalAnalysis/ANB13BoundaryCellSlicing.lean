import ANB12BoundaryWeightComparison

noncomputable section
set_option maxHeartbeats 1400000
namespace Grad.BoundedScalarInverse
open Grad.ClosedJets Grad.CartesianState Grad.CircularNormalLift Grad.InhomogeneousHighRobin
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Physical.WeightedTrace
local instance (priority := 2000) sliceBoundarySpace (grade : ℕ) : NormedSpace ℂ (normalBoundaryGrade grade) :=
  (normalBoundaryGrade grade).normedSpace

section Diagonal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

def hilbertDiagonal (weights : ℤ → ℝ) (bounded : ∃ bound : ℝ, ∀ mode, |weights mode| ≤ bound)
    (field : lp (fun _ : ℤ => E) 2) : lp (fun _ : ℤ => E) 2 :=
  ⟨fun mode => (weights mode : ℂ) • field mode, by
    rcases bounded with ⟨bound, estimate⟩
    apply (lp.memℓp ((bound : ℂ) • field)).mono'
    intro mode
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, lp.coeFn_smul, Pi.smul_apply]
    exact mul_le_mul_of_nonneg_right ((estimate mode).trans (le_abs_self _)) (norm_nonneg _)⟩

theorem hilbertDiagonal_norm (weights : ℤ → ℝ) (bounded : ∃ bound : ℝ, ∀ mode, |weights mode| ≤ bound)
    (field : lp (fun _ : ℤ => E) 2) (bound : ℝ) (nonnegative : 0 ≤ bound) (estimate : ∀ mode, |weights mode| ≤ bound) :
    ‖hilbertDiagonal weights bounded field‖ ≤ bound * ‖field‖ := by
  have comparison : ‖hilbertDiagonal weights bounded field‖ ≤ ‖(bound : ℂ) • field‖ := by
    apply lp.norm_mono (by norm_num)
    intro mode
    change ‖(weights mode : ℂ) • field mode‖ ≤ ‖(bound : ℂ) • field mode‖
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg nonnegative]
    exact mul_le_mul_of_nonneg_right (estimate mode) (norm_nonneg _)
  exact comparison.trans_eq (by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg nonnegative])
end Diagonal

theorem boundaryFlatRatio_bounded {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (order : ℕ) (cell : ℤ) : ∃ bound : ℝ, ∀ mode, |boundaryFlatRatio length sigma gamma scale order cell mode| ≤ bound := by
  refine ⟨bandWeightCeiling length gamma |(cell : ℝ) * scale / length|, ?_⟩
  intro mode
  rw [abs_of_nonneg (boundaryFlatRatio_nonnegative _ _ _ _ _ _ _)]
  exact boundaryFlatRatio_bound admissible _ cell le_rfl order mode

def boundaryFlatSlice {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (order : ℕ) (cell : ℤ) (field : APBoundaryGrade length sigma gamma scale 1 (order + 1)) : normalBoundaryGrade (order + 2) :=
  ⟨hilbertZeroCell (hilbertDiagonal (boundaryFlatRatio length sigma gamma scale order cell)
    (boundaryFlatRatio_bounded admissible order cell) (hilbertColumn field cell)), by
    apply (normalBoundary_mem_iff (order + 2) _).2
    intro mode other different
    exact if_neg different⟩

theorem boundaryFlatSlice_norm {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (ceiling : ℝ) (cell : ℤ) (band : InCellBand length scale ceiling cell) (order : ℕ)
    (field : APBoundaryGrade length sigma gamma scale 1 (order + 1)) :
    ‖boundaryFlatSlice admissible order cell field‖ ≤ bandWeightCeiling length gamma ceiling * ‖hilbertColumn field cell‖ := by
  change ‖hilbertZeroCell _‖ ≤ _
  rw [hilbertZeroCell_norm]
  apply hilbertDiagonal_norm
  · exact (Real.exp_pos _).le
  · intro mode
    rw [abs_of_nonneg (boundaryFlatRatio_nonnegative _ _ _ _ _ _ _)]
    exact boundaryFlatRatio_bound admissible ceiling cell band order mode

theorem boundaryFlatSlice_coefficient {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (order : ℕ) (cell : ℤ) (field : APBoundaryGrade length sigma gamma scale 1 (order + 1)) (mode : ℤ) :
    normalBoundaryCoefficient (order + 2) (boundaryFlatSlice admissible order cell field) mode =
      ((Real.exp (sigma * Grad.CellWeights.cellWeight cell) : ℝ) : ℂ) •
        apBoundaryCoefficient length sigma gamma scale (order + 1) field (mode, cell) := by
  change (normalBoundaryWeight (order + 2) mode : ℂ)⁻¹ •
    (if (0 : ℤ) = 0 then (boundaryFlatRatio length sigma gamma scale order cell mode : ℂ) • field (mode, cell) else 0) = _
  rw [if_pos rfl]
  unfold boundaryFlatRatio apBoundaryCoefficient
  push_cast
  rw [← mul_smul, ← mul_smul]
  congr 1
  field_simp [Complex.ofReal_ne_zero.mpr (normalBoundaryWeight_pos (order + 2) mode).ne']

def boundaryCellSlice {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (order : ℕ) (cell : ℤ) (field : APBoundaryGrade length sigma gamma scale 1 (order + 1)) : normalBoundaryGrade (order + 2) :=
  ((Real.exp (sigma * Grad.CellWeights.cellWeight cell) : ℝ) : ℂ)⁻¹ • boundaryFlatSlice admissible order cell field

theorem boundaryCellSlice_coefficient {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (order : ℕ) (cell : ℤ) (field : APBoundaryGrade length sigma gamma scale 1 (order + 1)) (mode : ℤ) :
    normalBoundaryCoefficient (order + 2) (boundaryCellSlice admissible order cell field) mode =
      apBoundaryCoefficient length sigma gamma scale (order + 1) field (mode, cell) := by
  change normalBoundaryCoefficientCLM (order + 2) mode
    (((Real.exp (sigma * Grad.CellWeights.cellWeight cell) : ℝ) : ℂ)⁻¹ • boundaryFlatSlice admissible order cell field) = _
  rw [map_smul, normalBoundaryCoefficientCLM_apply, boundaryFlatSlice_coefficient]
  exact inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) _

theorem boundaryCellSlice_flat {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (order : ℕ) (cell : ℤ) (field : APBoundaryGrade length sigma gamma scale 1 (order + 1)) :
    ((Real.exp (sigma * Grad.CellWeights.cellWeight cell) : ℝ) : ℂ) • boundaryCellSlice admissible order cell field =
      boundaryFlatSlice admissible order cell field :=
  smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) _

/-- Actual original circle Sobolev grades; coherence is equality of physical
Fourier coefficients, not equality of weighted coordinates. -/
structure BandSmoothBoundary (length sigma gamma scale : ℝ) where
  grade : (order : ℕ) → APBoundaryGrade length sigma gamma scale 1 (order + 1)
  coherent : ∀ order output, apBoundaryCoefficient length sigma gamma scale (order + 1) (grade order) output =
    apBoundaryCoefficient length sigma gamma scale 1 (grade 0) output

def smoothBoundaryCell {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (field : BandSmoothBoundary length sigma gamma scale) (cell : ℤ) : NormalSmoothBoundary where
  grade order := boundaryCellSlice admissible order cell (field.grade order)
  coherent order := by
    apply normalBoundary_ext
    intro mode
    exact (normalBoundaryLower_coefficient 2 (order + 2) (by omega) (by omega) _ mode).trans
      ((boundaryCellSlice_coefficient admissible order cell _ mode).trans
        ((field.coherent order (mode, cell)).trans (boundaryCellSlice_coefficient admissible 0 cell _ mode).symm))

theorem smoothBoundaryCell_coefficient {length sigma gamma scale : ℝ} (admissible : Admissible length sigma gamma scale)
    (field : BandSmoothBoundary length sigma gamma scale) (cell : ℤ) (order : ℕ) (mode : ℤ) :
    normalBoundaryCoefficient (order + 2) ((smoothBoundaryCell admissible field cell).grade order) mode =
      apBoundaryCoefficient length sigma gamma scale (order + 1) (field.grade order) (mode, cell) :=
  boundaryCellSlice_coefficient admissible order cell _ mode

end Grad.BoundedScalarInverse
