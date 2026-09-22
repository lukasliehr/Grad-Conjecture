import BT3FourierBoundary
import ClosedJetSmoothExtension

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.CartesianState Grad.SmoothingFamily

def collarPlane (point : ℝ × ℝ) : SpatialPlane :=
  WithLp.toLp 2 ![(1 - point.1) * Real.cos point.2, (1 - point.1) * Real.sin point.2]

theorem collarPlane_smooth : ContDiff ℝ ∞ collarPlane := by
  rw [contDiff_piLp]
  intro coordinate
  fin_cases coordinate <;> simp [collarPlane] <;> fun_prop

theorem collarPlane_norm (time angle : ℝ) : ‖collarPlane (time, angle)‖ = |1 - time| := by
  have normSquared : ‖collarPlane (time, angle)‖ ^ 2 = (1 - time) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two]
    change ‖(1 - time) * Real.cos angle‖ ^ 2 + ‖(1 - time) * Real.sin angle‖ ^ 2 = _
    simp only [Real.norm_eq_abs, sq_abs]
    calc
      _ = (1 - time) ^ 2 * (Real.cos angle ^ 2 + Real.sin angle ^ 2) := by ring
      _ = (1 - time) ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
  apply (sq_eq_sq₀ (norm_nonneg _) (abs_nonneg _)).mp
  simpa only [sq_abs] using normSquared

def collarRectangle : Set (ℝ × ℝ) := Icc (0 : ℝ) (1 / 4) ×ˢ Icc (-Real.pi) Real.pi

theorem collarRectangle_compact : IsCompact collarRectangle := isCompact_Icc.prod isCompact_Icc

theorem collarPlane_radius {point : ℝ × ℝ} (inside : point ∈ collarRectangle) :
    (3 / 4 : ℝ) ≤ ‖collarPlane point‖ ∧ ‖collarPlane point‖ ≤ 1 := by
  rw [show point = (point.1, point.2) from rfl, collarPlane_norm,
    abs_of_nonneg (by linarith [inside.1.2] : 0 ≤ 1 - point.1)]
  constructor <;> linarith [inside.1.1, inside.1.2]

def collarCutoff1D (time : ℝ) : ℝ := eta (16 * time) * eta (-16 * time)

theorem collarCutoff1D_smooth : ContDiff ℝ ∞ collarCutoff1D :=
  (eta_smooth.comp (contDiff_const.mul contDiff_id)).mul
    (eta_smooth.comp (contDiff_const.mul contDiff_id))

theorem collarCutoff1D_zero : collarCutoff1D 0 = 1 := by
  simp only [collarCutoff1D, mul_zero, eta_one 0 (by norm_num : (0 : ℝ) ≤ 1), one_mul]

theorem collarCutoff1D_vanishes (time : ℝ) (far : (1 / 8 : ℝ) ≤ time) :
    collarCutoff1D time = 0 := by
  rw [collarCutoff1D, eta_zero (16 * time) (by linarith : 2 ≤ 16 * time), zero_mul]

def collarCutoff (point : ℝ × ℝ) : ℝ := collarCutoff1D point.1

theorem collarCutoff_smooth : ContDiff ℝ ∞ collarCutoff := collarCutoff1D_smooth.comp contDiff_fst

def collarField {Value : Type*} [SMul ℝ Value] (field : SpatialPlane → Value) (point : ℝ × ℝ) : Value :=
  collarCutoff point • field (collarPlane point)

theorem collarField_smooth {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    {field : SpatialPlane → Value} (smooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (collarField field) := collarCutoff_smooth.smul (smooth.comp collarPlane_smooth)

/-- A single fixed-collar bound for all coordinate and cutoff derivatives
through the requested order, independent of the field and cell frequency. -/
def collarGeometryEnvelope (grade : ℕ) (point : ℝ × ℝ) : ℝ :=
  1 + ∑ order ∈ Finset.range (grade + 1),
    (‖iteratedFDeriv ℝ order collarPlane point‖ + ‖iteratedFDeriv ℝ order collarCutoff point‖)

theorem collarGeometryEnvelope_continuous (grade : ℕ) : Continuous (collarGeometryEnvelope grade) := by
  apply continuous_const.add
  apply continuous_finsetSum
  intro order _
  exact (collarPlane_smooth.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm.add
    (collarCutoff_smooth.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm

theorem exists_collarGeometry_bound (grade : ℕ) : ∃ bound : ℝ, 1 ≤ bound ∧
    ∀ point ∈ collarRectangle, collarGeometryEnvelope grade point ≤ bound := by
  obtain ⟨bound, property⟩ := bddAbove_def.mp
    (collarRectangle_compact.bddAbove_image (collarGeometryEnvelope_continuous grade).continuousOn)
  refine ⟨max 1 bound, le_max_left _ _, ?_⟩
  intro point inside
  exact (property _ ⟨point, inside, rfl⟩).trans (le_max_right _ _)

def collarGeometryBound (grade : ℕ) : ℝ := Classical.choose (exists_collarGeometry_bound grade)

theorem collarGeometryBound_one_le (grade : ℕ) : 1 ≤ collarGeometryBound grade :=
  (Classical.choose_spec (exists_collarGeometry_bound grade)).1

theorem collarGeometryEnvelope_le_bound (grade : ℕ) (point : ℝ × ℝ) (inside : point ∈ collarRectangle) :
    collarGeometryEnvelope grade point ≤ collarGeometryBound grade :=
  (Classical.choose_spec (exists_collarGeometry_bound grade)).2 point inside

end Grad.BoundaryTrace
