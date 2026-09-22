import BT4CollarGeometry

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace Grad.BoundaryTrace

open Grad.ClosedJets Grad.DiskExtension.Operator

theorem collarGeometry_derivatives_le (grade order : ℕ) (upper : order ≤ grade)
    (point : ℝ × ℝ) (inside : point ∈ collarRectangle) :
    ‖iteratedFDeriv ℝ order collarPlane point‖ ≤ collarGeometryBound grade ∧
    ‖iteratedFDeriv ℝ order collarCutoff point‖ ≤ collarGeometryBound grade := by
  have termBound := Finset.single_le_sum (s := Finset.range (grade + 1))
    (f := fun index => ‖iteratedFDeriv ℝ index collarPlane point‖ +
      ‖iteratedFDeriv ℝ index collarCutoff point‖)
    (fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _))
    (Finset.mem_range.mpr (by omega : order < grade + 1))
  have envelopeBound := collarGeometryEnvelope_le_bound grade point inside
  unfold collarGeometryEnvelope at envelopeBound
  constructor <;> linarith [norm_nonneg (iteratedFDeriv ℝ order collarPlane point),
    norm_nonneg (iteratedFDeriv ℝ order collarCutoff point)]

def spatialJetEnvelope {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : SpatialPlane → Value) (grade : ℕ) (point : SpatialPlane) : ℝ :=
  ∑ order ∈ Finset.range (grade + 1), ‖iteratedFDeriv ℝ order field point‖

def spatialJetSquaredDensity {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : SpatialPlane → Value) (grade : ℕ) (point : SpatialPlane) : ℝ :=
  ∑ order ∈ Finset.range (grade + 1), ‖iteratedFDeriv ℝ order field point‖ ^ 2

theorem spatialJetEnvelope_nonnegative {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : SpatialPlane → Value) (grade : ℕ) (point : SpatialPlane) :
    0 ≤ spatialJetEnvelope field grade point := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem spatialJetEnvelope_sq_le {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : SpatialPlane → Value) (grade : ℕ) (point : SpatialPlane) :
    spatialJetEnvelope field grade point ^ 2 ≤ (grade + 1 : ℝ) * spatialJetSquaredDensity field grade point := by
  have cauchy := weighted_cauchy_finset (Finset.range (grade + 1)) (fun _ => (1 : ℝ))
    (fun order => ‖iteratedFDeriv ℝ order field point‖) (by intros; norm_num)
  simpa [spatialJetEnvelope, spatialJetSquaredDensity] using cauchy

theorem spatialJetEnvelope_bound {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : SpatialPlane → Value) (grade order : ℕ) (upper : order ≤ grade) (point : SpatialPlane) :
    ‖iteratedFDeriv ℝ order field point‖ ≤ spatialJetEnvelope field grade point := by
  unfold spatialJetEnvelope
  exact Finset.single_le_sum (f := fun index => ‖iteratedFDeriv ℝ index field point‖)
    (fun _ _ => norm_nonneg _)
    (Finset.mem_range.mpr (by omega : order < grade + 1))

theorem collarComposite_derivative_bound {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field) (grade order : ℕ)
    (upper : order ≤ grade) (point : ℝ × ℝ) (inside : point ∈ collarRectangle) :
    ‖iteratedFDeriv ℝ order (field ∘ collarPlane) point‖ ≤
      order.factorial * spatialJetEnvelope field grade (collarPlane point) * collarGeometryBound grade ^ order := by
  have outerBounds : ∀ index, index ≤ order →
      ‖iteratedFDerivWithin ℝ index field univ (collarPlane point)‖ ≤
        spatialJetEnvelope field grade (collarPlane point) := by
    intro index indexBound
    rw [iteratedFDerivWithin_univ]
    exact spatialJetEnvelope_bound field grade index (indexBound.trans upper) _
  have innerBounds : ∀ index, 1 ≤ index → index ≤ order →
      ‖iteratedFDerivWithin ℝ index collarPlane univ point‖ ≤ collarGeometryBound grade ^ index := by
    intro index positive indexBound
    rw [iteratedFDerivWithin_univ]
    apply (collarGeometry_derivatives_le grade index (indexBound.trans upper) point inside).1.trans
    simpa only [pow_one] using pow_le_pow_right₀ (collarGeometryBound_one_le grade) positive
  have composition := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := order) (N := ∞)
    (s := univ) (t := univ) smooth.contDiffOn collarPlane_smooth.contDiffOn
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤)) uniqueDiffOn_univ uniqueDiffOn_univ
    (mapsTo_univ _ _) (mem_univ point) outerBounds innerBounds
  simpa only [iteratedFDerivWithin_univ] using composition

def collarDerivativeConstant (grade order : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) * collarGeometryBound grade *
    (order - index).factorial * collarGeometryBound grade ^ (order - index)

theorem collarDerivativeConstant_nonnegative (grade order : ℕ) : 0 ≤ collarDerivativeConstant grade order := by
  apply Finset.sum_nonneg
  intro index _
  have nonnegative := (zero_le_one.trans (collarGeometryBound_one_le grade))
  positivity

theorem collarField_derivative_bound {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field) (grade order : ℕ)
    (upper : order ≤ grade) (point : ℝ × ℝ) (inside : point ∈ collarRectangle) :
    ‖iteratedFDeriv ℝ order (collarField field) point‖ ≤
      collarDerivativeConstant grade order * spatialJetEnvelope field grade (collarPlane point) := by
  have product := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) (N := ∞) (n := order)
    (s := univ) collarCutoff_smooth.contDiffOn (smooth.comp collarPlane_smooth).contDiffOn
    uniqueDiffOn_univ (mem_univ point) (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  simp only [iteratedFDerivWithin_univ] at product
  refine product.trans ?_
  rw [collarDerivativeConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index indexIn
  have indexBound : index ≤ grade := by have := Finset.mem_range.mp indexIn; omega
  have remainingBound : order - index ≤ grade := (Nat.sub_le _ _).trans upper
  have cutoffBound := (collarGeometry_derivatives_le grade index indexBound point inside).2
  have compositeBound := collarComposite_derivative_bound field smooth grade (order - index)
    remainingBound point inside
  have boundNonnegative : 0 ≤ collarGeometryBound grade :=
    zero_le_one.trans (collarGeometryBound_one_le grade)
  calc
    _ ≤ (order.choose index : ℝ) * collarGeometryBound grade *
        ((order - index).factorial * spatialJetEnvelope field grade (collarPlane point) *
          collarGeometryBound grade ^ (order - index)) := by
      gcongr
    _ = _ := by ring

theorem collarField_derivative_sq_bound {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field) (grade order : ℕ)
    (upper : order ≤ grade) (point : ℝ × ℝ) (inside : point ∈ collarRectangle) :
    ‖iteratedFDeriv ℝ order (collarField field) point‖ ^ 2 ≤
      (collarDerivativeConstant grade order ^ 2 * (grade + 1 : ℝ)) *
        spatialJetSquaredDensity field grade (collarPlane point) := by
  calc
    _ ≤ (collarDerivativeConstant grade order * spatialJetEnvelope field grade (collarPlane point)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (collarField_derivative_bound field smooth grade order upper point inside) 2
    _ = collarDerivativeConstant grade order ^ 2 * spatialJetEnvelope field grade (collarPlane point) ^ 2 := mul_pow _ _ _
    _ ≤ collarDerivativeConstant grade order ^ 2 * ((grade + 1 : ℝ) *
        spatialJetSquaredDensity field grade (collarPlane point)) :=
      mul_le_mul_of_nonneg_left (spatialJetEnvelope_sq_le field grade _) (sq_nonneg _)
    _ = _ := by ring

end Grad.BoundaryTrace
