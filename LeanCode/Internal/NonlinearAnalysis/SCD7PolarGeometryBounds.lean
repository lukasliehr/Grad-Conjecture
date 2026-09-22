import SCD6AveragedDerivatives

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRadial Grad.BoundaryTrace

def polarRectangle : Set (ℝ × ℝ) := Icc (0 : ℝ) 1 ×ˢ Icc (-Real.pi) Real.pi

def polarAngularFactor (coordinate : Fin 2) (point : ℝ × ℝ) : ℝ := radialDirection point.2 coordinate

theorem polarAngularFactor_smooth (coordinate : Fin 2) : ContDiff ℝ ∞ (polarAngularFactor coordinate) :=
  (((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℝ) coordinate).contDiff.comp
    radialDirection_smooth).comp contDiff_snd)

def polarGeometryEnvelope (grade : ℕ) (point : ℝ × ℝ) : ℝ :=
  1 + ∑ order ∈ Finset.range (grade + 1),
    (‖iteratedFDeriv ℝ order polarPlane point‖ +
      ∑ coordinate : Fin 2, ‖iteratedFDeriv ℝ order (polarAngularFactor coordinate) point‖)

theorem polarGeometryEnvelope_continuous (grade : ℕ) : Continuous (polarGeometryEnvelope grade) := by
  apply continuous_const.add
  apply continuous_finsetSum
  intro order _
  apply (polarPlane_smooth.continuous_iteratedFDeriv
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm.add
  apply continuous_finsetSum
  intro coordinate _
  exact ((polarAngularFactor_smooth coordinate).continuous_iteratedFDeriv
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).norm

theorem exists_polarGeometry_bound (grade : ℕ) : ∃ bound : ℝ, 1 ≤ bound ∧
    ∀ point ∈ polarRectangle, polarGeometryEnvelope grade point ≤ bound := by
  obtain ⟨bound, property⟩ := bddAbove_def.mp
    ((isCompact_Icc.prod isCompact_Icc).bddAbove_image (polarGeometryEnvelope_continuous grade).continuousOn)
  refine ⟨max 1 bound, le_max_left _ _, ?_⟩
  intro point inside
  exact (property _ ⟨point, inside, rfl⟩).trans (le_max_right _ _)

def polarGeometryBound (grade : ℕ) : ℝ := Classical.choose (exists_polarGeometry_bound grade)

theorem polarGeometryBound_one_le (grade : ℕ) : 1 ≤ polarGeometryBound grade :=
  (Classical.choose_spec (exists_polarGeometry_bound grade)).1

theorem polarGeometry_derivatives_le (grade order : ℕ) (upper : order ≤ grade)
    (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    ‖iteratedFDeriv ℝ order polarPlane point‖ ≤ polarGeometryBound grade ∧
    ∀ coordinate : Fin 2, ‖iteratedFDeriv ℝ order (polarAngularFactor coordinate) point‖ ≤ polarGeometryBound grade := by
  have termBound := Finset.single_le_sum (s := Finset.range (grade + 1))
    (f := fun index => ‖iteratedFDeriv ℝ index polarPlane point‖ +
      ∑ coordinate : Fin 2, ‖iteratedFDeriv ℝ index (polarAngularFactor coordinate) point‖)
    (fun _ _ => add_nonneg (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _)))
    (Finset.mem_range.mpr (by omega : order < grade + 1))
  have totalBound := (Classical.choose_spec (exists_polarGeometry_bound grade)).2 point inside
  change polarGeometryEnvelope grade point ≤ polarGeometryBound grade at totalBound
  unfold polarGeometryEnvelope at totalBound
  have sumNonnegative : 0 ≤ ∑ coordinate : Fin 2,
      ‖iteratedFDeriv ℝ order (polarAngularFactor coordinate) point‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  constructor
  · linarith
  · intro coordinate
    have coordinateBound := Finset.single_le_sum
      (f := fun coordinate : Fin 2 => ‖iteratedFDeriv ℝ order (polarAngularFactor coordinate) point‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ coordinate)
    linarith [norm_nonneg (iteratedFDeriv ℝ order polarPlane point)]

theorem polarComposite_derivative_bound {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field) (grade order : ℕ)
    (upper : order ≤ grade) (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    ‖iteratedFDeriv ℝ order (field ∘ polarPlane) point‖ ≤
      order.factorial * spatialJetEnvelope field grade (polarPlane point) * polarGeometryBound grade ^ order := by
  have outerBounds : ∀ index, index ≤ order →
      ‖iteratedFDerivWithin ℝ index field univ (polarPlane point)‖ ≤
        spatialJetEnvelope field grade (polarPlane point) := by
    intro index indexBound
    rw [iteratedFDerivWithin_univ]
    exact spatialJetEnvelope_bound field grade index (indexBound.trans upper) _
  have innerBounds : ∀ index, 1 ≤ index → index ≤ order →
      ‖iteratedFDerivWithin ℝ index polarPlane univ point‖ ≤ polarGeometryBound grade ^ index := by
    intro index positive indexBound
    rw [iteratedFDerivWithin_univ]
    apply (polarGeometry_derivatives_le grade index (indexBound.trans upper) point inside).1.trans
    simpa only [pow_one] using pow_le_pow_right₀ (polarGeometryBound_one_le grade) positive
  have composition := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := order) (N := ∞)
    (s := univ) (t := univ) smooth.contDiffOn polarPlane_smooth.contDiffOn
    (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤)) uniqueDiffOn_univ uniqueDiffOn_univ
    (mapsTo_univ _ _) (mem_univ point) outerBounds innerBounds
  simpa only [iteratedFDerivWithin_univ] using composition

def polarProductConstant (grade order : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) * polarGeometryBound grade *
    (order - index).factorial * polarGeometryBound grade ^ (order - index)

theorem polarProductConstant_nonnegative (grade order : ℕ) : 0 ≤ polarProductConstant grade order := by
  have nonnegative := (polarGeometryBound_one_le grade).trans' zero_le_one
  apply Finset.sum_nonneg
  intro index _
  positivity

theorem polarProduct_derivative_bound {Value : Type*} [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (coordinate : Fin 2) (field : SpatialPlane → Value) (smooth : ContDiff ℝ ∞ field)
    (grade order : ℕ) (upper : order ≤ grade) (point : ℝ × ℝ) (inside : point ∈ polarRectangle) :
    ‖iteratedFDeriv ℝ order (fun point => polarAngularFactor coordinate point • field (polarPlane point)) point‖ ≤
      polarProductConstant grade order * spatialJetEnvelope field grade (polarPlane point) := by
  have product := norm_iteratedFDerivWithin_smul_le (𝕜 := ℝ) (N := ∞) (n := order)
    (s := univ) (polarAngularFactor_smooth coordinate).contDiffOn (smooth.comp polarPlane_smooth).contDiffOn
    uniqueDiffOn_univ (mem_univ point) (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  simp only [iteratedFDerivWithin_univ] at product
  refine product.trans ?_
  rw [polarProductConstant, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index indexIn
  have indexBound : index ≤ grade := by have := Finset.mem_range.mp indexIn; omega
  have remainingBound : order - index ≤ grade := (Nat.sub_le _ _).trans upper
  have factorBound := (polarGeometry_derivatives_le grade index indexBound point inside).2 coordinate
  have compositeBound := polarComposite_derivative_bound field smooth grade (order - index) remainingBound point inside
  have boundNonnegative : 0 ≤ polarGeometryBound grade := zero_le_one.trans (polarGeometryBound_one_le grade)
  calc
    _ ≤ (order.choose index : ℝ) * polarGeometryBound grade *
        ((order - index).factorial * spatialJetEnvelope field grade (polarPlane point) *
          polarGeometryBound grade ^ (order - index)) := by gcongr
    _ = _ := by ring

end Grad.SourceCollarDivision
