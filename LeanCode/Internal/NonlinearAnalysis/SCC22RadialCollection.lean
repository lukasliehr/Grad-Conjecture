import SCC21RadialSquareSum
import Mathlib.Analysis.InnerProductSpace.l2Space

noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision

abbrev CellL2 (dimension : ℕ) := lp (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2

def radialSlice {dimension : ℕ} (lower : ℝ) (field : DivisionRow dimension lower)
    (radius : ℝ) : CellL2 dimension :=
  ∑' mode : ℤ × ℤ, lp.single 2 mode (field mode radius)

theorem radialSlice_ae_memlp {dimension : ℕ} (lower : ℝ) (field : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Set.Icc lower 1), Memℓp (fun mode => field mode radius) 2 := by
  filter_upwards [(radialRowSquare_properties lower field).1] with radius summable
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_ofNat] using summable

theorem radialSlice_eq {dimension : ℕ} (lower : ℝ) (field : DivisionRow dimension lower)
    (radius : ℝ) (member : Memℓp (fun mode => field mode radius) 2) :
    radialSlice lower field radius = ⟨(fun mode => field mode radius), member⟩ := by
  exact (lp.hasSum_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (⟨(fun mode => field mode radius), member⟩ : CellL2 dimension)).tsum_eq

theorem radialSlice_ae {dimension : ℕ} (lower : ℝ) (field : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Set.Icc lower 1),
      ∀ mode : ℤ × ℤ, radialSlice lower field radius mode = field mode radius := by
  filter_upwards [radialSlice_ae_memlp lower field] with radius member
  rw [radialSlice_eq lower field radius member]
  intro mode
  rfl

theorem radialSlice_measurable {dimension : ℕ} (lower : ℝ) (field : DivisionRow dimension lower) :
    AEStronglyMeasurable (radialSlice lower field) (volume.restrict (Set.Icc lower 1)) := by
  apply aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset (ℤ × ℤ)))
    (f := fun modes radius => ∑ mode ∈ modes, (lp.single 2 mode (field mode radius) : CellL2 dimension))
  · intro modes
    apply Finset.aestronglyMeasurable_fun_sum
    intro mode _
    exact (lp.singleContinuousLinearMap ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (field mode))
  · filter_upwards [radialSlice_ae_memlp lower field] with radius member
    rw [radialSlice_eq lower field radius member]
    exact lp.hasSum_single (by norm_num) (⟨_, member⟩ : CellL2 dimension)

theorem radialSlice_norm_sq_ae {dimension : ℕ} (lower : ℝ) (field : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Set.Icc lower 1),
      ‖radialSlice lower field radius‖ ^ 2 = radialRowSquare lower field radius := by
  filter_upwards [radialSlice_ae lower field] with radius literal
  have equality := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (radialSlice lower field radius)
  norm_num at equality
  simpa only [literal, radialRowSquare] using equality

theorem radialSlice_memLp {dimension : ℕ} (lower : ℝ) (field : DivisionRow dimension lower) :
    MemLp (radialSlice lower field) 2 (volume.restrict (Set.Icc lower 1)) := by
  apply (memLp_two_iff_integrable_sq_norm (radialSlice_measurable lower field)).mpr
  exact (radialRowSquare_properties lower field).2.congr
    ((radialSlice_norm_sq_ae lower field).mono (fun _ equality => equality.symm))

def collectRadial {dimension : ℕ} (lower : ℝ) (field : DivisionRow dimension lower) :
    Lp (CellL2 dimension) 2 (volume.restrict (Set.Icc lower 1)) :=
  (radialSlice_memLp lower field).toLp (radialSlice lower field)

theorem collectRadial_ae {dimension : ℕ} (lower : ℝ) (field : DivisionRow dimension lower) :
    ∀ᵐ radius ∂volume.restrict (Set.Icc lower 1),
      ∀ mode : ℤ × ℤ, collectRadial lower field radius mode = field mode radius := by
  filter_upwards [(radialSlice_memLp lower field).coeFn_toLp, radialSlice_ae lower field]
    with radius collected literal
  change collectRadial lower field radius = radialSlice lower field radius at collected
  rw [collected]
  exact literal

theorem cellL2_Lp_norm_sq {dimension : ℕ} (lower : ℝ)
    (field : Lp (CellL2 dimension) 2 (volume.restrict (Set.Icc lower 1))) :
    ‖field‖ ^ 2 = ∫ radius, ‖field radius‖ ^ 2 ∂volume.restrict (Set.Icc lower 1) := by
  let := InnerProductSpace.rclikeToReal ℂ (CellL2 dimension)
  calc
    _ = inner ℝ field field := (real_inner_self_eq_norm_sq field).symm
    _ = ∫ radius, inner ℝ (field radius) (field radius) ∂volume.restrict (Set.Icc lower 1) :=
      L2.inner_def (𝕜 := ℝ) field field
    _ = _ := by simp only [real_inner_self_eq_norm_sq]

theorem collectRadial_norm {dimension : ℕ} (lower : ℝ) (field : DivisionRow dimension lower) :
    ‖collectRadial lower field‖ = ‖field‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [cellL2_Lp_norm_sq, ← radialRowSquare_integral lower field]
  apply integral_congr_ae
  filter_upwards [(radialSlice_memLp lower field).coeFn_toLp, radialSlice_norm_sq_ae lower field]
    with radius literal squared
  change collectRadial lower field radius = radialSlice lower field radius at literal
  rw [literal, squared]

end Grad.SourceCollarCoefficients
