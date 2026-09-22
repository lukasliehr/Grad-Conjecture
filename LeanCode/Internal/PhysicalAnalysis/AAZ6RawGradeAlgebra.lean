import AAZ5ActualRadialJetRecursion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRadialJets
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace

theorem annularRawGrade_zero_family (lower : ℝ) (grade : ℕ) : HasAnnularRawGrade lower grade 0 := by
  simp only [HasAnnularRawGrade, Pi.zero_apply, smul_zero]
  exact (0 : AnnularBulk lower).property

theorem annularRawGrade_add (lower : ℝ) (grade : ℕ) (first second : AnnularRawFamily lower)
    (firstGrade : HasAnnularRawGrade lower grade first) (secondGrade : HasAnnularRawGrade lower grade second) :
    HasAnnularRawGrade lower grade (first + second) := by
  have equality : (fun mode => (annularGradeWeight 0 0 grade mode : ℂ) • (first + second) mode) =
      (fun mode => (annularGradeWeight 0 0 grade mode : ℂ) • first mode) +
        (fun mode => (annularGradeWeight 0 0 grade mode : ℂ) • second mode) := by
    funext mode
    exact smul_add _ _ _
  exact (congrArg (fun value : AnnularRawFamily lower => Memℓp value 2) equality).mpr (firstGrade.add secondGrade)

theorem annularRawGrade_sum (lower : ℝ) (grade : ℕ) {Index : Type*} (support : Finset Index)
    (field : Index → AnnularRawFamily lower)
    (member : ∀ index ∈ support, HasAnnularRawGrade lower grade (field index)) :
    HasAnnularRawGrade lower grade (∑ index ∈ support, field index) := by
  classical
  induction support using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using annularRawGrade_zero_family lower grade
  | @insert index support missing previous =>
    rw [Finset.sum_insert missing]
    exact annularRawGrade_add lower grade _ _ (member index (Finset.mem_insert_self index support))
      (previous (fun other present => member other (Finset.mem_insert_of_mem present)))

theorem annularRawWeighted_add (lower : ℝ) (grade : ℕ) (first second : AnnularRawFamily lower)
    (firstGrade : HasAnnularRawGrade lower grade first) (secondGrade : HasAnnularRawGrade lower grade second)
    (sumGrade : HasAnnularRawGrade lower grade (first + second)) :
    annularRawWeighted lower grade (first + second) sumGrade =
      annularRawWeighted lower grade first firstGrade + annularRawWeighted lower grade second secondGrade := by
  apply lp.ext
  funext mode
  exact smul_add (annularGradeWeight 0 0 grade mode : ℂ) (first mode) (second mode)

theorem annularRawWeighted_add_bound (lower : ℝ) (grade : ℕ) (first second : AnnularRawFamily lower)
    (firstGrade : HasAnnularRawGrade lower grade first) (secondGrade : HasAnnularRawGrade lower grade second)
    (sumGrade : HasAnnularRawGrade lower grade (first + second)) :
    ‖annularRawWeighted lower grade (first + second) sumGrade‖ ≤
      ‖annularRawWeighted lower grade first firstGrade‖ + ‖annularRawWeighted lower grade second secondGrade‖ := by
  rw [annularRawWeighted_add lower grade first second firstGrade secondGrade sumGrade]
  exact norm_add_le _ _

theorem annularRawWeighted_sum (lower : ℝ) (grade : ℕ) {Index : Type*} (support : Finset Index)
    (field : Index → AnnularRawFamily lower) (member : ∀ index, HasAnnularRawGrade lower grade (field index))
    (sumGrade : HasAnnularRawGrade lower grade (∑ index ∈ support, field index)) :
    annularRawWeighted lower grade (∑ index ∈ support, field index) sumGrade =
      ∑ index ∈ support, annularRawWeighted lower grade (field index) (member index) := by
  apply lp.ext
  funext mode
  rw [lp.coeFn_sum, Finset.sum_apply]
  change (annularGradeWeight 0 0 grade mode : ℂ) • (∑ index ∈ support, field index) mode = _
  rw [Finset.sum_apply, Finset.smul_sum]
  rfl

theorem annularRawWeighted_sum_bound (lower : ℝ) (grade : ℕ) {Index : Type*} (support : Finset Index)
    (field : Index → AnnularRawFamily lower) (member : ∀ index, HasAnnularRawGrade lower grade (field index))
    (sumGrade : HasAnnularRawGrade lower grade (∑ index ∈ support, field index)) :
    ‖annularRawWeighted lower grade (∑ index ∈ support, field index) sumGrade‖ ≤
      ∑ index ∈ support, ‖annularRawWeighted lower grade (field index) (member index)‖ := by
  rw [annularRawWeighted_sum lower grade support field member sumGrade]
  exact norm_sum_le _ _

theorem annularRawGrade_real (lower : ℝ) (grade : ℕ) (scalar : ℝ) (field : AnnularRawFamily lower)
    (member : HasAnnularRawGrade lower grade field) : HasAnnularRawGrade lower grade (scalar • field) := by
  apply annularRawGrade_of_bound lower grade 0 field (scalar • field) |scalar| (abs_nonneg scalar) member
  intro mode
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, pow_zero, mul_one, le_refl]

theorem annularRawWeighted_real_bound (lower : ℝ) (grade : ℕ) (scalar : ℝ) (field : AnnularRawFamily lower)
    (member : HasAnnularRawGrade lower grade field) (scaled : HasAnnularRawGrade lower grade (scalar • field)) :
    ‖annularRawWeighted lower grade (scalar • field) scaled‖ ≤ |scalar| * ‖annularRawWeighted lower grade field member‖ := by
  apply annularRawWeighted_bound lower grade 0 field (scalar • field) |scalar| (abs_nonneg scalar) member _ scaled
  intro mode
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs, pow_zero, mul_one, le_refl]

end Grad.AnnularRadialJets
