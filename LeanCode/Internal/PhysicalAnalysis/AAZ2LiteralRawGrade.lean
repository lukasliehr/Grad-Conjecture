import AAZ1WeakReciprocalPowers

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

/-- Modewise physical derivatives are defined before their weighted square
summability is proved. Storage is the original sqrt(r) exp(Phi) storage. -/
abbrev AnnularRawFamily (lower : ℝ) := HighAnnularMode → RadialL2 1 lower

def HasAnnularRawGrade (lower : ℝ) (grade : ℕ) (field : AnnularRawFamily lower) : Prop :=
  Memℓp (fun mode => (annularGradeWeight 0 0 grade mode : ℂ) • field mode) 2

def annularRawWeighted (lower : ℝ) (grade : ℕ) (field : AnnularRawFamily lower)
    (member : HasAnnularRawGrade lower grade field) : AnnularBulk lower :=
  ⟨fun mode => (annularGradeWeight 0 0 grade mode : ℂ) • field mode, member⟩

theorem annularRawGrade_lp (lower : ℝ) (grade : ℕ) (field : AnnularBulk lower) :
    HasAnnularRawGrade lower grade (fun mode => field mode) ↔ HasAnnularLpGrade 0 0 grade field := Iff.rfl

theorem annularRawGrade_zero (lower : ℝ) (field : AnnularBulk lower) :
    HasAnnularRawGrade lower 0 (fun mode => field mode) := by
  have member : Memℓp (fun mode : HighAnnularMode => field mode) 2 := field.property
  simpa only [HasAnnularRawGrade, annularGradeWeight_zero, Complex.ofReal_one, one_smul] using member

theorem annularRawWeighted_norm_sq (lower : ℝ) (grade : ℕ) (field : AnnularRawFamily lower)
    (member : HasAnnularRawGrade lower grade field) :
    ‖annularRawWeighted lower grade field member‖ ^ 2 =
      ∑' mode : HighAnnularMode, (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ (2 * grade) * ‖field mode‖ ^ 2 := by
  have formula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (annularRawWeighted lower grade field member)
  norm_num at formula
  rw [formula]
  apply tsum_congr
  intro mode
  change ‖(annularGradeWeight 0 0 grade mode : ℂ) • field mode‖ ^ 2 = _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (annularGradeWeight_pos 0 0 grade mode).le,
    mul_pow, annularGradeWeight_literal]
  simp only [pow_zero, mul_one]
  rw [← pow_mul, Nat.mul_comm grade 2]
  rfl

theorem annularRawWeighted_point_bound (lower : ℝ) (grade loss : ℕ)
    (source target : AnnularRawFamily lower) (constant : ℝ)
    (pointwise : ∀ mode, ‖target mode‖ ≤ constant *
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ loss * ‖source mode‖)
    (mode : HighAnnularMode) :
    ‖(annularGradeWeight 0 0 grade mode : ℂ) • target mode‖ ≤
      constant * ‖(annularGradeWeight 0 0 (grade + loss) mode : ℂ) • source mode‖ := by
  simp only [norm_smul, Complex.norm_real, Real.norm_of_nonneg (annularGradeWeight_pos 0 0 grade mode).le,
    Real.norm_of_nonneg (annularGradeWeight_pos 0 0 (grade + loss) mode).le]
  have estimate := mul_le_mul_of_nonneg_left (pointwise mode) (annularGradeWeight_pos 0 0 grade mode).le
  exact estimate.trans_eq (by
    rw [annularGradeWeight_literal, annularGradeWeight_literal]
    simp only [pow_zero, mul_one, pow_add]
    unfold Grad.AnnularVariational.annularFrequency
    ring)

/-- Membership is obtained from the pointwise estimate, before the norm
of the new derivative is used. This is the noncircular grade step. -/
theorem annularRawGrade_of_bound (lower : ℝ) (grade loss : ℕ)
    (source target : AnnularRawFamily lower) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (sourceGrade : HasAnnularRawGrade lower (grade + loss) source)
    (pointwise : ∀ mode, ‖target mode‖ ≤ constant *
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ loss * ‖source mode‖) :
    HasAnnularRawGrade lower grade target := by
  let dominant := constant • lpNormFamily (annularRawWeighted lower (grade + loss) source sourceGrade)
  apply (lp.memℓp dominant).mono'
  intro mode
  change ‖(annularGradeWeight 0 0 grade mode : ℂ) • target mode‖ ≤
    ‖constant • ‖(annularGradeWeight 0 0 (grade + loss) mode : ℂ) • source mode‖‖
  have dominantNorm : ‖constant • ‖(annularGradeWeight 0 0 (grade + loss) mode : ℂ) • source mode‖‖ =
      constant * ‖(annularGradeWeight 0 0 (grade + loss) mode : ℂ) • source mode‖ := by
    rw [norm_smul, Real.norm_of_nonneg nonnegative, norm_norm]
  exact (annularRawWeighted_point_bound lower grade loss source target constant pointwise mode).trans_eq dominantNorm.symm

theorem annularRawWeighted_bound (lower : ℝ) (grade loss : ℕ)
    (source target : AnnularRawFamily lower) (constant : ℝ) (nonnegative : 0 ≤ constant)
    (sourceGrade : HasAnnularRawGrade lower (grade + loss) source)
    (pointwise : ∀ mode, ‖target mode‖ ≤ constant *
      (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ loss * ‖source mode‖)
    (targetGrade : HasAnnularRawGrade lower grade target) :
    ‖annularRawWeighted lower grade target targetGrade‖ ≤
      constant * ‖annularRawWeighted lower (grade + loss) source sourceGrade‖ := by
  have estimate : ‖annularRawWeighted lower grade target targetGrade‖ ≤
      ‖constant • lpNormFamily (annularRawWeighted lower (grade + loss) source sourceGrade)‖ := by
    apply lp.norm_mono (by norm_num)
    intro mode
    change ‖(annularGradeWeight 0 0 grade mode : ℂ) • target mode‖ ≤
      ‖constant • ‖(annularGradeWeight 0 0 (grade + loss) mode : ℂ) • source mode‖‖
    have dominantNorm : ‖constant • ‖(annularGradeWeight 0 0 (grade + loss) mode : ℂ) • source mode‖‖ =
        constant * ‖(annularGradeWeight 0 0 (grade + loss) mode : ℂ) • source mode‖ := by
      rw [norm_smul, Real.norm_of_nonneg nonnegative, norm_norm]
    exact (annularRawWeighted_point_bound lower grade loss source target constant pointwise mode).trans_eq dominantNorm.symm
  exact estimate.trans_eq (by rw [norm_smul, Real.norm_of_nonneg nonnegative, lpNormFamily_norm])

end Grad.AnnularRadialJets
