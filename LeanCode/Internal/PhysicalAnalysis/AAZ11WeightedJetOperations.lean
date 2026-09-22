import AAZ10UniformJetCoefficientBounds

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


theorem annularRawFrequency_one_le (mode : HighAnnularMode) :
    1 ≤ Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2 := by
  unfold Grad.AnnularVariational.annularFrequency
  linarith [abs_nonneg (mode.val.1 : ℝ), abs_nonneg (mode.val.2 : ℝ)]

theorem annularRawGrade_lower (lower : ℝ) (grade loss : ℕ) (field : AnnularRawFamily lower)
    (member : HasAnnularRawGrade lower (grade + loss) field) : HasAnnularRawGrade lower grade field := by
  apply annularRawGrade_of_bound lower grade loss field field 1 zero_le_one member
  intro mode
  simpa only [one_mul] using
    (mul_le_mul_of_nonneg_right (one_le_pow₀ (n := loss) (annularRawFrequency_one_le mode)) (norm_nonneg (field mode)))

theorem annularRawWeighted_lower (lower : ℝ) (grade loss : ℕ) (field : AnnularRawFamily lower)
    (member : HasAnnularRawGrade lower (grade + loss) field) (target : HasAnnularRawGrade lower grade field) :
    ‖annularRawWeighted lower grade field target‖ ≤ ‖annularRawWeighted lower (grade + loss) field member‖ := by
  have bound := annularRawWeighted_bound lower grade loss field field 1 zero_le_one member
    (fun mode => by simpa only [one_mul] using
      (mul_le_mul_of_nonneg_right (one_le_pow₀ (n := loss) (annularRawFrequency_one_le mode)) (norm_nonneg (field mode)))) target
  simpa only [one_mul] using bound

theorem annularRawGrade_nsmul (lower : ℝ) (grade : ℕ) (scalar : ℕ) (field : AnnularRawFamily lower)
    (member : HasAnnularRawGrade lower grade field) : HasAnnularRawGrade lower grade (scalar • field) := by
  induction scalar with
  | zero => simpa only [zero_nsmul] using annularRawGrade_zero_family lower grade
  | succ scalar previous =>
    rw [succ_nsmul]
    exact annularRawGrade_add lower grade _ _ previous member

theorem annularRawWeighted_nsmul_bound (lower : ℝ) (grade : ℕ) (scalar : ℕ) (field : AnnularRawFamily lower)
    (member : HasAnnularRawGrade lower grade field) (target : HasAnnularRawGrade lower grade (scalar • field)) :
    ‖annularRawWeighted lower grade (scalar • field) target‖ ≤ (scalar : ℝ) * ‖annularRawWeighted lower grade field member‖ := by
  apply annularRawWeighted_bound lower grade 0 field (scalar • field) (scalar : ℝ) (Nat.cast_nonneg scalar) member _ target
  intro mode
  simpa only [Pi.smul_apply, pow_zero, mul_one] using
    (show ‖scalar • field mode‖ ≤ (scalar : ℝ) * ‖field mode‖ from norm_nsmul_le)

theorem annularRawGrade_symbol (lower : ℝ) (grade loss : ℕ) (symbol : HighAnnularMode → ℂ)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ∀ mode, ‖symbol mode‖ ≤ constant * (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ loss)
    (field : AnnularRawFamily lower) (member : HasAnnularRawGrade lower (grade + loss) field) :
    HasAnnularRawGrade lower grade (annularRawSymbol lower symbol field) := by
  apply annularRawGrade_of_bound lower grade loss field _ constant nonnegative member
  intro mode
  exact (norm_smul (symbol mode) (field mode)).le.trans
    (mul_le_mul_of_nonneg_right (bound mode) (norm_nonneg (field mode)))

theorem annularRawWeighted_symbol_bound (lower : ℝ) (grade loss : ℕ) (symbol : HighAnnularMode → ℂ)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ∀ mode, ‖symbol mode‖ ≤ constant * (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) ^ loss)
    (field : AnnularRawFamily lower) (member : HasAnnularRawGrade lower (grade + loss) field)
    (target : HasAnnularRawGrade lower grade (annularRawSymbol lower symbol field)) :
    ‖annularRawWeighted lower grade (annularRawSymbol lower symbol field) target‖ ≤
      constant * ‖annularRawWeighted lower (grade + loss) field member‖ := by
  apply annularRawWeighted_bound lower grade loss field _ constant nonnegative member _ target
  intro mode
  exact (norm_smul (symbol mode) (field mode)).le.trans
    (mul_le_mul_of_nonneg_right (bound mode) (norm_nonneg (field mode)))

theorem annularRawGrade_reciprocalJet (lower : ℝ) (positive : 0 < lower) (grade base order : ℕ)
    (field : AnnularRawFamily lower) (member : HasAnnularRawGrade lower grade field) :
    HasAnnularRawGrade lower grade (annularReciprocalJet lower positive base order field) := by
  apply annularRawGrade_of_bound lower grade 0 field _ (annularReciprocalJetBound lower base order)
    (annularReciprocalJetBound_nonnegative lower positive base order) member
  intro mode
  simpa only [pow_zero, mul_one] using annularReciprocalJet_point_bound lower positive base order field mode

theorem annularRawWeighted_reciprocalJet_bound (lower : ℝ) (positive : 0 < lower) (grade base order : ℕ)
    (field : AnnularRawFamily lower) (member : HasAnnularRawGrade lower grade field)
    (target : HasAnnularRawGrade lower grade (annularReciprocalJet lower positive base order field)) :
    ‖annularRawWeighted lower grade (annularReciprocalJet lower positive base order field) target‖ ≤
      annularReciprocalJetBound lower base order * ‖annularRawWeighted lower grade field member‖ := by
  apply annularRawWeighted_bound lower grade 0 field _ (annularReciprocalJetBound lower base order)
    (annularReciprocalJetBound_nonnegative lower positive base order) member _ target
  intro mode
  simpa only [pow_zero, mul_one] using annularReciprocalJet_point_bound lower positive base order field mode

theorem annularRawGrade_leibniz (lower : ℝ) (positive : 0 < lower) (grade base order : ℕ)
    (jet : ℕ → AnnularRawFamily lower) (member : ∀ index ≤ order, HasAnnularRawGrade lower grade (jet index)) :
    HasAnnularRawGrade lower grade (annularLeibniz lower positive base order jet) := by
  apply annularRawGrade_sum lower grade (Finset.range (order + 1))
  intro index _
  exact annularRawGrade_nsmul lower grade (order.choose index) _
    (annularRawGrade_reciprocalJet lower positive grade base index (jet (order - index))
      (member (order - index) (Nat.sub_le _ _)))

end Grad.AnnularRadialJets
