import AAZ13SameSolutionPhysicalJetMembership

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





def annularLeibnizConstant (lower : ℝ) (base order : ℕ) : ℝ :=
  ∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) * annularReciprocalJetBound lower base index

theorem annularLeibnizConstant_nonnegative (lower : ℝ) (positive : 0 < lower) (base order : ℕ) :
    0 ≤ annularLeibnizConstant lower base order :=
  Finset.sum_nonneg (fun index _ => mul_nonneg (Nat.cast_nonneg _) (annularReciprocalJetBound_nonnegative lower positive base index))

/-- A finite uniform bound for the exact differentiated radial coefficient.
The constant depends on the order and collar alone, never on Fourier modes,
the inserted grade, or the analytic phase. -/
theorem annularRawWeighted_leibniz_bound (lower : ℝ) (positive : 0 < lower) (grade base order : ℕ)
    (jet : ℕ → AnnularRawFamily lower) (member : ∀ index, HasAnnularRawGrade lower grade (jet index))
    (target : HasAnnularRawGrade lower grade (annularLeibniz lower positive base order jet))
    (size : ℝ) (jetBound : ∀ index ≤ order, ‖annularRawWeighted lower grade (jet index) (member index)‖ ≤ size) :
    ‖annularRawWeighted lower grade (annularLeibniz lower positive base order jet) target‖ ≤
      annularLeibnizConstant lower base order * size := by
  let term := fun index => order.choose index • annularReciprocalJet lower positive base index (jet (order - index))
  have reciprocalMember (index : ℕ) := annularRawGrade_reciprocalJet lower positive grade base index
    (jet (order - index)) (member (order - index))
  have termMember (index : ℕ) := annularRawGrade_nsmul lower grade (order.choose index) _ (reciprocalMember index)
  have sumBound := annularRawWeighted_sum_bound lower grade (Finset.range (order + 1)) term termMember target
  apply sumBound.trans
  change _ ≤ (∑ index ∈ Finset.range (order + 1), (order.choose index : ℝ) * annularReciprocalJetBound lower base index) * size
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index _
  have scaled := annularRawWeighted_nsmul_bound lower grade (order.choose index) _ (reciprocalMember index) (termMember index)
  have reciprocal := annularRawWeighted_reciprocalJet_bound lower positive grade base index
    (jet (order - index)) (member (order - index)) (reciprocalMember index)
  have factor := annularReciprocalJetBound_nonnegative lower positive base index
  exact scaled.trans ((mul_le_mul_of_nonneg_left
    (reciprocal.trans (mul_le_mul_of_nonneg_left (jetBound (order - index) (Nat.sub_le _ _)) factor))
    (Nat.cast_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

/-- The literal two-component Hilbert norm, rather than a maximum or a
renormed state. Its square is the prescribed sum of squared mode norms. -/
def annularRawStateSize (lower : ℝ) (grade : ℕ) (field : AnnularRawState lower)
    (member : HasAnnularRawStateGrade lower grade field) : ℝ :=
  ‖WithLp.toLp 2 (annularRawWeighted lower grade field.1 member.1,
    annularRawWeighted lower grade field.2 member.2)‖

theorem annularRawStateSize_nonnegative (lower : ℝ) (grade : ℕ) (field : AnnularRawState lower)
    (member : HasAnnularRawStateGrade lower grade field) : 0 ≤ annularRawStateSize lower grade field member := norm_nonneg _

theorem annularRawStateSize_square (lower : ℝ) (grade : ℕ) (field : AnnularRawState lower)
    (member : HasAnnularRawStateGrade lower grade field) :
    annularRawStateSize lower grade field member ^ 2 =
      ‖annularRawWeighted lower grade field.1 member.1‖ ^ 2 + ‖annularRawWeighted lower grade field.2 member.2‖ ^ 2 :=
  WithLp.prod_norm_sq_eq_of_L2 _

theorem annularRawStateSize_first (lower : ℝ) (grade : ℕ) (field : AnnularRawState lower)
    (member : HasAnnularRawStateGrade lower grade field) :
    ‖annularRawWeighted lower grade field.1 member.1‖ ≤ annularRawStateSize lower grade field member := by
  have square := annularRawStateSize_square lower grade field member
  nlinarith [sq_nonneg ‖annularRawWeighted lower grade field.2 member.2‖,
    norm_nonneg (annularRawWeighted lower grade field.1 member.1), annularRawStateSize_nonnegative lower grade field member]

theorem annularRawStateSize_second (lower : ℝ) (grade : ℕ) (field : AnnularRawState lower)
    (member : HasAnnularRawStateGrade lower grade field) :
    ‖annularRawWeighted lower grade field.2 member.2‖ ≤ annularRawStateSize lower grade field member := by
  have square := annularRawStateSize_square lower grade field member
  nlinarith [sq_nonneg ‖annularRawWeighted lower grade field.1 member.1‖,
    norm_nonneg (annularRawWeighted lower grade field.2 member.2), annularRawStateSize_nonnegative lower grade field member]

theorem annularRawStateSize_sum_bound (lower : ℝ) (grade : ℕ) (field : AnnularRawState lower)
    (member : HasAnnularRawStateGrade lower grade field) :
    annularRawStateSize lower grade field member ≤
      ‖annularRawWeighted lower grade field.1 member.1‖ + ‖annularRawWeighted lower grade field.2 member.2‖ := by
  have square := annularRawStateSize_square lower grade field member
  nlinarith [norm_nonneg (annularRawWeighted lower grade field.1 member.1),
    norm_nonneg (annularRawWeighted lower grade field.2 member.2), annularRawStateSize_nonnegative lower grade field member,
    mul_nonneg (norm_nonneg (annularRawWeighted lower grade field.1 member.1))
      (norm_nonneg (annularRawWeighted lower grade field.2 member.2))]

end Grad.AnnularRadialJets
