import AAZ14UniformLeibnizNorm

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






theorem annularRawWeighted_mono (lower : ℝ) (grade larger : ℕ) (bound : grade ≤ larger)
    (field : AnnularRawFamily lower) (member : HasAnnularRawGrade lower grade field)
    (largerMember : HasAnnularRawGrade lower larger field) :
    ‖annularRawWeighted lower grade field member‖ ≤ ‖annularRawWeighted lower larger field largerMember‖ := by
  apply lp.norm_mono (by norm_num)
  intro mode
  change ‖(annularGradeWeight 0 0 grade mode : ℂ) • field mode‖ ≤
    ‖(annularGradeWeight 0 0 larger mode : ℂ) • field mode‖
  rw [norm_smul, norm_smul, Complex.norm_real, Complex.norm_real,
    Real.norm_of_nonneg (annularGradeWeight_pos 0 0 grade mode).le,
    Real.norm_of_nonneg (annularGradeWeight_pos 0 0 larger mode).le]
  exact mul_le_mul_of_nonneg_right
    (annularGradeWeight_mono 0 0 grade 0 0 larger le_rfl le_rfl bound mode) (norm_nonneg _)

def annularJetPrefixSize (lower : ℝ) (grade order : ℕ) (jet : ℕ → AnnularRawState lower)
    (member : ∀ index grade, HasAnnularRawStateGrade lower grade (jet index)) : ℝ :=
  ∑ index ∈ Finset.range (order + 1), annularRawStateSize lower grade (jet index) (member index grade)

theorem annularJetPrefixSize_nonnegative (lower : ℝ) (grade order : ℕ) (jet : ℕ → AnnularRawState lower)
    (member : ∀ index grade, HasAnnularRawStateGrade lower grade (jet index)) :
    0 ≤ annularJetPrefixSize lower grade order jet member :=
  Finset.sum_nonneg (fun index _ => annularRawStateSize_nonnegative lower grade (jet index) (member index grade))

theorem annularJetPrefixSize_component (lower : ℝ) (grade larger order : ℕ) (gradeBound : grade ≤ larger)
    (jet : ℕ → AnnularRawState lower) (member : ∀ index grade, HasAnnularRawStateGrade lower grade (jet index))
    (index : ℕ) (indexBound : index ≤ order) :
    ‖annularRawWeighted lower grade (jet index).1 (member index grade).1‖ ≤ annularJetPrefixSize lower larger order jet member ∧
    ‖annularRawWeighted lower grade (jet index).2 (member index grade).2‖ ≤ annularJetPrefixSize lower larger order jet member := by
  have single : annularRawStateSize lower larger (jet index) (member index larger) ≤
      annularJetPrefixSize lower larger order jet member :=
    Finset.single_le_sum (fun other _ => annularRawStateSize_nonnegative lower larger (jet other) (member other larger))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le indexBound))
  exact ⟨(annularRawWeighted_mono lower grade larger gradeBound _ (member index grade).1 (member index larger).1).trans
      ((annularRawStateSize_first lower larger (jet index) (member index larger)).trans single),
    (annularRawWeighted_mono lower grade larger gradeBound _ (member index grade).2 (member index larger).2).trans
      ((annularRawStateSize_second lower larger (jet index) (member index larger)).trans single)⟩

theorem annularRawWeighted_norm_congr (lower : ℝ) (grade : ℕ) (first second : AnnularRawFamily lower)
    (firstMember : HasAnnularRawGrade lower grade first) (secondMember : HasAnnularRawGrade lower grade second)
    (equality : first = second) :
    ‖annularRawWeighted lower grade first firstMember‖ = ‖annularRawWeighted lower grade second secondMember‖ := by
  subst second
  rfl

theorem annularRawWeighted_three_bound (lower : ℝ) (grade : ℕ) (first second third : AnnularRawFamily lower)
    (firstMember : HasAnnularRawGrade lower grade first) (secondMember : HasAnnularRawGrade lower grade second)
    (thirdMember : HasAnnularRawGrade lower grade third)
    (target : HasAnnularRawGrade lower grade (first + second + third)) :
    ‖annularRawWeighted lower grade (first + second + third) target‖ ≤
      ‖annularRawWeighted lower grade first firstMember‖ + ‖annularRawWeighted lower grade second secondMember‖ +
        ‖annularRawWeighted lower grade third thirdMember‖ := by
  have twoMember := annularRawGrade_add lower grade first second firstMember secondMember
  have two := annularRawWeighted_add_bound lower grade first second firstMember secondMember twoMember
  have three := annularRawWeighted_add_bound lower grade (first + second) third twoMember thirdMember target
  linarith

theorem annularRawWeighted_five_bound (lower : ℝ) (grade : ℕ) (first second third fourth fifth : AnnularRawFamily lower)
    (firstMember : HasAnnularRawGrade lower grade first) (secondMember : HasAnnularRawGrade lower grade second)
    (thirdMember : HasAnnularRawGrade lower grade third) (fourthMember : HasAnnularRawGrade lower grade fourth)
    (fifthMember : HasAnnularRawGrade lower grade fifth)
    (target : HasAnnularRawGrade lower grade (first + second + third + fourth + fifth)) :
    ‖annularRawWeighted lower grade (first + second + third + fourth + fifth) target‖ ≤
      ‖annularRawWeighted lower grade first firstMember‖ + ‖annularRawWeighted lower grade second secondMember‖ +
        ‖annularRawWeighted lower grade third thirdMember‖ + ‖annularRawWeighted lower grade fourth fourthMember‖ +
          ‖annularRawWeighted lower grade fifth fifthMember‖ := by
  have twoMember := annularRawGrade_add lower grade first second firstMember secondMember
  have threeMember := annularRawGrade_add lower grade (first + second) third twoMember thirdMember
  have fourMember := annularRawGrade_add lower grade (first + second + third) fourth threeMember fourthMember
  have three := annularRawWeighted_three_bound lower grade first second third firstMember secondMember thirdMember threeMember
  have four := annularRawWeighted_add_bound lower grade (first + second + third) fourth threeMember fourthMember fourMember
  have five := annularRawWeighted_add_bound lower grade (first + second + third + fourth) fifth fourMember fifthMember target
  linarith

end Grad.AnnularRadialJets
