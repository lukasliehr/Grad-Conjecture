import AAZ11WeightedJetOperations

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



def HasAnnularRawStateGrade (lower : ℝ) (grade : ℕ) (field : AnnularRawState lower) : Prop :=
  HasAnnularRawGrade lower grade field.1 ∧ HasAnnularRawGrade lower grade field.2

def HasAnnularRawSourceGrade (lower : ℝ) (grade : ℕ) (field : AnnularRawSource lower) : Prop :=
  HasAnnularRawGrade lower grade field.1 ∧ HasAnnularRawGrade lower grade field.2.1 ∧
    HasAnnularRawGrade lower grade field.2.2

/-- Genuine weighted square summability of every newly constructed physical
jet, proved from lower solution orders and source grades before taking its
norm. The same original phase occurs in every coordinate. -/
theorem annularPhysicalStateJet_allGrades (lower length : ℝ) (positive : 0 < lower)
    (lengthPositive : 0 < length) (initial : AnnularRawState lower) (source : ℕ → AnnularRawSource lower)
    (initialGrades : ∀ grade, HasAnnularRawStateGrade lower grade initial)
    (sourceGrades : ∀ order grade, HasAnnularRawSourceGrade lower grade (source order))
    (order grade : ℕ) :
    HasAnnularRawStateGrade lower grade (annularPhysicalStateJet lower positive length initial source order) := by
  induction order using Nat.strong_induction_on generalizing grade with
  | h order previous =>
    cases order with
    | zero => simpa only [annularPhysicalStateJet_zero] using initialGrades grade
    | succ order =>
      let jet := annularPhysicalStateJet lower positive length initial source
      have member (index : ℕ) (bound : index ≤ order) (grade : ℕ) :
          HasAnnularRawStateGrade lower grade (jet index) :=
        previous index (Nat.lt_succ_of_le bound) grade
      have pRadial := annularRawGrade_leibniz lower positive grade 1 order (fun index => (jet index).1)
        (fun index bound => (member index bound grade).1)
      have xiRadial := annularRawGrade_leibniz lower positive grade 1 order (fun index => (jet index).2)
        (fun index bound => (member index bound grade).2)
      have xiSquare := annularRawGrade_leibniz lower positive (grade + 1) 2 order (fun index => (jet index).2)
        (fun index bound => (member index bound (grade + 1)).2)
      have angular := annularRawGrade_symbol lower grade 1 annularAngularISymbol 1 zero_le_one
        (fun mode => by simpa only [one_mul, pow_one] using annularAngularISymbol_bound mode) _ xiSquare
      have longitudinal := annularRawGrade_symbol lower grade 2 (annularLongitudinalISymbol length)
        (1 / (3 * length ^ 2)) (by positivity) (annularLongitudinalISymbol_bound length lengthPositive)
        _ (member order le_rfl (grade + 2)).2
      have longitudinalSource := annularRawGrade_symbol lower grade 1 (annularLongitudinalSourceSymbol length)
        (1 / (3 * length)) (by positivity)
        (fun mode => by simpa only [pow_one] using annularLongitudinalSourceSymbol_bound length lengthPositive mode)
        _ (sourceGrades order (grade + 1)).2.2
      have pResult := annularRawGrade_add lower grade _ _
        (annularRawGrade_add lower grade _ _ (annularRawGrade_add lower grade _ _
          (annularRawGrade_add lower grade _ _ pRadial angular) longitudinal) (sourceGrades order grade).2.1)
        longitudinalSource
      have dGrade := annularRawGrade_symbol lower grade 1 (fun mode => -annularDSymbol mode) 1 zero_le_one
        (fun mode => by simpa only [norm_neg, one_mul, pow_one] using annularDSymbol_frequency_bound mode)
        _ (member order le_rfl (grade + 1)).1
      have xiResult := annularRawGrade_add lower grade _ _
        (annularRawGrade_add lower grade _ _ (annularRawGrade_real lower grade (-2) _ xiRadial) dGrade)
        (sourceGrades order grade).1
      exact (congrArg (HasAnnularRawStateGrade lower grade)
        (annularPhysicalStateJet_succ lower positive length initial source order)).mpr ⟨pResult, xiResult⟩

end Grad.AnnularRadialJets
