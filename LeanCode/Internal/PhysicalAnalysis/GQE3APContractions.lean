import GQE2CoreContractions

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger

theorem apFiniteJetMap_single {input output : ℕ} (mapping : ClosedJet input →ₗ[ℂ] ClosedJet output)
    (cell : ℤ) (field : ClosedJet input) :
    apFiniteJetMap mapping (Finsupp.single cell field) = Finsupp.single cell (mapping field) := by
  apply Finsupp.ext
  intro other
  by_cases same : other = cell
  · subst other; simp [apFiniteJetMap_apply]
  · simp [apFiniteJetMap_apply, Finsupp.single_eq_of_ne same]

def apRadialContraction {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    apGrade L sigma gamma ell 3 grade →L[ℂ] apGrade L sigma gamma ell 1 grade :=
  apMultiplier admissible (fixedJetFamily L sigma gamma ell radialRowJet grade)

def apTangentContraction {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    apGrade L sigma gamma ell 3 grade →L[ℂ] apGrade L sigma gamma ell 1 grade :=
  apMultiplier admissible (fixedJetFamily L sigma gamma ell tangentRowJet grade)

def apPairedContraction {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell) (grade : ℕ) :
    apGrade L sigma gamma ell 3 grade →L[ℂ]
      (apGrade L sigma gamma ell 1 grade × apGrade L sigma gamma ell 1 grade) :=
  (apRadialContraction admissible grade).prod
    ((apMeanFree L sigma gamma ell 1 grade).comp (apTangentContraction admissible grade))

theorem apRadialContraction_single {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (cell : ℤ) (field : ClosedJet 3) :
    apRadialContraction admissible grade (apFiniteInto L sigma gamma ell (Finsupp.single cell field)) =
      apFiniteInto L sigma gamma ell (Finsupp.single cell (apProductJet radialRowJet field)) := by
  exact (apMultiplier_single admissible cell 0 radialRowJet field).trans
    (congrArg (fun index => apFiniteInto L sigma gamma ell
      (Finsupp.single index (apProductJet radialRowJet field))) (add_zero cell))

theorem apTangentContraction_single {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (cell : ℤ) (field : ClosedJet 3) :
    apTangentContraction admissible grade (apFiniteInto L sigma gamma ell (Finsupp.single cell field)) =
      apFiniteInto L sigma gamma ell (Finsupp.single cell (apProductJet tangentRowJet field)) := by
  exact (apMultiplier_single admissible cell 0 tangentRowJet field).trans
    (congrArg (fun index => apFiniteInto L sigma gamma ell
      (Finsupp.single index (apProductJet tangentRowJet field))) (add_zero cell))

theorem apRadialContraction_complement {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (field : apGrade L sigma gamma ell 3 grade) :
    apRadialContraction admissible grade (apComplement L sigma gamma ell grade field) = 0 := by
  have equality : (apRadialContraction admissible grade).comp (apComplement L sigma gamma ell grade) = 0 := by
    apply apFiniteGenerator_ext L sigma gamma ell
    intro cell core
    change apRadialContraction admissible grade
      (apComplement L sigma gamma ell grade (apFiniteInto L sigma gamma ell (Finsupp.single cell core))) = 0
    rw [apComplement_core, apFiniteJetMap_single, apRadialContraction_single,
      radialRowJet_complement_zero, Finsupp.single_zero, map_zero]
  exact congrArg (fun mapping => mapping field) equality

theorem apMeanFree_tangent_complement {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (field : apGrade L sigma gamma ell 3 grade) :
    apMeanFree L sigma gamma ell 1 grade
      (apTangentContraction admissible grade (apComplement L sigma gamma ell grade field)) = 0 := by
  have equality : ((apMeanFree L sigma gamma ell 1 grade).comp
      (apTangentContraction admissible grade)).comp (apComplement L sigma gamma ell grade) = 0 := by
    apply apFiniteGenerator_ext L sigma gamma ell
    intro cell core
    change apMeanFree L sigma gamma ell 1 grade (apTangentContraction admissible grade
      (apComplement L sigma gamma ell grade (apFiniteInto L sigma gamma ell (Finsupp.single cell core)))) = 0
    rw [apComplement_core, apFiniteJetMap_single, apTangentContraction_single]
    change apFiniteInto L sigma gamma ell (Finsupp.single cell (apProductJet tangentRowJet (fixedComplementJet core))) -
      apAngularMean L sigma gamma ell 1 grade
        (apFiniteInto L sigma gamma ell (Finsupp.single cell (apProductJet tangentRowJet (fixedComplementJet core)))) = 0
    rw [apAngularMean_core, apFiniteJetMap_single]
    change apFiniteInto L sigma gamma ell (Finsupp.single cell (apProductJet tangentRowJet (fixedComplementJet core))) -
      apFiniteInto L sigma gamma ell (Finsupp.single cell
        (angularClosedJet 0 (apProductJet tangentRowJet (fixedComplementJet core)))) = 0
    rw [tangentRowJet_complement_mean, sub_self]
  exact congrArg (fun mapping => mapping field) equality

/-- The paired bounded zero-order map vanishes on the actual completed
range of C0, at every grade, not merely on a tangency-defined substitute. -/
theorem apPairedContraction_range_zero {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (grade : ℕ) (field : apGrade L sigma gamma ell 3 grade)
    (member : field ∈ apComplementRange L sigma gamma ell grade) :
    apPairedContraction admissible grade field = 0 := by
  obtain ⟨input, rfl⟩ := member
  exact Prod.ext (apRadialContraction_complement admissible grade input)
    (apMeanFree_tangent_complement admissible grade input)

end Grad.GaugeCoefficients.Physical.Compensated
