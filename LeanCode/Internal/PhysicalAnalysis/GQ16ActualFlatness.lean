import GQ15AngularFlatness

noncomputable section

set_option maxHeartbeats 1500000

namespace Grad.GaugeCoefficients.Physical.GaugeTransfer

open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.NonlinearDivision
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Allocation

theorem apCurrentProjection_axisFlat {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    {grade : ℕ} (large : 2 ≤ grade) (angle : ℝ) (field : apGrade L sigma gamma ell 3 grade)
    (flat : ClosedAxisFlat (apPhysicalValue admissible large angle field)) :
    ClosedAxisFlat (apPhysicalValue admissible large angle (apCurrentProjection admissible gauge grade field)) := by
  let firstCoefficient := cMapCoefficient admissible grade 3 3 angle (fullGaugeFamily gauge grade)
  let lastCoefficient := cMapCoefficient admissible grade 3 3 angle (complementExtensionFamily admissible gauge grade)
  have firstFlat : ClosedAxisFlat (cMapAction firstCoefficient (apPhysicalValue admissible large angle field)) :=
    flat.operator firstCoefficient
  have projectedFlat : ClosedAxisFlat (cMapComplement (cMapAction firstCoefficient (apPhysicalValue admissible large angle field))) :=
    firstFlat.complement
  have removedFlat : ClosedAxisFlat (cMapAction lastCoefficient
      (cMapComplement (cMapAction firstCoefficient (apPhysicalValue admissible large angle field)))) :=
    projectedFlat.operator lastCoefficient
  rw [apCurrentProjection_physical]
  exact flat.sub removedFlat

/-- Literal zero value and zero first Cartesian derivative in the
faithful physical realization; no additional AP2 graph coordinate. -/
def APAxisFirstJetZero {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {dimension grade : ℕ} (large : 2 ≤ grade) (field : apGrade L sigma gamma ell dimension grade) : Prop :=
  ∀ angle : ℝ, apPhysicalValue admissible large angle field closedOrigin = 0 ∧
    HasFDerivAt (closedFieldExtension (apPhysicalValue admissible large angle field))
      (0 : SpatialPlane →L[ℝ] ComplexEuclidean dimension) (0 : SpatialPlane)

/-- Exact CT_GC07: the actual original AP2 Qa preserves both Cartesian
first jets. No derivative or inverse property of a new coefficient is
assumed; the already constructed continuous multipliers suffice. -/
theorem apCurrentProjection_preserves_firstJet {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) (gauge : CoefficientFamily L sigma gamma ell 3 3)
    {grade : ℕ} (large : 2 ≤ grade) (field : apGrade L sigma gamma ell 3 grade)
    (flat : APAxisFirstJetZero admissible large field) :
    APAxisFirstJetZero admissible large (apCurrentProjection admissible gauge grade field) := by
  intro angle
  apply (closedAxisFlat_iff_firstJet _).mp
  exact apCurrentProjection_axisFlat admissible gauge large angle field
    ((closedAxisFlat_iff_firstJet _).mpr (flat angle))

/-- One original low neighborhood supplies the actual gauge projection
and zero-first-jet preservation simultaneously, for every grade. -/
def ActualGaugeFlatnessGoal (parameters : PhaseParameters) (L radius threshold : ℝ) : Prop :=
  ∃ lowRadius : ℝ, 0 < lowRadius ∧ lowRadius ≤ 1 ∧
    ∀ (ell rho alpha delta parameter epsilon : ℝ)
      (admissible : Admissible L parameters.sigma0 parameters.gamma ell),
      |alpha| ≤ radius → |delta| ≤ radius → |parameter| ≤ radius →
      ∀ base : ACore parameters 3,
        physicalBudget parameters base rho epsilon 10 < lowRadius →
        physicalBudget parameters base rho epsilon 12 ≤ 1 →
        ∃ ledger : ActualLedger parameters admissible rho alpha delta parameter epsilon base,
          primitiveSize parameters admissible rho alpha delta parameter epsilon base 2 ≤ threshold ∧
          (∀ grade, ActualProjectionLaws admissible ledger.val.gaugeDeviation grade) ∧
          ∀ (grade : ℕ) (large : 2 ≤ grade) (field : apGrade L parameters.sigma0 parameters.gamma ell 3 grade),
            APAxisFirstJetZero admissible large field →
              APAxisFirstJetZero admissible large (apCurrentProjection admissible ledger.val.gaugeDeviation grade field)

theorem actualGaugeFlatness (parameters : PhaseParameters) (L radius threshold : ℝ)
    (positive : 0 < L) (radiusNonnegative : 0 ≤ radius) (thresholdPositive : 0 < threshold) :
    ActualGaugeFlatnessGoal parameters L radius threshold := by
  obtain ⟨lowRadius, positiveRadius, boundedRadius, supplied⟩ :=
    actualGaugeProjection parameters L radius threshold positive radiusNonnegative thresholdPositive
  refine ⟨lowRadius, positiveRadius, boundedRadius, ?_⟩
  intro ell rho alpha delta parameter epsilon admissible alphaSmall deltaSmall parameterSmall base low bounded
  obtain ⟨ledger, margin, laws⟩ := supplied ell rho alpha delta parameter epsilon admissible
    alphaSmall deltaSmall parameterSmall base low bounded
  exact ⟨ledger, margin, laws, fun _ large field flat =>
    apCurrentProjection_preserves_firstJet admissible ledger.val.gaugeDeviation large field flat⟩

end Grad.GaugeCoefficients.Physical.GaugeTransfer
