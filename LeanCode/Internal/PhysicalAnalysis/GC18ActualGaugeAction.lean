import GC18ProfileAlgebra

noncomputable section

set_option maxHeartbeats 1600000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

def fullGaugeValueAction {L sigma gamma ell : ℝ} (gauge : CoefficientFamily L sigma gamma ell 3 3)
    (grade : ℕ) (angle : ℝ) (field : ClosedDisk → PhysicalValue 3) (point : ClosedDisk) : PhysicalValue 3 :=
  coefficientPhysicalValue (fullGaugeFamily gauge grade) angle point (field point)

theorem fullGaugeValueAction_continuous {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (grade : ℕ) (angle : ℝ) (field : ClosedDisk → PhysicalValue 3) (continuous : Continuous field) :
    Continuous (fullGaugeValueAction gauge grade angle field) :=
  (coefficientPhysicalValue_continuous admissible (fullGaugeFamily gauge)
    (fullGaugeFamily_coherent gauge coherent) grade angle).clm_apply continuous

/-- The polar evaluation of the actual full C product, with radial profiles
cancelled algebraically. No norm estimate is imposed on the profile α. -/
theorem fixedComplement_fullGauge_profile {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (grade : ℕ) (angle : ℝ) (first second : ClosedDisk → ℂ)
    (firstRadial : IsDiskRadial first) (secondRadial : IsDiskRadial second) (point : ClosedDisk) :
    fixedComplementValue (fullGaugeValueAction gauge grade angle (complementProfile first second)) point =
      radialBlockValue
        (familyMatrix (muCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (etaCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (nuCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (deltaCoefficient admissible gauge) grade angle point 0 0) point
        (complementProfile first second point) := by
  have tangentMoment : closedAngularMean (fun other => storedTangentDot other
      (fullGaugeValueAction gauge grade angle (complementProfile first second) other)) point =
      first point * (radiusScalar point * familyMatrix (muCoefficient admissible gauge) grade angle point 0 0) +
        second point * (radiusScalar point * familyMatrix (etaCoefficient admissible gauge) grade angle point 0 0) := by
    unfold fullGaugeValueAction
    simp_rw [gaugeTangentDot_profile]
    rw [closedAngularMean_radial_linear first second _ _ firstRadial secondRadial
      (fullGauge_tangent_moment_continuous admissible gauge coherent grade angle)
      (fullGauge_scalar_moment_continuous admissible gauge coherent grade angle),
      fullGauge_mu_moment admissible gauge coherent, fullGauge_eta_moment admissible gauge coherent]
  have scalarMoment : closedAngularMean (fun other =>
      (fullGaugeValueAction gauge grade angle (complementProfile first second) other) 2) point =
      first point * (radiusScalar point * familyMatrix (nuCoefficient admissible gauge) grade angle point 0 0) +
        second point * familyMatrix (deltaCoefficient admissible gauge) grade angle point 0 0 := by
    unfold fullGaugeValueAction
    simp_rw [gaugeThird_profile]
    rw [closedAngularMean_radial_linear first second _ _ firstRadial secondRadial
      (fullGauge_third_tangent_continuous admissible gauge coherent grade angle)
      (fullGauge_third_scalar_continuous admissible gauge coherent grade angle),
      fullGauge_nu_moment admissible gauge coherent, fullGauge_delta_moment admissible gauge coherent]
  rw [fixedComplementValue, radialBlockValue_profile]
  change ((radiusScalar point)⁻¹ * closedAngularMean (fun other => storedTangentDot other
      (fullGaugeValueAction gauge grade angle (complementProfile first second) other)) point) • storedTangent point +
      closedAngularMean (fun other => (fullGaugeValueAction gauge grade angle (complementProfile first second) other) 2) point • storedScalar =
    (familyMatrix (muCoefficient admissible gauge) grade angle point 0 0 * first point +
      familyMatrix (etaCoefficient admissible gauge) grade angle point 0 0 * second point) • storedTangent point +
    (familyMatrix (nuCoefficient admissible gauge) grade angle point 0 0 * radiusScalar point * first point +
      familyMatrix (deltaCoefficient admissible gauge) grade angle point 0 0 * second point) • storedScalar
  rw [tangentMoment, scalarMoment]
  apply congrArg₂ (fun left right : PhysicalValue 3 => left + right)
  · by_cases axis : point.val = 0
    · have tangentZero : storedTangent point = 0 := by
        apply PiLp.ext
        intro row
        fin_cases row <;> simp [storedTangent, axis]
      rw [tangentZero, smul_zero, smul_zero]
    · congr 1
      field_simp [radiusScalar_nonzero point axis]
  · congr 1
    ring

theorem cartesianComplement_fullGauge_profile {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (grade : ℕ) (angle : ℝ) (first second : ClosedDisk → ℂ)
    (firstRadial : IsDiskRadial first) (secondRadial : IsDiskRadial second)
    (continuous : Continuous (complementProfile first second)) (point : ClosedDisk) :
    cartesianComplementValue (fullGaugeValueAction gauge grade angle (complementProfile first second)) point =
      radialBlockValue
        (familyMatrix (muCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (etaCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (nuCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (deltaCoefficient admissible gauge) grade angle point 0 0) point
        (complementProfile first second point) := by
  rw [cartesianComplementValue_eq_polar _ (fullGaugeValueAction_continuous admissible gauge coherent grade angle _ continuous)]
  exact fixedComplement_fullGauge_profile admissible gauge coherent grade angle first second firstRadial secondRadial point

/-- Actual C0*C on the actual nonsingular Cartesian physical range. The
original AP2 normed completion is a separate realization boundary, not a
hidden replacement by this continuous-value carrier. -/
theorem cartesianGauge_on_range {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge)
    (grade : ℕ) (angle : ℝ) (field : C(ClosedDisk, PhysicalValue 3)) (member : field ∈ cartesianPhysicalRange)
    (point : ClosedDisk) :
    cartesianComplementValue (fullGaugeValueAction gauge grade angle field) point =
      radialBlockValue
        (familyMatrix (muCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (etaCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (nuCoefficient admissible gauge) grade angle point 0 0)
        (familyMatrix (deltaCoefficient admissible gauge) grade angle point 0 0) point (field point) := by
  have fixed := (mem_cartesianPhysicalRange_iff field).mp member
  let first := fun point => (radiusScalar point)⁻¹ * closedAngularMean (fun other => storedTangentDot other (field other)) point
  let second := closedAngularMean (fun point => field point 2)
  have profile : complementProfile first second = field := by
    funext other
    change fixedComplementValue field other = field other
    rw [← cartesianComplementValue_eq_polar field field.continuous other]
    exact congrArg (fun mapping : C(ClosedDisk, PhysicalValue 3) => mapping other) fixed
  have continuous : Continuous (complementProfile first second) := by rw [profile]; exact field.continuous
  have identity := cartesianComplement_fullGauge_profile admissible gauge coherent grade angle first second
    (fixedComplementValue_profile_first_radial field) (closedAngularMean_radial _) continuous point
  rw [profile] at identity
  exact identity

end Grad.GaugeCoefficients.Physical.RadialLedger
