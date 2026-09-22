import GC18ActualMoments
import GC18RadialValues

noncomputable section

set_option maxHeartbeats 1500000

open Set MeasureTheory
open scoped Topology BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

theorem closedAngularMean_radial_linear (first second left right : ClosedDisk → ℂ)
    (firstRadial : IsDiskRadial first) (secondRadial : IsDiskRadial second)
    (leftContinuous : Continuous left) (rightContinuous : Continuous right) (point : ClosedDisk) :
    closedAngularMean (fun other => first other * left other + second other * right other) point =
      first point * closedAngularMean left point + second point * closedAngularMean right point := by
  have firstRotation : ∀ rotation other, first (Grad.GaugeCoefficients.Radial.rotatedPoint rotation other) = first other := firstRadial
  have secondRotation : ∀ rotation other, second (Grad.GaugeCoefficients.Radial.rotatedPoint rotation other) = second other := secondRadial
  have leftIntegrable : IntegrableOn
      (fun time => left (Grad.GaugeCoefficients.Radial.rotatedPoint (2 * Real.pi * time) point)) (Icc (0 : ℝ) 1) volume :=
    (closedMeanIntegrand_continuous left leftContinuous point).continuousOn.integrableOn_Icc
  have rightIntegrable : IntegrableOn
      (fun time => right (Grad.GaugeCoefficients.Radial.rotatedPoint (2 * Real.pi * time) point)) (Icc (0 : ℝ) 1) volume :=
    (closedMeanIntegrand_continuous right rightContinuous point).continuousOn.integrableOn_Icc
  unfold closedAngularMean
  simp_rw [firstRotation, secondRotation]
  rw [integral_add (leftIntegrable.const_mul _) (rightIntegrable.const_mul _),
    integral_const_mul, integral_const_mul]

theorem storedTangent_continuous : Continuous storedTangent := by
  unfold storedTangent
  fun_prop

theorem storedTangentDot_continuous (field : ClosedDisk → PhysicalValue 3) (continuous : Continuous field) :
    Continuous (fun point => storedTangentDot point (field point)) := by
  unfold storedTangentDot
  fun_prop

theorem storedTangentDot_add (point : ClosedDisk) (first second : PhysicalValue 3) :
    storedTangentDot point (first + second) = storedTangentDot point first + storedTangentDot point second := by
  simp [storedTangentDot]
  ring

theorem storedTangentDot_smul (point : ClosedDisk) (scalar : ℂ) (value : PhysicalValue 3) :
    storedTangentDot point (scalar • value) = scalar * storedTangentDot point value := by
  simp [storedTangentDot]
  ring

theorem gaugeTangentDot_profile (mapping : ClosedDisk → OperatorValue 3 3)
    (first second : ClosedDisk → ℂ) (point : ClosedDisk) :
    storedTangentDot point (mapping point (complementProfile first second point)) =
      first point * storedTangentDot point (mapping point (storedTangent point)) +
        second point * storedTangentDot point (mapping point storedScalar) := by
  rw [complementProfile, map_add, map_smul, map_smul, storedTangentDot_add, storedTangentDot_smul, storedTangentDot_smul]

theorem gaugeThird_profile (mapping : ClosedDisk → OperatorValue 3 3)
    (first second : ClosedDisk → ℂ) (point : ClosedDisk) :
    (mapping point (complementProfile first second point)) 2 =
      first point * (mapping point (storedTangent point)) 2 + second point * (mapping point storedScalar) 2 := by
  simp [complementProfile, map_add, map_smul]

theorem fullGauge_tangent_moment_continuous {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) (grade : ℕ) (angle : ℝ) :
    Continuous (fun point => storedTangentDot point
      (coefficientPhysicalValue (fullGaugeFamily gauge grade) angle point (storedTangent point))) :=
  storedTangentDot_continuous _ ((coefficientPhysicalValue_continuous admissible (fullGaugeFamily gauge)
    (fullGaugeFamily_coherent gauge coherent) grade angle).clm_apply storedTangent_continuous)

theorem fullGauge_scalar_moment_continuous {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) (grade : ℕ) (angle : ℝ) :
    Continuous (fun point => storedTangentDot point
      (coefficientPhysicalValue (fullGaugeFamily gauge grade) angle point storedScalar)) :=
  storedTangentDot_continuous _ ((coefficientPhysicalValue_continuous admissible (fullGaugeFamily gauge)
    (fullGaugeFamily_coherent gauge coherent) grade angle).clm_apply continuous_const)

theorem fullGauge_third_tangent_continuous {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) (grade : ℕ) (angle : ℝ) :
    Continuous (fun point => (coefficientPhysicalValue (fullGaugeFamily gauge grade) angle point (storedTangent point)) 2) :=
  (PiLp.proj 2 (fun _ : Fin 3 => ℂ) 2 : PhysicalValue 3 →L[ℂ] ℂ).continuous.comp
    ((coefficientPhysicalValue_continuous admissible (fullGaugeFamily gauge)
      (fullGaugeFamily_coherent gauge coherent) grade angle).clm_apply storedTangent_continuous)

theorem fullGauge_third_scalar_continuous {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    (gauge : CoefficientFamily L sigma gamma ell 3 3) (coherent : FamilyCoherent gauge) (grade : ℕ) (angle : ℝ) :
    Continuous (fun point => (coefficientPhysicalValue (fullGaugeFamily gauge grade) angle point storedScalar) 2) :=
  (PiLp.proj 2 (fun _ : Fin 3 => ℂ) 2 : PhysicalValue 3 →L[ℂ] ℂ).continuous.comp
    ((coefficientPhysicalValue_continuous admissible (fullGaugeFamily gauge)
      (fullGaugeFamily_coherent gauge coherent) grade angle).clm_apply continuous_const)

end Grad.GaugeCoefficients.Physical.RadialLedger
