import GC18ScalarNormalization
import GC18ActualExtension

noncomputable section

set_option maxHeartbeats 1400000

open Set MeasureTheory
open scoped Topology BigOperators Interval

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Radial Grad.NonlinearDivision

def radiusScalar (point : ClosedDisk) : ℂ := ((‖point.val‖ ^ 2 : ℝ) : ℂ)

def storedTangent (point : ClosedDisk) : PhysicalValue 3 :=
  WithLp.toLp 2 ![-(point.val 1 : ℂ), (point.val 0 : ℂ), 0]

def storedScalar : PhysicalValue 3 := WithLp.toLp 2 ![0, 0, 1]

def storedTangentDot (point : ClosedDisk) (value : PhysicalValue 3) : ℂ :=
  -(point.val 1 : ℂ) * value 0 + (point.val 0 : ℂ) * value 1

def IsDiskRadial (field : ClosedDisk → ℂ) : Prop :=
  ∀ rotation point, field (Grad.GaugeCoefficients.Radial.rotatedPoint rotation point) = field point

theorem radiusScalar_rotation : IsDiskRadial radiusScalar := by
  intro rotation point
  simp only [radiusScalar, radialRotatedPoint_norm]

theorem closedAngularMean_radial (field : ClosedDisk → ℂ) : IsDiskRadial (closedAngularMean field) :=
  closedAngularMean_rotation field

theorem closedAngularMean_const {Target : Type} [NormedAddCommGroup Target] [NormedSpace ℝ Target] [CompleteSpace Target]
    (value : Target) (point : ClosedDisk) : closedAngularMean (fun _ => value) point = value := by
  rw [closedAngularMean, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const, sub_zero, one_smul]

theorem closedAngularMean_of_radial (field : ClosedDisk → ℂ) (radial : IsDiskRadial field)
    (point : ClosedDisk) : closedAngularMean field point = field point := by
  change ∀ rotation other, field (Grad.GaugeCoefficients.Radial.rotatedPoint rotation other) = field other at radial
  unfold closedAngularMean
  simp_rw [radial]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    intervalIntegral.integral_const, sub_zero, one_smul]

def complementProfile (first second : ClosedDisk → ℂ) (point : ClosedDisk) : PhysicalValue 3 :=
  first point • storedTangent point + second point • storedScalar

theorem storedTangentDot_profile (first second : ClosedDisk → ℂ) (point : ClosedDisk) :
    storedTangentDot point (complementProfile first second point) = radiusScalar point * first point := by
  simp only [storedTangentDot, complementProfile, storedTangent, storedScalar, PiLp.add_apply,
    PiLp.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, smul_eq_mul]
  rw [radiusScalar, EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
  push_cast
  ring

theorem complementProfile_third (first second : ClosedDisk → ℂ) (point : ClosedDisk) :
    complementProfile first second point 2 = second point := by
  simp [complementProfile, storedTangent, storedScalar]

/-- The pointwise polar evaluation formula for diag(T,Π). This definition
alone is not called the original normed V; its Cartesian-core correspondence
is proved separately before use as an operator realization. -/
def fixedComplementValue (field : ClosedDisk → PhysicalValue 3) (point : ClosedDisk) : PhysicalValue 3 :=
  complementProfile
    (fun point => (radiusScalar point)⁻¹ * closedAngularMean (fun other => storedTangentDot other (field other)) point)
    (closedAngularMean (fun point => field point 2)) point

theorem fixedComplementValue_profile_first_radial (field : ClosedDisk → PhysicalValue 3) :
    IsDiskRadial (fun point => (radiusScalar point)⁻¹ * closedAngularMean (fun other => storedTangentDot other (field other)) point) := by
  intro rotation point
  dsimp only
  rw [radiusScalar_rotation rotation point, closedAngularMean_rotation]

theorem radiusScalar_nonzero (point : ClosedDisk) (offAxis : point.val ≠ 0) : radiusScalar point ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr offAxis))

theorem fixedComplementValue_profile (first second : ClosedDisk → ℂ)
    (firstRadial : IsDiskRadial first) (secondRadial : IsDiskRadial second) (point : ClosedDisk) :
    fixedComplementValue (complementProfile first second) point = complementProfile first second point := by
  have productRadial : IsDiskRadial (fun point => radiusScalar point * first point) := by
    intro rotation other
    dsimp only
    rw [radiusScalar_rotation rotation other, firstRadial rotation other]
  unfold fixedComplementValue
  simp_rw [storedTangentDot_profile, complementProfile_third]
  have firstMean := closedAngularMean_of_radial _ productRadial point
  have secondMean := closedAngularMean_of_radial second secondRadial point
  change ((radiusScalar point)⁻¹ * closedAngularMean (fun other => radiusScalar other * first other) point) • storedTangent point +
    closedAngularMean second point • storedScalar = first point • storedTangent point + second point • storedScalar
  rw [firstMean, secondMean]
  by_cases axis : point.val = 0
  · have tangentZero : storedTangent point = 0 := by
      apply PiLp.ext
      intro row
      fin_cases row <;> simp [storedTangent, axis]
    rw [tangentZero, smul_zero, smul_zero]
  · rw [← mul_assoc, inv_mul_cancel₀ (radiusScalar_nonzero point axis), one_mul]

theorem fixedComplementValue_idempotent (field : ClosedDisk → PhysicalValue 3) (point : ClosedDisk) :
    fixedComplementValue (fixedComplementValue field) point = fixedComplementValue field point :=
  fixedComplementValue_profile _ _ (fixedComplementValue_profile_first_radial field)
    (closedAngularMean_radial _) point

/-- Physical pointwise range, kept distinct from the original scaled
Cartesian normed completion until its realization bridge is supplied. -/
def fixedComplementValueRange : Set (ClosedDisk → PhysicalValue 3) := Set.range fixedComplementValue

theorem mem_fixedComplementValueRange_iff (field : ClosedDisk → PhysicalValue 3) :
    field ∈ fixedComplementValueRange ↔ fixedComplementValue field = field := by
  constructor
  · rintro ⟨source, rfl⟩
    funext point
    exact fixedComplementValue_idempotent source point
  · intro fixed
    exact ⟨field, fixed⟩

end Grad.GaugeCoefficients.Physical.RadialLedger
