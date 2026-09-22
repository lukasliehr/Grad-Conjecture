import GC18MeanProducts

noncomputable section

set_option maxHeartbeats 1400000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers Grad.Constraints

theorem IsDiskRadial.add {first second : ClosedDisk → ℂ}
    (firstRadial : IsDiskRadial first) (secondRadial : IsDiskRadial second) :
    IsDiskRadial (fun point => first point + second point) := by
  intro rotation point
  dsimp only
  rw [firstRadial rotation point, secondRadial rotation point]

theorem IsDiskRadial.mul {first second : ClosedDisk → ℂ}
    (firstRadial : IsDiskRadial first) (secondRadial : IsDiskRadial second) :
    IsDiskRadial (fun point => first point * second point) := by
  intro rotation point
  dsimp only
  rw [firstRadial rotation point, secondRadial rotation point]

theorem IsDiskRadial.sub {first second : ClosedDisk → ℂ}
    (firstRadial : IsDiskRadial first) (secondRadial : IsDiskRadial second) :
    IsDiskRadial (fun point => first point - second point) := by
  intro rotation point
  dsimp only
  rw [firstRadial rotation point, secondRadial rotation point]

theorem IsDiskRadial.neg {field : ClosedDisk → ℂ} (radial : IsDiskRadial field) :
    IsDiskRadial (fun point => -field point) := by
  intro rotation point
  dsimp only
  rw [radial rotation point]

theorem radialBlockValue_profile (mu eta nu delta : ℂ) (first second : ClosedDisk → ℂ) (point : ClosedDisk) :
    radialBlockValue mu eta nu delta point (complementProfile first second point) =
      complementProfile (fun other => mu * first other + eta * second other)
        (fun other => nu * radiusScalar other * first other + delta * second other) point := by
  apply PiLp.ext
  intro row
  fin_cases row
  · simp [radialBlockValue, complementProfile, storedTangent, storedScalar]
    ring
  · simp [radialBlockValue, complementProfile, storedTangent, storedScalar]
    ring
  · simp [radialBlockValue, complementProfile, storedTangent, storedScalar, radiusScalar,
      EuclideanSpace.real_norm_sq_eq, Fin.sum_univ_two]
    ring

theorem adjugateBlockValue_profile (mu eta nu delta : ℂ) (first second : ClosedDisk → ℂ) (point : ClosedDisk) :
    adjugateBlockValue mu eta nu delta point (complementProfile first second point) =
      complementProfile (fun other => delta * first other - eta * second other)
        (fun other => -nu * radiusScalar other * first other + mu * second other) point := by
  have identity := radialBlockValue_profile delta (-eta) (-nu) mu first second point
  simpa only [radialBlockValue, adjugateBlockValue, neg_mul, sub_eq_add_neg, neg_neg] using identity

theorem complementProfile_smul (scalar : ℂ) (first second : ClosedDisk → ℂ) (point : ClosedDisk) :
    scalar • complementProfile first second point =
      complementProfile (fun other => scalar * first other) (fun other => scalar * second other) point := by
  simp only [complementProfile, smul_add, smul_smul]

/-- A radial profile lies in the actual nonsingular Cartesian physical
range whenever it is a continuous physical field. -/
theorem radialProfile_cartesian_fixed (first second : ClosedDisk → ℂ)
    (firstRadial : IsDiskRadial first) (secondRadial : IsDiskRadial second)
    (continuous : Continuous (complementProfile first second)) (point : ClosedDisk) :
    cartesianComplementValue (complementProfile first second) point = complementProfile first second point := by
  rw [cartesianComplementValue_eq_polar _ continuous, fixedComplementValue_profile first second firstRadial secondRadial]

end Grad.GaugeCoefficients.Physical.RadialLedger
