import GC18ActualRadialIdentities

noncomputable section

set_option maxHeartbeats 1000000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.GenericCarriers

/-- The literal block action after the AO9 reduction. This is not yet the
identification with C0*C; that remaining correspondence is a separate proof. -/
def radialBlockValue (mu eta nu delta : ℂ) (point : ClosedDisk) (value : PhysicalValue 3) : PhysicalValue 3 :=
  WithLp.toLp 2 ![mu * value 0 - eta * (point.val 1 : ℂ) * value 2,
    mu * value 1 + eta * (point.val 0 : ℂ) * value 2,
    nu * (-(point.val 1 : ℂ) * value 0 + (point.val 0 : ℂ) * value 1) + delta * value 2]

def adjugateBlockValue (mu eta nu delta : ℂ) (point : ClosedDisk) (value : PhysicalValue 3) : PhysicalValue 3 :=
  WithLp.toLp 2 ![delta * value 0 + eta * (point.val 1 : ℂ) * value 2,
    delta * value 1 - eta * (point.val 0 : ℂ) * value 2,
    -nu * (-(point.val 1 : ℂ) * value 0 + (point.val 0 : ℂ) * value 1) + mu * value 2]

def blockDeterminant (mu eta nu delta : ℂ) (point : ClosedDisk) : ℂ :=
  mu * delta - ((point.val 0 : ℂ) ^ 2 + (point.val 1 : ℂ) ^ 2) * eta * nu

/-- Pointwise tangency is a necessary complement condition, not a replacement
definition of V. Full equivariance and radiality remain in the C0*C linkage. -/
def PointwiseTangential (point : ClosedDisk) (value : PhysicalValue 3) : Prop :=
  (point.val 0 : ℂ) * value 0 + (point.val 1 : ℂ) * value 1 = 0

theorem radialBlockValue_tangential (mu eta nu delta : ℂ) (point : ClosedDisk) (value : PhysicalValue 3)
    (tangential : PointwiseTangential point value) :
    PointwiseTangential point (radialBlockValue mu eta nu delta point value) := by
  change (point.val 0 : ℂ) * (mu * value 0 - eta * (point.val 1 : ℂ) * value 2) +
    (point.val 1 : ℂ) * (mu * value 1 + eta * (point.val 0 : ℂ) * value 2) = 0
  change (point.val 0 : ℂ) * value 0 + (point.val 1 : ℂ) * value 1 = 0 at tangential
  linear_combination mu * tangential

theorem adjugateBlockValue_tangential (mu eta nu delta : ℂ) (point : ClosedDisk) (value : PhysicalValue 3)
    (tangential : PointwiseTangential point value) :
    PointwiseTangential point (adjugateBlockValue mu eta nu delta point value) := by
  change (point.val 0 : ℂ) * (delta * value 0 + eta * (point.val 1 : ℂ) * value 2) +
    (point.val 1 : ℂ) * (delta * value 1 - eta * (point.val 0 : ℂ) * value 2) = 0
  change (point.val 0 : ℂ) * value 0 + (point.val 1 : ℂ) * value 1 = 0 at tangential
  linear_combination delta * tangential

theorem adjugate_radialBlock (mu eta nu delta : ℂ) (point : ClosedDisk) (value : PhysicalValue 3)
    (tangential : PointwiseTangential point value) :
    adjugateBlockValue mu eta nu delta point (radialBlockValue mu eta nu delta point value) =
      blockDeterminant mu eta nu delta point • value := by
  apply PiLp.ext
  intro coordinate
  change (point.val 0 : ℂ) * value 0 + (point.val 1 : ℂ) * value 1 = 0 at tangential
  fin_cases coordinate
  · change delta * (mu * value 0 - eta * (point.val 1 : ℂ) * value 2) +
      eta * (point.val 1 : ℂ) * (nu * (-(point.val 1 : ℂ) * value 0 + (point.val 0 : ℂ) * value 1) + delta * value 2) =
      (mu * delta - ((point.val 0 : ℂ)^2 + (point.val 1 : ℂ)^2) * eta * nu) * value 0
    linear_combination eta * nu * (point.val 0 : ℂ) * tangential
  · change delta * (mu * value 1 + eta * (point.val 0 : ℂ) * value 2) -
      eta * (point.val 0 : ℂ) * (nu * (-(point.val 1 : ℂ) * value 0 + (point.val 0 : ℂ) * value 1) + delta * value 2) =
      (mu * delta - ((point.val 0 : ℂ)^2 + (point.val 1 : ℂ)^2) * eta * nu) * value 1
    linear_combination eta * nu * (point.val 1 : ℂ) * tangential
  · change -nu * (-(point.val 1 : ℂ) * (mu * value 0 - eta * (point.val 1 : ℂ) * value 2) +
        (point.val 0 : ℂ) * (mu * value 1 + eta * (point.val 0 : ℂ) * value 2)) +
      mu * (nu * (-(point.val 1 : ℂ) * value 0 + (point.val 0 : ℂ) * value 1) + delta * value 2) =
      (mu * delta - ((point.val 0 : ℂ)^2 + (point.val 1 : ℂ)^2) * eta * nu) * value 2
    ring

theorem radial_adjugateBlock (mu eta nu delta : ℂ) (point : ClosedDisk) (value : PhysicalValue 3)
    (tangential : PointwiseTangential point value) :
    radialBlockValue mu eta nu delta point (adjugateBlockValue mu eta nu delta point value) =
      blockDeterminant mu eta nu delta point • value := by
  have identity := adjugate_radialBlock delta (-eta) (-nu) mu point value tangential
  have determinant : blockDeterminant delta (-eta) (-nu) mu point =
      blockDeterminant mu eta nu delta point := by unfold blockDeterminant; ring
  rw [determinant] at identity
  simpa only [radialBlockValue, adjugateBlockValue, sub_eq_add_neg, neg_mul, neg_neg] using identity

end Grad.GaugeCoefficients.Physical.RadialLedger
