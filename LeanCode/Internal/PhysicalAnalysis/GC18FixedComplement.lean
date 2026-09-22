import GC18ComplementAlgebra
import GaugeSplittings
import PolarCoverage
import TangentialCore

noncomputable section

set_option maxHeartbeats 1400000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges

/-- The literal fixed complement projection C0=diag(T,Pi), in stored
planar-planar-toroidal coordinates on the original all-grade core. -/
def fixedComplementCore (parameters : PhaseParameters) : ACore parameters 3 →ₗ[ℂ] ACore parameters 3 :=
  (planarInclusionCore parameters).comp ((tangentialCore parameters).comp (planarPartCore parameters)) +
    (toroidalInclusionCore parameters).comp ((angularCore parameters 0).comp (toroidalPartCore parameters))

theorem fixedComplementCore_planar (parameters : PhaseParameters) (field : ACore parameters 3) :
    planarPartCore parameters (fixedComplementCore parameters field) =
      tangentialCore parameters (planarPartCore parameters field) := by
  change planarPartCore parameters (planarInclusionCore parameters (tangentialCore parameters (planarPartCore parameters field)) +
    toroidalInclusionCore parameters (angularCore parameters 0 (toroidalPartCore parameters field))) = _
  rw [map_add, planarPartCore_planarInclusionCore, planarPartCore_toroidalInclusionCore, add_zero]

theorem fixedComplementCore_toroidal (parameters : PhaseParameters) (field : ACore parameters 3) :
    toroidalPartCore parameters (fixedComplementCore parameters field) =
      angularCore parameters 0 (toroidalPartCore parameters field) := by
  change toroidalPartCore parameters (planarInclusionCore parameters (tangentialCore parameters (planarPartCore parameters field)) +
    toroidalInclusionCore parameters (angularCore parameters 0 (toroidalPartCore parameters field))) = _
  rw [map_add, toroidalPartCore_planarInclusionCore, toroidalPartCore_toroidalInclusionCore, zero_add]

theorem fixedComplementCore_idempotent (parameters : PhaseParameters) (field : ACore parameters 3) :
    fixedComplementCore parameters (fixedComplementCore parameters field) = fixedComplementCore parameters field := by
  change planarInclusionCore parameters (tangentialCore parameters (planarPartCore parameters (fixedComplementCore parameters field))) +
      toroidalInclusionCore parameters (angularCore parameters 0 (toroidalPartCore parameters (fixedComplementCore parameters field))) = _
  rw [fixedComplementCore_planar, fixedComplementCore_toroidal, tangentialCore_idempotent, angularCore_projection]
  rfl

theorem tangentialJet_pointwise (field : ClosedJet 2) (point : ClosedDisk) :
    (point.val 0 : ℂ) * (tangentialJet field).value point 0 +
      (point.val 1 : ℂ) * (tangentialJet field).value point 1 = 0 := by
  obtain ⟨angle, polar⟩ := closedPoint_has_polar_angle point
  have radial := tangentialJet_polar_radial_zero field ‖point.val‖
    (by rw [abs_norm]; exact point.property) angle
  rw [polar] at radial
  have coordinates := congrArg Subtype.val polar
  rw [polarClosedPoint_coordinates] at coordinates
  have first := congrArg (fun source : SpatialPlane => source 0) coordinates
  have second := congrArg (fun source : SpatialPlane => source 1) coordinates
  change ‖point.val‖ * Real.cos angle = point.val 0 at first
  change ‖point.val‖ * Real.sin angle = point.val 1 at second
  rw [← first, ← second, Complex.ofReal_mul, Complex.ofReal_mul]
  linear_combination (‖point.val‖ : ℂ) * radial

/-- Every actual C0 range value satisfies the tangency used in the adjugate
algebra, including the axis. V is the actual range, not this pointwise law. -/
theorem fixedComplementCore_pointwise (parameters : PhaseParameters) (field : ACore parameters 3)
    (cell : ℤ) (point : ClosedDisk) :
    PointwiseTangential point (((fixedComplementCore parameters field).val cell).value point) := by
  have equality := congrArg (fun core : ACore parameters 2 => (core.val cell).value point)
    (fixedComplementCore_planar parameters field)
  change ((valueMapCore planarPartMap parameters (fixedComplementCore parameters field)).val cell).value point =
    ((tangentialCore parameters (planarPartCore parameters field)).val cell).value point at equality
  rw [valueMapCore_apply, valueMapJet_value, tangentialCore_apply] at equality
  have first := congrArg (fun value : ComplexEuclidean 2 => value 0) equality
  have second := congrArg (fun value : ComplexEuclidean 2 => value 1) equality
  change (((fixedComplementCore parameters field).val cell).value point) 0 = _ at first
  change (((fixedComplementCore parameters field).val cell).value point) 1 = _ at second
  change (point.val 0 : ℂ) * (((fixedComplementCore parameters field).val cell).value point) 0 +
    (point.val 1 : ℂ) * (((fixedComplementCore parameters field).val cell).value point) 1 = 0
  rw [first, second]
  exact tangentialJet_pointwise _ point

/-- The smooth fixed complement is the actual range of C0. -/
def fixedComplementRange (parameters : PhaseParameters) : Submodule ℂ (ACore parameters 3) :=
  LinearMap.range (fixedComplementCore parameters)

theorem mem_fixedComplementRange_iff (parameters : PhaseParameters) (field : ACore parameters 3) :
    field ∈ fixedComplementRange parameters ↔ fixedComplementCore parameters field = field := by
  constructor
  · rintro ⟨source, rfl⟩
    exact fixedComplementCore_idempotent parameters source
  · intro fixed
    exact ⟨field, fixed⟩

/-- Immediate range consumer for the determinant algebra. This does not
yet assert that the displayed block action is the actual C0*C operator. -/
theorem adjugate_radialBlock_on_fixedComplement (parameters : PhaseParameters)
    (field : fixedComplementRange parameters) (cell : ℤ) (point : ClosedDisk)
    (mu eta nu delta : ℂ) :
    adjugateBlockValue mu eta nu delta point (radialBlockValue mu eta nu delta point ((field.val.val cell).value point)) =
      blockDeterminant mu eta nu delta point • (field.val.val cell).value point := by
  have fixed := (mem_fixedComplementRange_iff parameters field.val).mp field.property
  have tangential := fixedComplementCore_pointwise parameters field.val cell point
  rw [fixed] at tangential
  exact adjugate_radialBlock mu eta nu delta point _ tangential

end Grad.GaugeCoefficients.Physical.RadialLedger
