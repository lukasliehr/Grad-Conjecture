import AKBL21SameCircleJointLocalization

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- Exact axial Fourier/C0 commutation on the actual punctured domain.
Only joint continuity there is used; the axis is never assigned smooth data. -/
theorem startupComplement_punctured_axialCoefficient
    (raw : ℝ × Spatial → PhysicalValue 3)
    (continuousRaw : ContinuousOn raw {pair | pair.2 ∈ openUnitDisk \ {(0 : Spatial)}})
    (cell : ℤ) (point : ClosedDisk) (positive : 0 < ‖point.val‖) (inside : ‖point.val‖ < 1) :
    cartesianComplementValue (fun other => angularCoefficient (fun angle => raw (angle,other.val)) cell) point =
      angularCoefficient (fun angle => cartesianComplementValue (fun other : ClosedDisk => raw (angle,other.val)) point) cell := by
  obtain ⟨localized,continuousLocal,same⟩ := startupJointCircle_continuousLocalization raw continuousRaw point.val positive inside
  have coefficientSame : cartesianComplementValue (fun other => angularCoefficient (fun angle => raw (angle,other.val)) cell) point =
      cartesianComplementValue (fun other => angularCoefficient (fun angle => localized angle other) cell) point := by
    apply startupComplement_norm_locality
    intro other normSame
    exact congrArg (fun function : ℝ → PhysicalValue 3 => angularCoefficient function cell)
      (funext (fun angle => (same angle other normSame).symm))
  have pointSame (angle : ℝ) :
      cartesianComplementValue (fun other : ClosedDisk => raw (angle,other.val)) point =
        cartesianComplementValue (localized angle) point :=
    startupComplement_norm_locality _ _ point (fun other normSame => (same angle other normSame).symm)
  rw [coefficientSame,startupComplement_axialCoefficient localized continuousLocal]
  exact congrArg (fun function : ℝ → PhysicalValue 3 => angularCoefficient function cell) (funext (fun angle => (pointSame angle).symm))

end Grad.CartesianStartup
