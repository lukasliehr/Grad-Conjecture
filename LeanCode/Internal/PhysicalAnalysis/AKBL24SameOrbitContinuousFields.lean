import AKBL23SameWeightedComplementField

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- A local continuous realization of each entire circle and its axial
family. This property is proved from the original punctured continuity. -/
def StartupOrbitContinuous {dimension : ℕ} (raw : ℝ × Spatial → PhysicalValue dimension) : Prop :=
  ∀ point : Spatial, 0 < ‖point‖ → ‖point‖ < 1 →
    ∃ localized : ℝ → C(ClosedDisk,PhysicalValue dimension), Continuous localized ∧
      ∀ angle (other : ClosedDisk), ‖other.val‖ = ‖point‖ → localized angle other = raw (angle,other.val)

 theorem startupOrbitContinuous_of_punctured {dimension : ℕ} (raw : ℝ × Spatial → PhysicalValue dimension)
    (continuousRaw : ContinuousOn raw {pair | pair.2 ∈ openUnitDisk \ {(0 : Spatial)}}) :
    StartupOrbitContinuous raw := startupJointCircle_continuousLocalization raw continuousRaw

 theorem StartupOrbitContinuous.axial {dimension : ℕ} {raw : ℝ × Spatial → PhysicalValue dimension}
    (regular : StartupOrbitContinuous raw) (point : ClosedDisk) (positive : 0 < ‖point.val‖) (inside : ‖point.val‖ < 1) :
    Continuous (fun angle => raw (angle,point.val)) := by
  obtain ⟨localized,continuousLocal,same⟩ := regular point.val positive inside
  have equality : (fun angle => raw (angle,point.val)) = fun angle => localized angle point :=
    funext (fun angle => (same angle point rfl).symm)
  rw [equality]
  exact (ContinuousMap.evalCLM ℂ point).continuous.comp continuousLocal

 def startupRawComplement (raw : ℝ × Spatial → PhysicalValue 3) (pair : ℝ × Spatial) : PhysicalValue 3 :=
  closedFieldExtension (cartesianComplementValue (fun other : ClosedDisk => raw (pair.1,other.val))) pair.2

 theorem startupRawComplement_value (raw : ℝ × Spatial → PhysicalValue 3) (angle : ℝ) (point : ClosedDisk) :
    startupRawComplement raw (angle,point.val) = cartesianComplementValue (fun other : ClosedDisk => raw (angle,other.val)) point :=
  closedFieldExtension_value _ point

/-- The genuine C0 action preserves this exact local realization property;
there is no new regularity assumption on its output. -/
 theorem StartupOrbitContinuous.complement {raw : ℝ × Spatial → PhysicalValue 3}
    (regular : StartupOrbitContinuous raw) : StartupOrbitContinuous (startupRawComplement raw) := by
  intro point positive inside
  obtain ⟨localized,continuousLocal,same⟩ := regular point positive inside
  refine ⟨fun angle => cMapComplement (localized angle),cMapComplement.continuous.comp continuousLocal,?_⟩
  intro angle other normSame
  rw [startupRawComplement_value]
  change cartesianComplementValue (localized angle) other = _
  apply startupComplement_norm_locality
  intro query sameQuery
  exact same angle query (sameQuery.trans normSame)

/-- C0/Fourier commutation needs only the proved SAME-circle realization,
so it remains applicable after matrix and C0 compositions. -/
 theorem StartupOrbitContinuous.complement_fourier {raw : ℝ × Spatial → PhysicalValue 3}
    (regular : StartupOrbitContinuous raw) (cell : ℤ) (point : ClosedDisk)
    (positive : 0 < ‖point.val‖) (inside : ‖point.val‖ < 1) :
    cartesianComplementValue (fun other => angularCoefficient (fun angle => raw (angle,other.val)) cell) point =
      angularCoefficient (fun angle => startupRawComplement raw (angle,point.val)) cell := by
  obtain ⟨localized,continuousLocal,same⟩ := regular point.val positive inside
  have coefficientSame : cartesianComplementValue (fun other => angularCoefficient (fun angle => raw (angle,other.val)) cell) point =
      cartesianComplementValue (fun other => angularCoefficient (fun angle => localized angle other) cell) point := by
    apply startupComplement_norm_locality
    intro other normSame
    exact congrArg (fun function : ℝ → PhysicalValue 3 => angularCoefficient function cell)
      (funext (fun angle => (same angle other normSame).symm))
  rw [coefficientSame,startupComplement_axialCoefficient localized continuousLocal]
  apply congrArg (fun function : ℝ → PhysicalValue 3 => angularCoefficient function cell)
  funext angle
  rw [startupRawComplement_value]
  exact startupComplement_norm_locality _ _ point (fun other normSame => same angle other normSame)

end Grad.CartesianStartup
