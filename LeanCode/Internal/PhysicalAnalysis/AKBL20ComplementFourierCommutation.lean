import AKBL19ExactRadialComplementWeight

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace
open Grad.GaugeCoefficients.Physical.RadialLedger

 theorem startupAngularCoefficient_clm {Source Target : Type*}
    [NormedAddCommGroup Source] [NormedSpace ℂ Source] [CompleteSpace Source]
    [NormedAddCommGroup Target] [NormedSpace ℂ Target] [CompleteSpace Target]
    (mapping : Source →L[ℂ] Target) (raw : ℝ → Source) (continuousRaw : Continuous raw) (cell : ℤ) :
    angularCoefficient (fun angle => mapping (raw angle)) cell = mapping (angularCoefficient raw cell) := by
  have integrable : IntervalIntegrable (fun angle : ℝ => fourier (-cell) (angle : CellCircle) • raw angle)
      volume (-Real.pi) Real.pi :=
    (((fourier (-cell)).continuous.comp (AddCircle.continuous_mk' _)).smul continuousRaw).intervalIntegrable _ _
  rw [angularCoefficient_integral,angularCoefficient_integral]
  change (2*Real.pi)⁻¹ • (∫ angle in -Real.pi..Real.pi, fourier (-cell) (angle : CellCircle) • mapping (raw angle)) =
    (mapping.restrictScalars ℝ) ((2*Real.pi)⁻¹ • (∫ angle in -Real.pi..Real.pi, fourier (-cell) (angle : CellCircle) • raw angle))
  rw [map_smul]
  congr 1
  change _ = mapping (∫ angle in -Real.pi..Real.pi, fourier (-cell) (angle : CellCircle) • raw angle)
  rw [← mapping.intervalIntegral_comp_comm integrable]
  apply intervalIntegral.integral_congr
  intro angle _
  exact (mapping.map_smul _ _).symm

 theorem startupAngularCoefficient_cmap_value {dimension : ℕ}
    (raw : ℝ → C(ClosedDisk,PhysicalValue dimension)) (continuousRaw : Continuous raw)
    (cell : ℤ) (point : ClosedDisk) :
    angularCoefficient (fun angle => raw angle point) cell = (angularCoefficient raw cell) point :=
  startupAngularCoefficient_clm (ContinuousMap.evalCLM ℂ point) raw continuousRaw cell

/-- Actual C0 commutes with the original axial Fourier coefficient on a
continuous closed realization. Punctured fields can use the SAME-circle
localization, without axis regularity or finite-cell truncation. -/
 theorem startupComplement_axialCoefficient (raw : ℝ → C(ClosedDisk,PhysicalValue 3))
    (continuousRaw : Continuous raw) (cell : ℤ) (point : ClosedDisk) :
    cartesianComplementValue (fun other => angularCoefficient (fun angle => raw angle other) cell) point =
      angularCoefficient (fun angle => cartesianComplementValue (raw angle) point) cell := by
  have same : (fun other => angularCoefficient (fun angle => raw angle other) cell) =
      (angularCoefficient raw cell) := funext (fun other => startupAngularCoefficient_cmap_value raw continuousRaw cell other)
  rw [same]
  have mapped := startupAngularCoefficient_clm cMapComplement raw continuousRaw cell
  have value := startupAngularCoefficient_cmap_value (fun angle => cMapComplement (raw angle))
    (cMapComplement.continuous.comp continuousRaw) cell point
  exact (congrArg (fun field : C(ClosedDisk,PhysicalValue 3) => field point) mapped).symm.trans value.symm

end Grad.CartesianStartup
