import AKBL28SameRoughCurrentRecovery

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set MeasureTheory
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.BoundaryTrace
open Grad.Constraints Grad.Constraints.Gauges Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.ActualCartesianWeakEquations

 theorem startupClosedScalarMean_polar {dimension : ℕ} (raw : ClosedDisk → PhysicalValue dimension)
    (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    closedCharacterProjection 0 raw (Grad.Constraints.polarClosedPoint radius bounded angle) =
      angularCoefficient (fun polar => raw (Grad.Constraints.polarClosedPoint radius bounded polar)) 0 := by
  have periodic : Function.Periodic (fun polar => raw (Grad.Constraints.polarClosedPoint radius bounded polar)) (2*Real.pi) := by
    intro polar
    change raw (Grad.Constraints.polarClosedPoint radius bounded (polar+2*Real.pi)) = _
    rw [Grad.Constraints.polarClosedPoint_periodic]
  change closedCharacterProjection 0 raw (Grad.GaugeCoefficients.Radial.rotatedPoint angle (axisClosedPoint radius bounded)) = _
  rw [closedCharacterProjection_rotation,angularCharacter_zero_mode,one_smul,
    closedCharacterProjection_integral,originalAngularMean_interval _ periodic]
  simp only [angularCharacter_zero_mode,one_smul]
  rfl

 theorem startupClosedTangentialMean_fourier (raw : ClosedDisk → PhysicalValue 2)
    (continuousRaw : Continuous raw) (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    closedTangentialValue raw (Grad.Constraints.polarClosedPoint radius bounded angle) =
      angularCoefficient (fun polar => polarTangentialComponent polar
        (raw (Grad.Constraints.polarClosedPoint radius bounded polar))) 0 • polarTangentialVector angle := by
  have periodic : Function.Periodic (fun polar => polarTangentialComponent polar
      (raw (Grad.Constraints.polarClosedPoint radius bounded polar))) (2*Real.pi) := by
    intro polar
    change polarTangentialComponent (polar+2*Real.pi) (raw (Grad.Constraints.polarClosedPoint radius bounded (polar+2*Real.pi))) = _
    rw [(Grad.Constraints.polarClosedPoint_periodic radius bounded) polar]
    simp only [polarTangentialComponent,Real.cos_add_two_pi,Real.sin_add_two_pi]
  rw [closedTangentialValue_polar_formula raw continuousRaw,closedPolarTangentialMean_independent,
    originalAngularMean_interval _ periodic]
  simp only [closedPolarTangentialMean,add_zero]

/-- The two literal physical gauge means are exactly the two components
removed by C0. This uses the original centered Fourier normalization. -/
 theorem startupComplement_zero_of_gaugeMeans (raw : ClosedDisk → PhysicalValue 3)
    (continuousRaw : Continuous raw) (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ)
    (tangential : angularCoefficient (fun polar => polarTangentialComponent polar
      (planarPartMap (raw (Grad.Constraints.polarClosedPoint radius bounded polar)))) 0 = 0)
    (scalar : angularCoefficient (fun polar => toroidalPartMap
      (raw (Grad.Constraints.polarClosedPoint radius bounded polar))) 0 = 0) :
    cartesianComplementValue raw (Grad.Constraints.polarClosedPoint radius bounded angle) = 0 := by
  have planarContinuous : Continuous (fun other => planarPartMap (raw other)) := planarPartMap.continuous.comp continuousRaw
  rw [cartesianComplementValue,startupClosedTangentialMean_fourier (fun other => planarPartMap (raw other)) planarContinuous,
    startupClosedScalarMean_polar,tangential,scalar,zero_smul,map_zero,map_zero,add_zero]

end Grad.CartesianStartup
