import AKBE7ActualObservedCartesianEquations
import GC18PolarMean

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped Interval ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.SourceCollarFullSource Grad.BoundaryTrace

/-- The original nonsingular Cartesian radial mean removal, with its actual
quarter-turn signs. -/
def closedOriginalRadialProjection (field : ClosedDisk → ComplexEuclidean 2) (point : ClosedDisk) : ComplexEuclidean 2 :=
  field point + quarterValueMap (closedTangentialValue (fun other => quarterValueMap (field other)) point)

private theorem quarter_tangential (angle : ℝ) :
    quarterValueMap (polarTangentialVector angle) = -polarRadialVector angle := by
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [quarterValueMap,quarterValueLinear,polarTangentialVector,polarRadialVector]

/-- Reuse the actual tangential polar formula to identify I+JTJ with radial
mean removal; no unproved projector correspondence is assumed. -/
theorem closedOriginalRadialProjection_polar (field : ClosedDisk → ComplexEuclidean 2)
    (continuousField : Continuous field) (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    closedOriginalRadialProjection field (Grad.Constraints.polarClosedPoint radius bounded angle) =
      field (Grad.Constraints.polarClosedPoint radius bounded angle) -
        ((2*Real.pi)⁻¹ • ∫ polar in (0 : ℝ)..2*Real.pi,
          polarRadialComponent polar (field (Grad.Constraints.polarClosedPoint radius bounded polar))) •
          polarRadialVector angle := by
  unfold closedOriginalRadialProjection
  rw [closedTangentialValue_polar_formula (fun other => quarterValueMap (field other)) (by fun_prop) radius bounded angle,
    closedPolarTangentialMean_independent, map_smul, quarter_tangential, smul_neg, ← sub_eq_add_neg]
  congr 2
  unfold closedPolarTangentialMean
  simp only [add_zero]
  congr 1
  apply intervalIntegral.integral_congr
  intro polar _
  simp [polarTangentialComponent,polarRadialComponent,quarterValueMap,quarterValueLinear]
  ring

/-- The two full-period conventions have the same actual angular mean. -/
theorem originalAngularMean_interval {Value : Type} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (field : ℝ → Value) (periodic : Function.Periodic field (2*Real.pi)) :
    angularCoefficient field 0 = (2*Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2*Real.pi,field angle := by
  rw [angularCoefficient_compact_general]
  simp only [neg_zero,cellExponential,Int.cast_zero,mul_zero,zero_mul,Complex.exp_zero,one_smul]
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le (by linarith [Real.pi_pos] : -Real.pi ≤ Real.pi)]
  congr 1
  have shifted := periodic.intervalIntegral_add_eq (-Real.pi) 0
  simpa only [show -Real.pi+(2*Real.pi)=Real.pi by ring,zero_add] using shifted

/-- Exact coefficient convention in the radial mean; the centered Fourier
integral and the nonsingular Cartesian projector act on the same circle. -/
theorem closedOriginalRadialProjection_fourier (field : ClosedDisk → ComplexEuclidean 2)
    (continuousField : Continuous field) (radius : ℝ) (bounded : |radius| ≤ 1) (angle : ℝ) :
    closedOriginalRadialProjection field (Grad.Constraints.polarClosedPoint radius bounded angle) =
      field (Grad.Constraints.polarClosedPoint radius bounded angle) -
        angularCoefficient (fun polar => polarRadialComponent polar
          (field (Grad.Constraints.polarClosedPoint radius bounded polar))) 0 • polarRadialVector angle := by
  have periodic : Function.Periodic (fun polar => polarRadialComponent polar
      (field (Grad.Constraints.polarClosedPoint radius bounded polar))) (2*Real.pi) := by
    intro polar
    simp only [polarClosedPoint_periodic radius bounded polar,polarRadialComponent,Real.cos_add_two_pi,Real.sin_add_two_pi]
  rw [originalAngularMean_interval _ periodic]
  exact closedOriginalRadialProjection_polar field continuousField radius bounded angle

end Grad.ActualCartesianWeakEquations
