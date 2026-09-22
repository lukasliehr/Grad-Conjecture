import AKBG3BoundedCovariantPrimitive

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.Constraints Grad.GaugeCoefficients.Radial

/-- Actual real coordinate matrix of J. -/
def startupQuarterEntry (target source : Fin 2) : ℝ :=
  if target = 0 then (if source = 0 then 0 else -1) else (if source = 0 then 1 else 0)

/-- The equivariant average has the exact R-J resonance. -/
theorem startupCovariantAverageTest_rotation (source target : Fin 2)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (point : Spatial) :
    startupCovariantAngularTest (fun _ : ℝ => 1) source target (startupRotationDerivative test) point =
      ∑ middle : Fin 2, startupQuarterEntry target middle *
        startupCovariantAngularTest (fun _ : ℝ => 1) source middle test point := by
  fin_cases source <;> fin_cases target <;>
    simp only [startupCovariantAngularTest_matrix, Fin.sum_univ_two, startupQuarterEntry]
  all_goals norm_num
  all_goals simp only [startupCosineTest_rotation test smooth point, startupSineTest_rotation test smooth point]

/-- Raw C(R-J)=I-A in compact-test form. Every equivariant mean term is
explicit; this is the needed first-order recovery without shifted inverses. -/
theorem startupCovariantPrimitiveTest_rotation (source target : Fin 2)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (point : Spatial) :
    startupCovariantAngularTest (fun angle : ℝ => angle) source target (startupRotationDerivative test) point =
      startupCovariantAngularTest (fun _ : ℝ => 1) source target test point +
        (∑ middle : Fin 2, startupQuarterEntry target middle *
          startupCovariantAngularTest (fun angle : ℝ => angle) source middle test point) -
        (if source = target then 1 else 0 : ℝ) * test point := by
  fin_cases source <;> fin_cases target <;>
    simp only [startupCovariantAngularTest_matrix, Fin.sum_univ_two, startupQuarterEntry]
  all_goals norm_num
  all_goals simp only [startupPrimitiveCosineTest_rotation test smooth point,
    startupPrimitiveSineTest_rotation test smooth point]
  all_goals ring

end Grad.CartesianStartup
