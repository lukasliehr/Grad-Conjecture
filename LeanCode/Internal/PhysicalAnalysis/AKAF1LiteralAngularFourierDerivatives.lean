import AKAC30SameActualPhysicalRecoveryConsumer
import BT11AngularJets

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.ActualSmoothPhysicalField Grad.SourceCollarDivision

/-- The genuine polar derivative, using the existing directional jet calculus
with the two physical angle coordinates interchanged explicitly. -/
def polarAngleJet {dimension : ℕ} (order : ℕ) (field : ℝ × ℝ → ComplexEuclidean dimension) :
    ℝ × ℝ → ComplexEuclidean dimension := (angularJet order (field ∘ Prod.swap)) ∘ Prod.swap

theorem polarAngleJet_smooth {dimension : ℕ} (order : ℕ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field) :
    ContDiff ℝ ∞ (polarAngleJet order field) :=
  (angularJet_smooth order _ (smooth.comp (contDiff_snd.prodMk contDiff_fst))).comp (contDiff_snd.prodMk contDiff_fst)

theorem polarAngleJet_hasDerivAt {dimension : ℕ}
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (polar axial : ℝ) :
    HasDerivAt (fun angle => field (angle,axial)) (polarAngleJet 1 field (polar,axial)) polar := by
  simpa only [polarAngleJet,Function.comp_apply,Prod.swap_prod_mk,angularJet_zero,zero_add] using
    angularJet_hasDerivAt 0 (field ∘ Prod.swap) (smooth.comp (contDiff_snd.prodMk contDiff_fst)) axial polar

theorem polarAngleJet_doubleCoefficient {dimension : ℕ} (order : ℕ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (smooth : ContDiff ℝ ∞ field)
    (periodic : Function.Periodic field (2 * Real.pi,0)) (mode : ℤ × ℤ) :
    doubleCoefficient (polarAngleJet order field) mode =
      (Complex.I * (mode.1 : ℂ)) ^ order • doubleCoefficient field mode := by
  have swapped : Function.Periodic (field ∘ Prod.swap) (0,2 * Real.pi) := by
    intro point
    simpa only [Function.comp_apply,Prod.swap_add,Prod.swap_prod_mk] using periodic point.swap
  have inner (axial : ℝ) : angularCoefficient (fun polar => polarAngleJet order field (polar,axial)) mode.1 =
      (Complex.I * (mode.1 : ℂ)) ^ order • angularCoefficient (fun polar => field (polar,axial)) mode.1 := by
    simpa only [polarAngleJet,Function.comp_apply,Prod.swap_prod_mk] using
      angularCoefficient_angularJet order (field ∘ Prod.swap) (smooth.comp (contDiff_snd.prodMk contDiff_fst)) swapped axial mode.1
  rw [doubleCoefficient,doubleCoefficient_swap _ (polarAngleJet_smooth order field smooth).continuous]
  simp_rw [inner]
  change angularCoefficient (((Complex.I * (mode.1 : ℂ)) ^ order) •
    (fun axial => angularCoefficient (fun polar => field (polar,axial)) mode.1)) mode.2 = _
  rw [angularCoefficient_smul_continuous,← doubleCoefficient_swap field smooth.continuous]
  rfl

end Grad.ActualPolarEquations
