import AKBP5SameRadialConjugation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Radial Grad.GenericCarriers Grad.Constraints Grad.Constraints.Gauges
open Grad.ActualAngularInverse Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger

namespace StartupRadialRelated
variable {symbol : ℤ → Spatial → ℝ}
variable (radial : ∀ (cell : ℤ) (angle : ℝ) (point : Spatial), symbol cell (planeRotationEquiv angle point) = symbol cell point)

include radial in
theorem trueInverse {dimension : ℕ} {weighted original : StartupL2 dimension}
    (same : StartupRadialRelated symbol weighted original) (shift : ℤ) :
    StartupRadialRelated symbol (startupTrueAngularInverse dimension shift weighted)
      (startupTrueAngularInverse dimension shift original) := by
  change StartupRadialRelated symbol
    (startupPrimitiveKernel dimension shift (weighted-startupCharacterKernel dimension (-shift) weighted))
    (startupPrimitiveKernel dimension shift (original-startupCharacterKernel dimension (-shift) original))
  exact (same.sub (same.angular radial (angularCharacter (-shift)) (angularCharacter_smooth (-shift)))).angular
    radial (shiftPrimitiveKernel shift) (shiftPrimitiveKernel_smooth shift)

include radial in
theorem covector {weighted original : StartupL2 3} (same : StartupRadialRelated symbol weighted original)
    (weight : ℝ → ℂ) (smooth : ContDiff ℝ ∞ weight) (input output : Fin 2) :
    StartupRadialRelated symbol (startupCovectorAngularKernel weight smooth input output weighted)
      (startupCovectorAngularKernel weight smooth input output original) :=
  same.angular radial (startupCovectorWeight weight input output) (startupCovectorWeight_smooth weight smooth input output)

include radial in
theorem inverseTensor {weighted original : StartupL2 3} (same : StartupRadialRelated symbol weighted original)
    (input output : Fin 2) :
    StartupRadialRelated symbol (startupTrueInverseTensorKernel input output weighted)
      (startupTrueInverseTensorKernel input output original) := by
  simp only [startupTrueInverseTensorKernel,sub_apply,Fin.sum_univ_two]
  exact (same.covector radial (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) input output).sub
    (((same.covector radial (angularCharacter 0) (angularCharacter_smooth 0) input 0).covector
      radial (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) 0 output).add
      ((same.covector radial (angularCharacter 0) (angularCharacter_smooth 0) input 1).covector
        radial (shiftPrimitiveKernel 0) (shiftPrimitiveKernel_smooth 0) 1 output))

include radial in
/-- Both radial phase and cell moments commute with the entire literal fixed
ER tensor, including both inverse covectors and the resonant subtraction. -/
theorem principalFixed {weighted original : StartupL2 3} (same : StartupRadialRelated symbol weighted original)
    (outer inner : Fin 2) (row : Fin 3) :
    StartupRadialRelated symbol (startupPrincipalFixedKernel outer inner row weighted)
      (startupPrincipalFixedKernel outer inner row original) := by
  fin_cases row
  · change StartupRadialRelated symbol
      (originalValueKernel (startupPlanarRotatedEntryMap outer 1) (startupTrueInverseTensorKernel 0 inner weighted) -
        originalValueKernel (startupPlanarRotatedEntryMap outer 0) (startupTrueInverseTensorKernel 1 inner weighted))
      (originalValueKernel (startupPlanarRotatedEntryMap outer 1) (startupTrueInverseTensorKernel 0 inner original) -
        originalValueKernel (startupPlanarRotatedEntryMap outer 0) (startupTrueInverseTensorKernel 1 inner original))
    exact ((same.inverseTensor radial 0 inner).value (startupPlanarRotatedEntryMap outer 1)).sub
      ((same.inverseTensor radial 1 inner).value (startupPlanarRotatedEntryMap outer 0))
  · change StartupRadialRelated symbol
      ((if outer = inner then startupTrueAngularInverse 3 0 else 0) weighted)
      ((if outer = inner then startupTrueAngularInverse 3 0 else 0) original)
    by_cases equal : outer = inner
    · rw [if_pos equal]
      exact same.trueInverse radial 0
    · rw [if_neg equal]
      exact StartupRadialRelated.zero
  · change StartupRadialRelated symbol
      (originalValueKernel (startupPlanarEntryMap outer inner) weighted - (2 : ℂ) •
        ∑ middle : Fin 2, originalValueKernel (startupPlanarRotatedEntryMap outer middle)
          (startupTrueInverseTensorKernel middle inner weighted))
      (originalValueKernel (startupPlanarEntryMap outer inner) original - (2 : ℂ) •
        ∑ middle : Fin 2, originalValueKernel (startupPlanarRotatedEntryMap outer middle)
          (startupTrueInverseTensorKernel middle inner original))
    rw [Fin.sum_univ_two,Fin.sum_univ_two]
    exact (same.value (startupPlanarEntryMap outer inner)).sub
      ((((same.inverseTensor radial 0 inner).value (startupPlanarRotatedEntryMap outer 0)).add
        ((same.inverseTensor radial 1 inner).value (startupPlanarRotatedEntryMap outer 1))).smul 2)

include radial in
theorem principalRows (weighted original : Fin 3 → StartupL2 3)
    (same : ∀ row, StartupRadialRelated symbol (weighted row) (original row)) (outer inner : Fin 2) :
    StartupRadialRelated symbol
      (∑ row : Fin 3, startupPrincipalFixedKernel outer inner row (weighted row))
      (∑ row : Fin 3, startupPrincipalFixedKernel outer inner row (original row)) := by
  simp only [Fin.sum_univ_three]
  exact (((same 0).principalFixed radial outer inner 0).add
    ((same 1).principalFixed radial outer inner 1)).add ((same 2).principalFixed radial outer inner 2)

end StartupRadialRelated
end Grad.CartesianStartup
