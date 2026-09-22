import WM1Kernel

noncomputable section

open MeasureTheory Grad.PDEBootstrap Grad.GenericCarriers
open Grad.WeakTesting
open scoped ContDiff

namespace Grad.Mollifier.WeakJets

universe valueUniverse

theorem translation_ae (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [InnerProductSpace ℂ Value] (offset : Spatial) (field : DomainL2 Value Set.univ) :
    Grad.SpatialTranslation.translation Value offset field =ᵐ[volume]
      fun point => field (point - offset) := by
  have represented :=
    Lp.coeFn_compMeasurePreserving field (Grad.SpatialTranslation.shift_univ_measurePreserving offset)
  change Grad.SpatialTranslation.translation Value offset field =ᵐ[volume.restrict Set.univ]
    (fun point => field (point - offset)) at represented
  simpa only [Measure.restrict_univ] using represented

theorem integral_translation_test (dimension : ℕ) (offset : Spatial)
    (field : FieldL2 dimension Set.univ) (cell : ℤ) (vector : PhysicalValue dimension)
    (test : Spatial → ℝ) :
    (∫ point : Spatial, test point •
      inner ℂ vector (Grad.SpatialTranslation.translation (CellValues dimension) offset field point cell)) =
      ∫ point : Spatial, test (point + offset) • inner ℂ vector (field point cell) := by
  calc
    _ = ∫ point : Spatial, test point • inner ℂ vector (field (point - offset) cell) := by
      apply integral_congr_ae
      filter_upwards [translation_ae (CellValues dimension) offset field] with point represented
      rw [represented]
    _ = _ := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self
          (fun point : Spatial => test point • inner ℂ vector (field (point - offset) cell)) offset).symm

theorem translationWeakGoal : TranslationWeakGoal := by
  intro dimension rank word field derivative weakDerivative offset cell vector test smoothness compactSupport _
  simp only [compactPairing_apply, Grad.WeakTesting.Commutation.signedDerivativePairing,
    smul_apply, orderedDerivativePairing_apply, smul_eq_mul, Measure.restrict_univ]
  rw [integral_translation_test, integral_translation_test]
  have identity := weakOrderedDerivative_integral dimension rank word field derivative weakDerivative
    cell vector (shiftedTest offset test) (shiftedTest_contDiff offset test smoothness)
      (shiftedTest_compactSupport offset test compactSupport)
  simp_rw [orderedTestDerivative_shifted] at identity
  exact identity

end Grad.Mollifier.WeakJets
