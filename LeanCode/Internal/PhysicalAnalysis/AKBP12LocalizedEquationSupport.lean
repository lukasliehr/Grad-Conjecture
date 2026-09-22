import AKBP11ActualTensorCutoffCommutation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
open Set MeasureTheory
open scoped ContDiff
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.WeightedJets Grad.WeightedJets.ZeroExtension

theorem startupSupported_add {support : Set Spatial} {first second : StartupL2 3}
    (one : SupportedField (CellValues 3) openUnitDisk support first)
    (two : SupportedField (CellValues 3) openUnitDisk support second) :
    SupportedField (CellValues 3) openUnitDisk support (first+second) := by
  filter_upwards [one,two,Lp.coeFn_add first second] with point one two same
  intro outside
  simp only [same,Pi.add_apply,one outside,two outside,add_zero]

theorem startupSupported_sub {support : Set Spatial} {first second : StartupL2 3}
    (one : SupportedField (CellValues 3) openUnitDisk support first)
    (two : SupportedField (CellValues 3) openUnitDisk support second) :
    SupportedField (CellValues 3) openUnitDisk support (first-second) := by
  filter_upwards [one,two,Lp.coeFn_sub first second] with point one two same
  intro outside
  simp only [same,Pi.sub_apply,one outside,two outside,sub_zero]

theorem startupSupported_smul {support : Set Spatial} {field : StartupL2 3}
    (same : SupportedField (CellValues 3) openUnitDisk support field) (constant : ℂ) :
    SupportedField (CellValues 3) openUnitDisk support (constant • field) := by
  filter_upwards [same,Lp.coeFn_smul constant field] with point same represented
  intro outside
  simp only [represented,Pi.smul_apply,same outside,smul_zero]

theorem startupSupported_sumTwo {support : Set Spatial} (field : Fin 2 → StartupL2 3)
    (same : ∀ index, SupportedField (CellValues 3) openUnitDisk support (field index)) :
    SupportedField (CellValues 3) openUnitDisk support (∑ index, field index) := by
  rw [Fin.sum_univ_two]
  exact startupSupported_add (same 0) (same 1)

theorem startupCutoffL2_supported (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff)
    (compact : HasCompactSupport cutoff) (support : Set Spatial) (included : tsupport cutoff ⊆ support)
    (field : StartupL2 3) :
    SupportedField (CellValues 3) openUnitDisk support (startupCutoffL2 cutoff smooth compact field) := by
  filter_upwards [startupCutoffL2_ae cutoff smooth compact field] with point same
  intro outside
  apply lp.ext
  funext cell
  change startupCutoffL2 cutoff smooth compact field point cell = 0
  rw [same cell,image_eq_zero_of_notMem_tsupport (fun inside => outside (included inside))]
  simp only [Complex.ofReal_zero,zero_smul]

theorem startupCutoffDerivative_supported (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff)
    (compact : HasCompactSupport cutoff) (field : StartupL2 3) (direction : Fin 2) :
    SupportedField (CellValues 3) openUnitDisk (tsupport cutoff) (startupCutoffDerivative cutoff smooth compact direction field) :=
  startupCutoffL2_supported _ _ _ _ (startupTestDerivative_supported cutoff direction) field

theorem startupCutoffSecondDerivative_supported (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff)
    (compact : HasCompactSupport cutoff) (field : StartupL2 3) (outer inner : Fin 2) :
    SupportedField (CellValues 3) openUnitDisk (tsupport cutoff) (startupCutoffSecondDerivative cutoff smooth compact outer inner field) :=
  startupCutoffL2_supported _ _ _ _ ((startupTestDerivative_supported _ outer).trans
    (startupTestDerivative_supported cutoff inner)) field

/-- The SAME localized unknown, tensor, zeroth term and every flux have one
actual compact support; this is the precise whole-plane test-extension input. -/
theorem startupCutoffEquation_supported (cutoff : Spatial → ℝ) (smooth : ContDiff ℝ ∞ cutoff)
    (compact : HasCompactSupport cutoff) (field zeroth : StartupL2 3)
    (tensor : Fin 2 → Fin 2 → StartupL2 3) (flux : Fin 2 → StartupL2 3) :
    SupportedField (CellValues 3) openUnitDisk (tsupport cutoff) (startupCutoffL2 cutoff smooth compact field) ∧
    SupportedField (CellValues 3) openUnitDisk (tsupport cutoff) (startupCutoffEquationZeroth cutoff smooth compact field zeroth tensor flux) ∧
    (∀ outer inner, SupportedField (CellValues 3) openUnitDisk (tsupport cutoff)
      (startupCutoffL2 cutoff smooth compact (tensor outer inner))) ∧
    (∀ direction, SupportedField (CellValues 3) openUnitDisk (tsupport cutoff)
      (startupCutoffEquationFlux cutoff smooth compact field tensor flux direction)) := by
  refine ⟨startupCutoffL2_supported cutoff smooth compact _ Subset.rfl field,?_,
    (fun outer inner => startupCutoffL2_supported cutoff smooth compact _ Subset.rfl (tensor outer inner)),?_⟩
  · apply startupSupported_sub
    · apply startupSupported_add
      · apply startupSupported_add
        · exact startupCutoffL2_supported cutoff smooth compact _ Subset.rfl zeroth
        · apply startupSupported_sumTwo
          intro outer
          apply startupSupported_sumTwo
          intro inner
          exact startupCutoffSecondDerivative_supported cutoff smooth compact (tensor outer inner) outer inner
      · apply startupSupported_sumTwo
        intro direction
        exact startupCutoffDerivative_supported cutoff smooth compact (flux direction) direction
    · apply startupSupported_sumTwo
      intro direction
      exact startupCutoffSecondDerivative_supported cutoff smooth compact field direction direction
  · intro direction
    apply startupSupported_sub
    · apply startupSupported_add
      · apply startupSupported_add
        · exact startupCutoffL2_supported cutoff smooth compact _ Subset.rfl (flux direction)
        · apply startupSupported_sumTwo
          intro inner
          exact startupCutoffDerivative_supported cutoff smooth compact (tensor direction inner) inner
      · apply startupSupported_sumTwo
        intro outer
        exact startupCutoffDerivative_supported cutoff smooth compact (tensor outer direction) outer
    · exact startupSupported_smul (startupCutoffDerivative_supported cutoff smooth compact field direction) 2

end Grad.CartesianStartup
