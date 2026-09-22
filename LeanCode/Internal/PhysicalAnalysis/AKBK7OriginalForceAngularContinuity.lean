import AKBK4LiteralForceCellAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.ActualCartesianWeakEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceBoundaryTrace Grad.BoundaryTrace
open Grad.SourceCollarCoefficients Grad.ActualCartesianEquations Grad.PDEBootstrap Grad.SourceCollarFullSource
open Grad.ActualCartesianDescent Grad.ActualSmoothPhysicalField Grad.SourceCollarDivision

/-- The actual derivative along a circle is jointly continuous in both
angles. This uses the genuine Cartesian derivative on the specified open domain. -/
theorem originalField_fderiv_circle_continuous {dimension : ℕ} (domain : Set Spatial)
    (openDomain : IsOpen domain) (field : Spatial × ℝ → ComplexEuclidean dimension)
    (smooth : ContDiffOn ℝ ∞ field (domain ×ˢ (univ : Set ℝ)))
    (radius : ℝ) (inside : ∀ angle, polarPlane (radius,angle) ∈ domain) :
    Continuous (fun angles : ℝ × ℝ => fderiv ℝ field (polarPlane (radius,angles.1),angles.2)) := by
  have derivative := ((contDiffOn_infty_iff_fderiv_of_isOpen (openDomain.prod isOpen_univ)).mp smooth).2
  exact derivative.continuousOn.comp_continuous
    ((polarPlane_smooth.continuous.comp (continuous_const.prodMk continuous_fst)).prodMk continuous_snd)
    (fun angles => ⟨inside angles.1,mem_univ _⟩)

theorem nativeLocalField_fderiv_circle_continuous {dimension : ℕ} {parameters : PhaseParameters}
    {lower : ℝ} {positive : 0 < lower} {row : DivisionRow dimension lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower < 1)
    (radius : ℝ) (inside : radius ∈ Ioo lower 1) :
    Continuous (fun angles : ℝ × ℝ => fderiv ℝ (curves.cartesianField bounded)
      (polarPlane (radius,angles.1),angles.2)) := by
  let domain : Set Spatial := {point | ‖point‖ ∈ Ioo lower 1}
  have openDomain : IsOpen domain := isOpen_Ioo.preimage continuous_norm
  apply originalField_fderiv_circle_continuous domain openDomain
  · intro point member
    exact (curves.cartesianField_smoothAt bounded point member.1).contDiffWithinAt
  · intro angle
    change ‖polarPlane (radius,angle)‖ ∈ Ioo lower 1
    simpa only [polarPlane_norm,abs_of_pos (positive.trans inside.1)] using inside

theorem planarGradientValue_continuous :
    Continuous (planarGradientValue : (Spatial × ℝ →L[ℝ] ComplexEuclidean 1) → ComplexEuclidean 3) := by
  unfold planarGradientValue
  apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)).comp
  apply continuous_pi
  intro coordinate
  fin_cases coordinate <;> dsimp <;> fun_prop

end Grad.ActualCartesianWeakEquations
