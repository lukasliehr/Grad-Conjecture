import AKAF1LiteralAngularFourierDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.ActualSmoothPhysicalField Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularCurrentLow Grad.AnnularSmoothCore Grad.AnnularPhysicalFourier

private theorem angularJet_periodic_translation {dimension : ℕ} (order : ℕ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (shift : ℝ × ℝ)
    (periodic : Function.Periodic field shift) : Function.Periodic (angularJet order field) shift := by
  intro point
  have same : (fun input : ℝ × ℝ => field (input + shift)) = field := funext periodic
  unfold angularJet
  rw [← iteratedFDeriv_comp_add_right order shift point,same]

theorem polarAngleJet_periodic {dimension : ℕ} (order : ℕ)
    (field : ℝ × ℝ → ComplexEuclidean dimension) (shift : ℝ × ℝ)
    (periodic : Function.Periodic field shift) : Function.Periodic (polarAngleJet order field) shift := by
  have swapped : Function.Periodic (field ∘ Prod.swap) shift.swap := by
    intro point
    simpa only [Function.comp_apply,Prod.swap_add,Prod.swap_swap] using periodic point.swap
  intro point
  simpa only [polarAngleJet,Function.comp_apply,Prod.swap_add] using
    angularJet_periodic_translation order _ shift.swap swapped point.swap

theorem physicalField_angles_smooth {dimension : ℕ} {parameters : PhaseParameters}
    {lower : ℝ} {positive : 0 < lower} {row : DivisionRow dimension lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower < 1)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    ContDiff ℝ ∞ (fun angles => curves.fullField bounded (radius,angles)) := by
  apply contDiffOn_univ.mp
  exact (curves.fullField_smooth bounded).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨inside,mem_univ _⟩)

/-- The genuine Fourier angular law determines the classical derivative of
these SAME smooth physical representatives, including the collar endpoints. -/
theorem samePhysical_angularDerivative {dimension : ℕ} {parameters : PhaseParameters}
    {lower : ℝ} {positive : 0 < lower} {row rotated : DivisionRow dimension lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row)
    (rotation : SmoothLowPhysicalRow parameters lower positive rotated) (bounded : lower < 1)
    (same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      lowRhoPhysicalCoefficient parameters lower positive rotated radius mode =
        (Complex.I * (mode.1 : ℂ)) • lowRhoPhysicalCoefficient parameters lower positive row radius mode)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) :
    HasDerivAt (fun angle => curves.fullField bounded (radius,angle,axial))
      (rotation.fullField bounded (radius,polar,axial)) polar := by
  let field := fun angles => curves.fullField bounded (radius,angles)
  have smooth := physicalField_angles_smooth curves bounded radius inside
  have angular : Function.Periodic field (2 * Real.pi,0) := by
    rintro ⟨first,second⟩
    simpa only [field,Prod.mk_add_mk,add_zero] using curves.fullField_angular_shift bounded radius first second
  have cell : Function.Periodic field (0,2 * Real.pi) := by
    rintro ⟨first,second⟩
    simpa only [field,Prod.mk_add_mk,add_zero] using curves.fullField_cell_shift bounded radius first second
  have coefficient (mode : ℤ × ℤ) : rotation.physicalCurve 0 radius mode =
      (Complex.I * (mode.1 : ℂ)) • curves.physicalCurve 0 radius mode := by
    apply collarCurve_eq_of_ae lower bounded
      (fun location => rotation.physicalCurve 0 location mode)
      (fun location => (Complex.I * (mode.1 : ℂ)) • curves.physicalCurve 0 location mode)
      ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).continuous.comp_continuousOn
        (rotation.physicalCurve_smooth bounded 0).continuousOn)
      ((show ContinuousOn (fun _ : ℝ => (Complex.I * (mode.1 : ℂ))) (Icc lower 1) from continuousOn_const).smul ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).continuous.comp_continuousOn
        (curves.physicalCurve_smooth bounded 0).continuousOn)) _ inside
    filter_upwards [rotation.physicalCurve_actual bounded 0,curves.physicalCurve_actual bounded 0,same]
      with location rotatedSame curveSame law
    simpa only [rotatedSame mode,curveSame mode,pow_zero,one_smul] using law mode
  have equality := rotation.fullField_eq_of_doubleCoefficient bounded radius inside (polarAngleJet 1 field)
    (polarAngleJet_smooth 1 field smooth).continuous
    (fun axial polar => by
      have law := polarAngleJet_periodic 1 field (2 * Real.pi,0) angular (polar,axial)
      simpa only [Prod.mk_add_mk,add_zero] using law)
    (fun polar axial => by
      have law := polarAngleJet_periodic 1 field (0,2 * Real.pi) cell (polar,axial)
      simpa only [Prod.mk_add_mk,add_zero] using law)
    (fun mode => by
      rw [polarAngleJet_doubleCoefficient 1 field smooth angular,pow_one]
      exact (congrArg ((Complex.I * (mode.1 : ℂ)) • ·)
        (curves.fullField_doubleCoefficient bounded radius inside mode)).trans (coefficient mode).symm)
  have derivative := polarAngleJet_hasDerivAt field smooth polar axial
  rw [← congrFun equality (polar,axial)] at derivative
  exact derivative

end Grad.ActualPolarEquations
