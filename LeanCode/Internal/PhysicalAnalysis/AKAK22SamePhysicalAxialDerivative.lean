import AKAK13ProjectedDeterminantRHS

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.ActualPolarEquations
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.SourceCollarFullSource
open Grad.SourceBoundaryTrace Grad.ActualSmoothPhysicalField Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularCurrentLow Grad.AnnularSmoothCore Grad.AnnularPhysicalFourier

/-- Exact Fourier coefficients give the actual axial derivative, with a
fixed scalar multiplier on the supplied slope representative. -/
theorem fullField_axialDerivative_of_coefficients {parameters : PhaseParameters}
    {lower : ℝ} {positive : 0 < lower} {row slope : DivisionRow 1 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row)
    (derivative : SmoothLowPhysicalRow parameters lower positive slope) (bounded : lower < 1)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (scalar : ℂ)
    (same : ∀ mode : ℤ × ℤ, scalar • derivative.physicalCurve 0 radius mode =
      (Complex.I * (mode.2 : ℂ)) • curves.physicalCurve 0 radius mode)
    (polar axial : ℝ) :
    HasDerivAt (fun angle => curves.fullField bounded (radius,polar,angle))
      (scalar • derivative.fullField bounded (radius,polar,axial)) axial := by
  let field := fun angles => curves.fullField bounded (radius,angles)
  have smooth := physicalField_angles_smooth curves bounded radius inside
  have angular : Function.Periodic field (2*Real.pi,0) := by
    rintro ⟨first,second⟩
    simpa only [field,Prod.mk_add_mk,add_zero] using curves.fullField_angular_shift bounded radius first second
  have cell : Function.Periodic field (0,2*Real.pi) := by
    rintro ⟨first,second⟩
    simpa only [field,Prod.mk_add_mk,add_zero] using curves.fullField_cell_shift bounded radius first second
  have equality : angularJet 1 field = fun angles => scalar • derivative.fullField bounded (radius,angles) := by
    have slopeContinuous : Continuous (fun angles => scalar • derivative.fullField bounded (radius,angles)) :=
      (physicalField_angles_smooth derivative bounded radius inside).continuous.const_smul scalar
    apply doubleFourier_ext (angularJet 1 field) (fun angles => scalar • derivative.fullField bounded (radius,angles))
      (angularJet_smooth 1 field smooth).continuous slopeContinuous
    · intro axial polar
      simpa only [Prod.mk_add_mk,add_zero] using axialAngleJet_periodic 1 field (2*Real.pi,0) angular (polar,axial)
    · intro axial polar
      change scalar • derivative.fullField bounded (radius,polar+2*Real.pi,axial) = scalar • derivative.fullField bounded (radius,polar,axial)
      rw [derivative.fullField_angular_shift bounded radius polar axial]
    · intro polar axial
      simpa only [Prod.mk_add_mk,add_zero] using axialAngleJet_periodic 1 field (0,2*Real.pi) cell (polar,axial)
    · intro polar axial
      change scalar • derivative.fullField bounded (radius,polar,axial+2*Real.pi) = scalar • derivative.fullField bounded (radius,polar,axial)
      rw [derivative.fullField_cell_shift bounded radius polar axial]
    · intro mode
      rw [← doubleCoefficient_swap (angularJet 1 field) (angularJet_smooth 1 field smooth).continuous]
      rw [← doubleCoefficient_swap (fun angles => scalar • derivative.fullField bounded (radius,angles))
        ((physicalField_angles_smooth derivative bounded radius inside).continuous.const_smul scalar)]
      change doubleCoefficient (angularJet 1 field) mode =
        doubleCoefficient (fun angles => scalar • derivative.fullField bounded (radius,angles)) mode
      rw [axialAngleJet_doubleCoefficient 1 field smooth cell,pow_one,
        doubleCoefficient_const_smul scalar _ (physicalField_angles_smooth derivative bounded radius inside).continuous,
        derivative.fullField_doubleCoefficient bounded radius inside mode,
        curves.fullField_doubleCoefficient bounded radius inside mode]
      exact (same mode).symm
  have law := angularJet_hasDerivAt 0 field smooth polar axial
  simpa only [angularJet_zero,zero_add,equality] using law

/-- The original almost-everywhere coefficient relation determines that
same axial derivative at every radius of the closed collar. -/
theorem samePhysical_scaledAxialDerivative {parameters : PhaseParameters}
    {lower : ℝ} {positive : 0 < lower} {row slope : DivisionRow 1 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row)
    (derivative : SmoothLowPhysicalRow parameters lower positive slope) (bounded : lower < 1)
    (scalar : ℝ → ℂ) (scalarContinuous : ContinuousOn scalar (Icc lower 1))
    (same : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      scalar radius • lowRhoPhysicalCoefficient parameters lower positive slope radius mode =
        (Complex.I * (mode.2 : ℂ)) • lowRhoPhysicalCoefficient parameters lower positive row radius mode)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (polar axial : ℝ) :
    HasDerivAt (fun angle => curves.fullField bounded (radius,polar,angle))
      (scalar radius • derivative.fullField bounded (radius,polar,axial)) axial := by
  apply fullField_axialDerivative_of_coefficients curves derivative bounded radius inside (scalar radius) _ polar axial
  intro mode
  apply collarCurve_eq_of_ae lower bounded
    (fun location => scalar location • derivative.physicalCurve 0 location mode)
    (fun location => (Complex.I * (mode.2 : ℂ)) • curves.physicalCurve 0 location mode)
    (scalarContinuous.smul ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).continuous.comp_continuousOn
      (derivative.physicalCurve_smooth bounded 0).continuousOn))
    (((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 mode).continuous.comp_continuousOn
      (curves.physicalCurve_smooth bounded 0).continuousOn).const_smul (Complex.I * (mode.2 : ℂ))) _ inside
  filter_upwards [derivative.physicalCurve_actual bounded 0,curves.physicalCurve_actual bounded 0,same]
    with location slopeSame curveSame law
  simpa only [slopeSame mode,curveSame mode,pow_zero,one_smul] using law mode

end Grad.ActualPolarEquations
