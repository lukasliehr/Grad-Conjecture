import AKBA1ScalarOriginalWeightedRestriction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped ContDiff
namespace Grad.OriginalKernelGraphRestriction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.PhaseAlgebra
open Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction Grad.ActualSmoothPhysicalField
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularCurrentEnergy Grad.AnnularSmoothCore Grad.SourceCollarFullSource

variable (lower : ℝ) (positive : 0<lower)

theorem originalInverseRadiusCurve_bound (radius : ℝ) (_inside : radius ∈ Icc lower 1) :
    ‖annularInverseRadiusCurve lower positive radius‖≤lower⁻¹ := by
  change ‖1/max lower radius‖≤lower⁻¹
  rw [Real.norm_of_nonneg (by positivity),one_div]
  exact inv_anti₀ positive (le_max_left _ _)

def originalInverseRadiusRow : DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower :=
  complexLpTwoMap (fun _ => scalarRadialMap lower (annularInverseRadiusCurve lower positive) lower⁻¹
    (originalInverseRadiusCurve_bound lower positive)) lower⁻¹ (inv_nonneg.mpr positive.le)
    (fun _ field => scalarRadialMap_bound lower (annularInverseRadiusCurve lower positive) lower⁻¹
      (originalInverseRadiusCurve_bound lower positive) field)

theorem originalInverseRadiusRow_ae (row : DivisionRow 1 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      originalInverseRadiusRow lower positive row mode radius = (radius : ℂ)⁻¹ • row mode radius := by
  have coordinate (mode : ℤ × ℤ) := scalarRadialMap_ae lower (annularInverseRadiusCurve lower positive) lower⁻¹
    (originalInverseRadiusCurve_bound lower positive) (row mode)
  filter_upwards [ae_all_iff.mpr coordinate,ae_restrict_mem measurableSet_Icc] with radius same inside
  intro mode
  change scalarRadialMap lower (annularInverseRadiusCurve lower positive) lower⁻¹
    (originalInverseRadiusCurve_bound lower positive) (row mode) radius = _
  rw [same mode]
  change ((1/max lower radius : ℝ) : ℂ) • (row mode radius : ComplexEuclidean 1) = (radius : ℂ)⁻¹ • row mode radius
  rw [max_eq_right inside.1,one_div,Complex.ofReal_inv]

def originalInverseRadiusCurves {parameters : PhaseParameters} {row : DivisionRow 1 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) :
    SmoothLowPhysicalRow parameters lower positive (originalInverseRadiusRow lower positive row) where
  curve grade radius := (radius : ℂ)⁻¹ • curves.curve grade radius
  smooth grade := (reciprocalRadius_smooth lower positive).smul (curves.smooth grade)
  same grade := by
    filter_upwards [curves.same grade,originalInverseRadiusRow_ae lower positive row] with radius same divided
    intro mode
    change (radius : ℂ)⁻¹ • curves.curve grade radius mode = _
    rw [same mode]
    unfold lowRhoPhysicalCoefficient
    rw [divided mode]
    simp only [smul_smul]
    congr 1
    ring

theorem originalInverseRadiusCurves_fullField {parameters : PhaseParameters} {row : DivisionRow 1 lower}
    (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower<1)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angles : ℝ × ℝ) :
    (originalInverseRadiusCurves lower positive curves).fullField bounded (radius,angles) =
      (radius : ℂ)⁻¹ • curves.fullField bounded (radius,angles) := by
  apply congrFun ((originalInverseRadiusCurves lower positive curves).fullField_eq_of_doubleCoefficient bounded radius inside _
    ((curves.fullField_continuous_angles bounded radius inside).const_smul ((radius : ℂ)⁻¹))
    (fun axial polar => congrArg (((radius : ℂ)⁻¹) • ·) (curves.fullField_angular_periodic bounded radius axial polar))
    (fun polar axial => congrArg (((radius : ℂ)⁻¹) • ·) (curves.fullField_cell_periodic bounded radius polar axial)) _) angles
  intro mode
  have scalar : doubleCoefficient (fun angles => (radius : ℂ)⁻¹ • curves.fullField bounded (radius,angles)) mode =
      (radius : ℂ)⁻¹ • doubleCoefficient (fun angles => curves.fullField bounded (radius,angles)) mode := by
    exact doubleCoefficient_valueMap ((radius : ℂ)⁻¹ • ContinuousLinearMap.id ℂ (ComplexEuclidean 1)) _
      (curves.fullField_continuous_angles bounded radius inside) mode
  change doubleCoefficient (fun angles => (radius : ℂ)⁻¹ • curves.fullField bounded (radius,angles)) mode = _
  rw [scalar,curves.fullField_doubleCoefficient bounded radius inside mode,
    (originalInverseRadiusCurves lower positive curves).physicalCurve_coefficient bounded 0 radius inside mode,
    curves.physicalCurve_coefficient bounded 0 radius inside mode]
  change (radius : ℂ)⁻¹ • ((Real.exp (-radialPhase parameters radius mode.2) : ℂ) • curves.curve 0 radius mode) =
    (Real.exp (-radialPhase parameters radius mode.2) : ℂ) • ((radius : ℂ)⁻¹ • curves.curve 0 radius mode)
  exact smul_comm _ _ _

end Grad.OriginalKernelGraphRestriction
