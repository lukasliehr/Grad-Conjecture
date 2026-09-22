import AKBD23SameCartesianRotationDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Set Filter
open scoped Topology ContDiff
namespace Grad.ActualDeterminantEquations
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.ActualSmoothPhysicalField
open Grad.ActualCartesianEquations Grad.ActualCartesianDescent Grad.PhysicalFamily Grad.BoundaryTrace

private theorem determinantCartesianBasis (angle : ℝ) :
    (spatialBasis 0,(0 : ℝ)) = Real.cos angle • (radialDirection angle,(0 : ℝ)) -
      Real.sin angle • (planeQuarterTurn (radialDirection angle),(0 : ℝ)) ∧
    (spatialBasis 1,(0 : ℝ)) = Real.sin angle • (radialDirection angle,(0 : ℝ)) +
      Real.cos angle • (planeQuarterTurn (radialDirection angle),(0 : ℝ)) := by
  constructor <;> apply Prod.ext
  · apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [spatialBasis,radialDirection,collarPlane,planeQuarterTurn]
    all_goals nlinarith [Real.cos_sq_add_sin_sq angle]
  · simp
  · apply PiLp.ext
    intro coordinate
    fin_cases coordinate <;> simp [spatialBasis,radialDirection,collarPlane,planeQuarterTurn]
    all_goals nlinarith [Real.cos_sq_add_sin_sq angle]
  · simp

/-- Exact L,L,1 divergence identity for a genuine Frechet derivative and
its three polar derivatives. No differentiability at the axis is used. -/
theorem determinantDivergence_polar_algebra (length radius angle : ℝ) (lengthNonzero : length ≠ 0) (radiusNonzero : radius ≠ 0)
    (derivative : SpatialPlane × ℝ →L[ℝ] ComplexEuclidean 3)
    (value radial angular axial : ComplexEuclidean 3)
    (radialSame : derivative (radialDirection angle,0) = cartesianCovariantValue angle radial)
    (angularSame : derivative (radius • planeQuarterTurn (radialDirection angle),0) = cartesianCovariantValue angle (angular+polarQuarter value))
    (axialSame : derivative (0,1) = cartesianCovariantValue angle axial) :
    (length : ℂ)*(derivative (spatialBasis 0,0) 0+derivative (spatialBasis 1,0) 1)+derivative (0,1) 2 =
      (length : ℂ)*(radial 0+value 0/(radius : ℂ)+angular 1/(radius : ℂ)+axial 2/(length : ℂ)) := by
  have angularPair : (radius • planeQuarterTurn (radialDirection angle),(0 : ℝ)) =
      radius • (planeQuarterTurn (radialDirection angle),(0 : ℝ)) := by simp
  rw [angularPair,map_smul] at angularSame
  have unscaled : derivative (planeQuarterTurn (radialDirection angle),0) =
      radius⁻¹ • cartesianCovariantValue angle (angular+polarQuarter value) := by
    rw [← angularSame,smul_smul,inv_mul_cancel₀ radiusNonzero,one_smul]
  have first := congrArg derivative (determinantCartesianBasis angle).1
  have second := congrArg derivative (determinantCartesianBasis angle).2
  rw [map_sub,map_smul,map_smul,radialSame,unscaled] at first
  rw [map_add,map_smul,map_smul,radialSame,unscaled] at second
  rw [first,second,axialSame]
  simp only [cartesianCovariantValue_apply,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,Complex.real_smul,Complex.ofReal_inv]
  simp only [polarQuarter,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  have trig : (Real.cos angle : ℂ)^2+(Real.sin angle : ℂ)^2=1 := by exact_mod_cast Real.cos_sq_add_sin_sq angle
  calc
    _ = ((Real.cos angle : ℂ)^2+(Real.sin angle : ℂ)^2)*
        ((length : ℂ)*radial 0+(length : ℂ)/(radius : ℂ)*(angular 1+value 0))+axial 2 := by ring
    _ = _ := by rw [trig]; field_simp [Complex.ofReal_ne_zero.mpr lengthNonzero]; ring

/-- The SAME existing Q-rotated smooth curve has its literal Cartesian
divergence, at every point of the punctured original collar. -/
theorem sameCartesianRotation_divergence {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 3 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) (bounded : lower < 1)
    (length : ℝ) (lengthNonzero : length ≠ 0) (radius : ℝ) (inside : radius ∈ Ioo lower 1) (polar axial : ℝ) :
    cartesianDeterminantDivergence length (curves.cartesianCovariant.cartesianField bounded) (polarPlane (radius,polar),axial) =
      (length : ℂ)*(scalarDirectionalField curves bounded 0 (1,0,0) (radius,polar,axial)+curves.fullField bounded (radius,polar,axial) 0/(radius : ℂ)+
        scalarDirectionalField curves bounded 1 (0,1,0) (radius,polar,axial)/(radius : ℂ)+scalarDirectionalField curves bounded 2 (0,0,1) (radius,polar,axial)/(length : ℂ)) := by
  have algebra := determinantDivergence_polar_algebra length radius polar lengthNonzero (ne_of_gt (positive.trans inside.1)) _
    (curves.fullField bounded (radius,polar,axial))
    (vectorDirectionalField curves bounded (1,0,0) (radius,polar,axial))
    (vectorDirectionalField curves bounded (0,1,0) (radius,polar,axial))
    (vectorDirectionalField curves bounded (0,0,1) (radius,polar,axial))
    (sameCartesianRotation_radial curves bounded radius inside polar axial)
    (sameCartesianRotation_angular curves bounded radius inside polar axial)
    (sameCartesianRotation_axial curves bounded radius inside polar axial)
  simp_rw [vectorDirectionalField_component curves bounded _ _ (radius,polar,axial) inside] at algebra
  exact algebra

end Grad.ActualDeterminantEquations
