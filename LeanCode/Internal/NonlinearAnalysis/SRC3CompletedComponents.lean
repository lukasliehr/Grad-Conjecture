import SRC2OriginalSource

noncomputable section

namespace Grad.SourceCollarBulk

open Grad.ClosedJets Grad.CartesianState Grad.AxisCore Grad.QuotientProjection
open Grad.SourceCollarDivision Grad.SourceCollarRestriction
open Grad.SourceCollarAngular Grad.CompatibleCompletion Grad.FlatSourceProjection

/-- The completed BS36 component `F0 = e_theta dot f`, stored at angular
power `t+1` with both its value and weak radial derivative. -/
def completedForceTangential (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (tangential : ℕ) :
    ZAmbient parameters (tangential + 2) →L[ℂ]
      annularDerivativeGraph 1 lower positive 1 :=
  (completedTangentialContraction lower positive bounded parameters
    (tangential + 1) 1).comp
      (originalSourcePlanar parameters (tangential + 2))

/-- The completed radial component `F1 = e_r dot f`, retained in the same
full weak radial graph as `F0`. -/
def completedForceRadial (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (tangential : ℕ) :
    ZAmbient parameters (tangential + 2) →L[ℂ]
      annularDerivativeGraph 1 lower positive 1 :=
  (completedRadialContraction lower positive bounded parameters
    (tangential + 1) 1).comp
      (originalSourcePlanar parameters (tangential + 2))

/-- The completed fourth component `F2 = h/L`, at angular power `t` and
weak radial order one. The source is lowered from `t+2` to its exact required
grade `t+1` before restriction. -/
def completedFourthSource (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (L : ℝ)
    (tangential : ℕ) :
    ZAmbient parameters (tangential + 2) →L[ℂ]
      annularDerivativeGraph 1 lower positive 1 :=
  (((L : ℂ)⁻¹) •
      (completedRestriction (dimension := 1) lower positive bounded parameters
        tangential 1)).comp
    ((completedInclusion parameters (show tangential + 1 ≤ tangential + 2 by omega)).comp
      (originalSourceComponent parameters (tangential + 2) 3))

/-- The genuine `R F0` weak graph. Multiplication by `im/nu` lowers the
stored `nu^(t+1)` row to the exact `nu^t` angular derivative row. -/
def completedForceAngular (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (tangential : ℕ) :
    ZAmbient parameters (tangential + 2) →L[ℂ]
      annularDerivativeGraph 1 lower positive 1 :=
  (annularAngularDerivative lower positive).comp
    (completedForceTangential lower positive bounded parameters tangential)

theorem completedForceTangential_bound (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (tangential : ℕ)
    (source : ZAmbient parameters (tangential + 2)) :
    ‖completedForceTangential lower positive bounded parameters tangential source‖ ≤
      (2 * (2 : ℝ) ^ (tangential + 1) *
        restrictionGraphConstant (tangential + 1) 1) * ‖source‖ := by
  exact (completedTangentialContraction_bound lower positive bounded parameters
    (tangential + 1) 1 (originalSourcePlanar parameters (tangential + 2) source)).trans
      (mul_le_mul_of_nonneg_left
        (originalSourcePlanar_bound parameters (tangential + 2) source)
        (mul_nonneg (by positivity)
          (restrictionGraphConstant_nonnegative (tangential + 1) 1)))

theorem completedForceRadial_bound (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (tangential : ℕ)
    (source : ZAmbient parameters (tangential + 2)) :
    ‖completedForceRadial lower positive bounded parameters tangential source‖ ≤
      (2 * (2 : ℝ) ^ (tangential + 1) *
        restrictionGraphConstant (tangential + 1) 1) * ‖source‖ := by
  exact (completedRadialContraction_bound lower positive bounded parameters
    (tangential + 1) 1 (originalSourcePlanar parameters (tangential + 2) source)).trans
      (mul_le_mul_of_nonneg_left
        (originalSourcePlanar_bound parameters (tangential + 2) source)
        (mul_nonneg (by positivity)
          (restrictionGraphConstant_nonnegative (tangential + 1) 1)))

theorem completedForceAngular_bound (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (tangential : ℕ)
    (source : ZAmbient parameters (tangential + 2)) :
    ‖completedForceAngular lower positive bounded parameters tangential source‖ ≤
      (2 * (2 : ℝ) ^ (tangential + 1) *
        restrictionGraphConstant (tangential + 1) 1) * ‖source‖ :=
  (annularAngularDerivative_apply_norm_le lower positive _).trans
    (completedForceTangential_bound lower positive bounded parameters tangential source)

theorem completedFourthSource_bound (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (L : ℝ)
    (LPositive : 0 < L) (tangential : ℕ)
    (source : ZAmbient parameters (tangential + 2)) :
    ‖completedFourthSource lower positive bounded parameters L tangential source‖ ≤
      (L⁻¹ * restrictionGraphConstant tangential 1) * ‖source‖ := by
  have inclusion :=
    (completedInclusion parameters (show tangential + 1 ≤ tangential + 2 by omega)).le_opNorm
      (originalSourceComponent parameters (tangential + 2) 3 source)
  have lowered :
      ‖completedInclusion parameters (show tangential + 1 ≤ tangential + 2 by omega)
          (originalSourceComponent parameters (tangential + 2) 3 source)‖ ≤ ‖source‖ :=
    inclusion.trans ((mul_le_mul_of_nonneg_right
        (completedInclusion_norm_le_one parameters
          (show tangential + 1 ≤ tangential + 2 by omega))
        (norm_nonneg _)).trans
      ((one_mul _).trans_le
        (originalSourceComponent_bound parameters (tangential + 2) 3 source)))
  rw [completedFourthSource, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  change ‖(L : ℂ)⁻¹ • completedRestriction lower positive bounded parameters
    tangential 1 (completedInclusion parameters
      (show tangential + 1 ≤ tangential + 2 by omega)
      (originalSourceComponent parameters (tangential + 2) 3 source))‖ ≤ _
  rw [norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg LPositive.le]
  exact (mul_le_mul_of_nonneg_left
    ((completedRestriction_bound lower positive bounded parameters tangential 1 _).trans
      (mul_le_mul_of_nonneg_left lowered
        (restrictionGraphConstant_nonnegative tangential 1)))
    (inv_nonneg.mpr LPositive.le)).trans_eq (by ring)

theorem completedForceTangential_core (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (tangential : ℕ)
    (source : SmoothQuotient parameters) :
    completedForceTangential lower positive bounded parameters tangential
        (quotientEta parameters (tangential + 2) source) =
      completedTangentialContraction lower positive bounded parameters
        (tangential + 1) 1
          (aGradeEta parameters
            (GradeCore.ofCoreLinear (cartesianSourceVector source))) := by
  rw [completedForceTangential, ContinuousLinearMap.comp_apply,
    originalSourcePlanar_core]

theorem completedForceRadial_core (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (tangential : ℕ)
    (source : SmoothQuotient parameters) :
    completedForceRadial lower positive bounded parameters tangential
        (quotientEta parameters (tangential + 2) source) =
      completedRadialContraction lower positive bounded parameters
        (tangential + 1) 1
          (aGradeEta parameters
            (GradeCore.ofCoreLinear (cartesianSourceVector source))) := by
  rw [completedForceRadial, ContinuousLinearMap.comp_apply,
    originalSourcePlanar_core]

theorem completedFourthSource_core (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (L : ℝ)
    (tangential : ℕ) (source : SmoothQuotient parameters) :
    completedFourthSource lower positive bounded parameters L tangential
        (quotientEta parameters (tangential + 2) source) =
      (L : ℂ)⁻¹ • completedRestriction lower positive bounded parameters
        tangential 1
          (aGradeEta parameters (GradeCore.ofCoreLinear (source 3))) := by
  have component := originalSourceComponent_core parameters (tangential + 2) 3 source
  have lowered := completedInclusion_apply_eta parameters
    (show tangential + 1 ≤ tangential + 2 by omega)
    (GradeCore.ofCoreLinear (grade := tangential + 2) (source 3))
  have sourceLowered :
      completedInclusion parameters (show tangential + 1 ≤ tangential + 2 by omega)
          (originalSourceComponent parameters (tangential + 2) 3
            (quotientEta parameters (tangential + 2) source)) =
        aGradeEta parameters (GradeCore.ofCoreLinear (source 3)) :=
    (congrArg (completedInclusion parameters
      (show tangential + 1 ≤ tangential + 2 by omega)) component).trans lowered
  have result := congrArg (fun value : AGrade parameters 1 (tangential + 1) =>
    (L : ℂ)⁻¹ • completedRestriction lower positive bounded parameters
      tangential 1 value) sourceLowered
  simpa only [completedFourthSource, ContinuousLinearMap.comp_apply, smul_apply] using result

theorem completedForceAngular_core (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (parameters : PhaseParameters) (tangential : ℕ)
    (source : SmoothQuotient parameters) :
    completedForceAngular lower positive bounded parameters tangential
        (quotientEta parameters (tangential + 2) source) =
      annularAngularDerivative lower positive
        (completedTangentialContraction lower positive bounded parameters
          (tangential + 1) 1
            (aGradeEta parameters
              (GradeCore.ofCoreLinear (cartesianSourceVector source)))) := by
  rw [completedForceAngular, ContinuousLinearMap.comp_apply,
    completedForceTangential_core]

end Grad.SourceCollarBulk
