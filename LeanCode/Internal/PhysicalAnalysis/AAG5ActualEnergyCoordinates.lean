import AAG4EnergyMultipliers

noncomputable section
set_option maxHeartbeats 800000

namespace Grad.AnnularVariational

open Grad.ClosedJets Grad.SourceCollarDivision

def annularModeDerivative (lower : ℝ) : AnnularModeEnergyAmbient lower →L[ℂ] RadialL2 1 lower :=
  (ContinuousLinearMap.fst ℂ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap

def annularModeRest (lower : ℝ) :
    AnnularModeEnergyAmbient lower →L[ℂ] WithLp 2 (RadialL2 1 lower × ComplexEuclidean 1) :=
  (ContinuousLinearMap.snd ℂ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap

def annularModeMass (lower : ℝ) : AnnularModeEnergyAmbient lower →L[ℂ] RadialL2 1 lower :=
  ((ContinuousLinearMap.fst ℂ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap).comp
    (annularModeRest lower)

def annularModeOuter (lower : ℝ) : AnnularModeEnergyAmbient lower →L[ℂ] ComplexEuclidean 1 :=
  ((ContinuousLinearMap.snd ℂ _ _).comp (WithLp.prodContinuousLinearEquiv 2 ℂ _ _).toContinuousLinearMap).comp
    (annularModeRest lower)

theorem annularModeEnergy_norm_sq (lower : ℝ) (field : AnnularModeEnergyAmbient lower) :
    ‖field‖ ^ 2 = ‖annularModeDerivative lower field‖ ^ 2 + ‖annularModeMass lower field‖ ^ 2 +
      ‖annularModeOuter lower field‖ ^ 2 := by
  have first := WithLp.prod_norm_sq_eq_of_L2 field
  have second := WithLp.prod_norm_sq_eq_of_L2 (annularModeRest lower field)
  change ‖field‖ ^ 2 = ‖annularModeDerivative lower field‖ ^ 2 + ‖annularModeRest lower field‖ ^ 2 at first
  change ‖annularModeRest lower field‖ ^ 2 =
    ‖annularModeMass lower field‖ ^ 2 + ‖annularModeOuter lower field‖ ^ 2 at second
  linarith

theorem annularModeDerivative_bound (lower : ℝ) (field : AnnularModeEnergyAmbient lower) :
    ‖annularModeDerivative lower field‖ ≤ 1 * ‖field‖ := by
  have identity := annularModeEnergy_norm_sq lower field
  nlinarith [norm_nonneg field, norm_nonneg (annularModeDerivative lower field),
    sq_nonneg ‖annularModeMass lower field‖, sq_nonneg ‖annularModeOuter lower field‖]

theorem annularModeMass_bound (lower : ℝ) (field : AnnularModeEnergyAmbient lower) :
    ‖annularModeMass lower field‖ ≤ 1 * ‖field‖ := by
  have identity := annularModeEnergy_norm_sq lower field
  nlinarith [norm_nonneg field, norm_nonneg (annularModeMass lower field),
    sq_nonneg ‖annularModeDerivative lower field‖, sq_nonneg ‖annularModeOuter lower field‖]

theorem annularModeOuter_bound (lower : ℝ) (field : AnnularModeEnergyAmbient lower) :
    ‖annularModeOuter lower field‖ ≤ 1 * ‖field‖ := by
  have identity := annularModeEnergy_norm_sq lower field
  nlinarith [norm_nonneg field, norm_nonneg (annularModeOuter lower field),
    sq_nonneg ‖annularModeDerivative lower field‖, sq_nonneg ‖annularModeMass lower field‖]

abbrev AnnularBulk (lower : ℝ) := lp (fun _ : HighAnnularMode => RadialL2 1 lower) 2
abbrev AnnularBoundary := lp (fun _ : HighAnnularMode => ComplexEuclidean 1) 2

def annularAmbientDerivative (lower : ℝ) : AnnularEnergyAmbient lower →L[ℂ] AnnularBulk lower :=
  complexLpTwoMap (fun _ => annularModeDerivative lower) 1 (by norm_num) (fun _ => annularModeDerivative_bound lower)

def annularAmbientMass (lower : ℝ) : AnnularEnergyAmbient lower →L[ℂ] AnnularBulk lower :=
  complexLpTwoMap (fun _ => annularModeMass lower) 1 (by norm_num) (fun _ => annularModeMass_bound lower)

def annularAmbientOuter (lower : ℝ) : AnnularEnergyAmbient lower →L[ℂ] AnnularBoundary :=
  complexLpTwoMap (fun _ => annularModeOuter lower) 1 (by norm_num) (fun _ => annularModeOuter_bound lower)

def annularEnergyDerivative (lower length : ℝ) (positive : 0 < lower) :
    annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  (annularAmbientDerivative lower).comp (annularEnergySpace lower length positive).subtypeL

def annularEnergyMass (lower length : ℝ) (positive : 0 < lower) :
    annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  (annularAmbientMass lower).comp (annularEnergySpace lower length positive).subtypeL

def annularEnergyOuter (lower length : ℝ) (positive : 0 < lower) :
    annularEnergySpace lower length positive →L[ℂ] AnnularBoundary :=
  (annularAmbientOuter lower).comp (annularEnergySpace lower length positive).subtypeL

theorem annularEnergyDerivative_bound (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) :
    ‖annularEnergyDerivative lower length positive field‖ ≤ ‖field‖ := by
  change ‖annularAmbientDerivative lower field.val‖ ≤ ‖field.val‖
  simpa only [one_mul, annularEnergyDerivative, annularAmbientDerivative, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply] using complexLpTwoMap_bound (fun _ : HighAnnularMode => annularModeDerivative lower) 1
    (by norm_num) (fun _ => annularModeDerivative_bound lower) field.val

theorem annularEnergyMass_bound (lower length : ℝ) (positive : 0 < lower)
    (field : annularEnergySpace lower length positive) :
    ‖annularEnergyMass lower length positive field‖ ≤ ‖field‖ := by
  change ‖annularAmbientMass lower field.val‖ ≤ ‖field.val‖
  simpa only [one_mul, annularEnergyMass, annularAmbientMass, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply] using complexLpTwoMap_bound (fun _ : HighAnnularMode => annularModeMass lower) 1
    (by norm_num) (fun _ => annularModeMass_bound lower) field.val

def annularEnergyPhase (parameters : Grad.CartesianState.PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length)) :
    annularEnergySpace lower length positive →L[ℂ] AnnularBulk lower :=
  (complexLpTwoMap (annularPhaseMassMap parameters lower length positive lengthPositive widthHalf widthLength)
    (1 / 2) (by norm_num)
    (annularPhaseMassMap_bound parameters lower length positive lengthPositive widthHalf widthLength)).comp
      (annularEnergyMass lower length positive)

theorem annularEnergyPhase_bound (parameters : Grad.CartesianState.PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (field : annularEnergySpace lower length positive) :
    ‖annularEnergyPhase parameters lower length positive lengthPositive widthHalf widthLength field‖ ≤
      (1 / 2 : ℝ) * ‖field‖ :=
  (complexLpTwoMap_bound
    (annularPhaseMassMap parameters lower length positive lengthPositive widthHalf widthLength)
    (1 / 2) (by norm_num)
    (annularPhaseMassMap_bound parameters lower length positive lengthPositive widthHalf widthLength)
    (annularEnergyMass lower length positive field)).trans
    (mul_le_mul_of_nonneg_left (annularEnergyMass_bound lower length positive field) (by norm_num))

end Grad.AnnularVariational
