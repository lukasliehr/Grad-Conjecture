import AKO7FullMovingIncomingLogBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped ENNReal BigOperators
namespace Grad.AnnularIncomingIntegrability
open Grad.AnnularVariational Grad.AnnularReconstruction Grad.AnnularRestriction Grad.AnnularLowEnergy
open Grad.AnnularCoupledInverse Grad.AnnularSourceGraph Grad.AnnularTiltedReference

theorem lowIncomingSquare_measurable (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) :
    Measurable (lowIncomingSquare lower length positive bounded field) := by
  apply Measurable.tsum
  intro index
  have frequency : Measurable (fun radius : ℝ => (lowMu length radius index.2.val.2)⁻¹) := by
    unfold lowMu
    fun_prop
  exact (((measurable_id.pow_const (-(7 / 2 : ℝ))).fun_mul frequency).fun_mul
    ((lowIncomingRepresentative lower length positive bounded field index).continuous.measurable.norm.pow_const 2)).ennreal_ofReal

theorem coupledIncomingSquare_measurable (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (lengthPositive : 0 < length) (field : CoupledSpace lower length positive lengthPositive) :
    Measurable (coupledIncomingSquare lower length positive bounded lengthPositive field) :=
  (highIncomingSquare_measurable lower length positive bounded field.ofLp.1.ofLp.1).fun_add
    (lowIncomingSquare_measurable lower length positive bounded field.ofLp.2)

/-- SAME density under an intermediate restriction. This uses genuine moving
traces and the accepted graph restriction composition laws. -/
theorem coupledIncomingSquare_restriction
    (lower middle radius length : ℝ) (lowerPositive : 0 < lower) (middlePositive : 0 < middle)
    (radiusPositive : 0 < radius) (radiusBounded : radius < 1) (lengthPositive : 0 < length)
    (first : lower ≤ middle) (second : middle ≤ radius)
    (field : CoupledSpace lower length lowerPositive lengthPositive) :
    coupledIncomingSquare middle length middlePositive (second.trans_lt radiusBounded) lengthPositive
      (coupledEndpointRestriction lower middle length lowerPositive middlePositive (second.trans_lt radiusBounded) lengthPositive first field) radius =
    coupledIncomingSquare lower length lowerPositive ((first.trans second).trans_lt radiusBounded) lengthPositive field radius := by
  have highInner := highIncomingSquare_eq_restricted_norm middle radius length middlePositive radiusPositive radiusBounded lengthPositive second
    (highEnergyRestriction lower middle length lowerPositive middlePositive first field.ofLp.1.ofLp.1)
  have highOuter := highIncomingSquare_eq_restricted_norm lower radius length lowerPositive radiusPositive radiusBounded lengthPositive (first.trans second)
    field.ofLp.1.ofLp.1
  rw [highEnergyRestriction_comp lower middle radius length lowerPositive middlePositive radiusPositive radiusBounded first second] at highInner
  have lowInner := lowIncomingSquare_eq_restricted_norm middle radius length middlePositive radiusPositive radiusBounded second
    (lowEnergyRestriction lower middle length first lowerPositive middlePositive (second.trans_lt radiusBounded) field.ofLp.2)
  have lowOuter := lowIncomingSquare_eq_restricted_norm lower radius length lowerPositive radiusPositive radiusBounded (first.trans second) field.ofLp.2
  rw [lowEnergyRestriction_comp lower middle radius length first second lowerPositive middlePositive radiusPositive radiusBounded] at lowInner
  exact congrArg₂ (fun high low : ℝ≥0∞ => high + low) (highInner.trans highOuter.symm) (lowInner.trans lowOuter.symm)

end Grad.AnnularIncomingIntegrability
