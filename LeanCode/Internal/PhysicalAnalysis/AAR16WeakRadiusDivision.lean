import AAR13ScalarVariationalTests
import ANR27RadialFluxCalculus

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

def annularInverseRadiusCurve (lower : ℝ) (positive : 0 < lower) : C(ℝ, ℝ) :=
  ⟨fun radius => 1 / max lower radius,
    continuous_const.div (continuous_const.max continuous_id)
      (fun radius => (positive.trans_le (le_max_left lower radius)).ne')⟩

def annularInverseRadiusSlope (lower : ℝ) (positive : 0 < lower) : C(ℝ, ℝ) :=
  -(annularInverseRadiusCurve lower positive * annularInverseRadiusCurve lower positive)

theorem inverseRadius_test_smooth (lower : ℝ) (positive : 0 < lower)
    (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile) (supported : tsupport profile ⊆ Ioo lower 1) :
    ContDiff ℝ ∞ (fun radius => radius⁻¹ * profile radius) := by
  rw [contDiff_iff_contDiffAt]
  intro radius
  by_cases zero : radius = 0
  · subst radius
    have outside : (0 : ℝ) ∉ tsupport profile := by
      intro member
      have inside := supported member
      linarith [inside.1]
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport profile).isOpen_compl.mem_nhds outside] with radius absent
    rw [image_eq_zero_of_notMem_tsupport absent, mul_zero]
  · exact (contDiffAt_id.fun_inv zero).mul smooth.contDiffAt

/-- Division by the literal positive radius preserves genuine weak graphs.
Compact tests are divided by r; their support removes the apparent pole. -/
theorem compactWeakDerivative_divide_radius (lower : ℝ) (positive : 0 < lower)
    (value derivative : CollarL2 (ComplexEuclidean 1) lower)
    (weak : CompactWeakDerivative 1 lower value derivative) :
    CompactWeakDerivative 1 lower
      (collarScalar 1 lower (annularInverseRadiusCurve lower positive) value)
      (collarScalar 1 lower (annularInverseRadiusSlope lower positive) value +
        collarScalar 1 lower (annularInverseRadiusCurve lower positive) derivative) := by
  intro profile smooth compact supported vector
  let auxiliary : ℝ → ℝ := fun radius => radius⁻¹ * profile radius
  have auxiliarySmooth := inverseRadius_test_smooth lower positive profile smooth supported
  have auxiliarySupport : tsupport auxiliary ⊆ Ioo lower 1 := tsupport_mul_subset_right.trans supported
  have auxiliaryCompact : HasCompactSupport auxiliary := compact.mul_left
  let testMap : C(ℝ, ℝ) := ⟨profile, smooth.continuous⟩
  let derivativeMap : C(ℝ, ℝ) := ⟨deriv profile, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩
  let auxiliaryMap : C(ℝ, ℝ) := ⟨auxiliary, auxiliarySmooth.continuous⟩
  let auxiliaryDerivative : C(ℝ, ℝ) := ⟨deriv auxiliary, (contDiff_infty_iff_deriv.mp auxiliarySmooth).2.continuous⟩
  have valueEquality : ∀ radius ∈ Icc lower 1,
      auxiliaryMap radius = (testMap * annularInverseRadiusCurve lower positive) radius := by
    intro radius inside
    change radius⁻¹ * profile radius = profile radius * (1 / max lower radius)
    rw [max_eq_right inside.1, one_div, mul_comm]
  have derivativeEquality : ∀ radius ∈ Icc lower 1,
      auxiliaryDerivative radius =
        (derivativeMap * annularInverseRadiusCurve lower positive + testMap * annularInverseRadiusSlope lower positive) radius := by
    intro radius inside
    have radiusNonzero := (positive.trans_le inside.1).ne'
    have differentiated := (((hasDerivAt_id radius).inv radiusNonzero).mul
      (smooth.differentiable (by simp) radius).hasDerivAt).deriv
    change deriv auxiliary radius = _ at differentiated
    change deriv auxiliary radius = deriv profile radius * (1 / max lower radius) +
      profile radius * -((1 / max lower radius) * (1 / max lower radius))
    rw [differentiated, max_eq_right inside.1]
    simp only [id_eq, Pi.inv_apply]
    field_simp [radiusNonzero]
    ring
  have law := weak auxiliary auxiliarySmooth auxiliaryCompact auxiliarySupport vector
  have valuePair := collarPairing_test_congr 1 lower auxiliaryMap
    (testMap * annularInverseRadiusCurve lower positive) valueEquality vector derivative
  have derivativePair := collarPairing_test_congr 1 lower auxiliaryDerivative
    (derivativeMap * annularInverseRadiusCurve lower positive + testMap * annularInverseRadiusSlope lower positive)
    derivativeEquality vector value
  change collarPairing lower auxiliaryMap vector derivative = -collarPairing lower auxiliaryDerivative vector value at law
  rw [valuePair, derivativePair, collarPairing_test_add] at law
  rw [map_add, collarScalar_pairing, collarScalar_pairing, collarScalar_pairing]
  change collarPairing lower (testMap * annularInverseRadiusSlope lower positive) vector value +
    collarPairing lower (testMap * annularInverseRadiusCurve lower positive) vector derivative =
      -collarPairing lower (derivativeMap * annularInverseRadiusCurve lower positive) vector value
  linear_combination law

end Grad.AnnularReconstruction
