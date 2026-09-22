import AAR11SingleModeVariationalFormula
import AAR12RadialMomentCalculus
import AAG17ActualVariationalInverse

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.AnnularReconstruction
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

def annularPotentialCurve (lower length : ℝ) (positive : 0 < lower) (mode : HighAnnularMode) : C(ℝ, ℝ) :=
  annularPotentialWeight lower length positive mode.val.1 mode.val.2 *
    annularPotentialWeight lower length positive mode.val.1 mode.val.2

theorem annularPotentialCurve_literal (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (radius : ℝ) (inside : lower ≤ radius) :
    annularPotentialCurve lower length positive mode radius =
      annularPotential length radius mode.val.1 mode.val.2 := by
  change annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius *
    annularPotentialWeight lower length positive mode.val.1 mode.val.2 radius = _
  rw [← pow_two]
  exact annularPotentialWeight_sq lower length positive mode.val.1 mode.val.2 radius inside

theorem weightedCurve_scalar_pairing (lower : ℝ) (positive : 0 < lower)
    (coefficient test : C(ℝ, ℝ)) (vector : ComplexEuclidean 1) (field : RadialL2 1 lower) :
    inner ℂ (weightedCurveComplex 1 lower (continuousCurveWeight 1 coefficient (collarTestCurve test vector))) field =
      collarPairing lower test vector (collarScalar 1 lower coefficient (annularRadialMoment lower positive field)) := by
  rw [← collarScalar_weightedCurve, collarScalar_inner, weightedCurve_test_moment, annularRadialMoment_scalar]

theorem annularMass_scalar_pairing (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (test : C(ℝ, ℝ)) (vector : ComplexEuclidean 1)
    (field : annularEnergySpace lower length positive) :
    inner ℂ (weightedCurveComplex 1 lower
      (continuousCurveWeight 1 (annularPotentialWeight lower length positive mode.val.1 mode.val.2)
        (collarTestCurve test vector))) (annularEnergyMass lower length positive field mode) =
      collarPairing lower test vector (collarScalar 1 lower (annularPotentialCurve lower length positive mode)
        (annularRadialMoment lower positive (annularEnergyValue lower length positive field mode))) := by
  rw [← collarScalar_weightedCurve, collarScalar_inner, annularEnergyMass_mode, collarScalar_mul_apply,
    weightedCurve_test_moment, annularRadialMoment_scalar]
  rfl

theorem smoothScalarRadialCore_value_curve (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile)
    (vector : ComplexEuclidean 1) :
    (smoothScalarRadialCore profile smooth vector).val.1 = collarTestCurve ⟨profile, smooth.continuous⟩ vector := rfl

theorem smoothScalarRadialCore_slope_curve (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile)
    (vector : ComplexEuclidean 1) :
    (smoothScalarRadialCore profile smooth vector).val.2 =
      collarTestCurve ⟨deriv profile, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩ vector := by
  apply ContinuousMap.ext
  intro radius
  exact smoothScalarRadialCore_slope profile smooth vector radius

def annularScalarTest (lower length : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile)
    (vector : ComplexEuclidean 1) : annularEnergySpace lower length positive :=
  annularEnergyCoreInto lower length positive (Finsupp.single mode (smoothScalarRadialCore profile smooth vector))

theorem annularScalarTest_inner_zero (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (mode : HighAnnularMode) (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile)
    (innerZero : profile lower = 0) (vector : ComplexEuclidean 1) :
    annularScalarTest lower length positive mode profile smooth vector ∈
      annularInnerZero lower length positive bounded lengthPositive := by
  change annularEnergyTrace lower length positive bounded lengthPositive 0
    (annularEnergyCoreInto lower length positive (Finsupp.single mode (smoothScalarRadialCore profile smooth vector))) = 0
  rw [annularEnergyTrace_single]
  change lp.single 2 mode ((Real.sqrt (Grad.AnnularVariational.annularFrequency mode.val.1 mode.val.2) : ℂ) •
    (profile lower • vector)) = (0 : AnnularBoundary)
  rw [innerZero, zero_smul, smul_zero]
  exact map_zero (lp.singleContinuousLinearMap ℂ (fun _ : HighAnnularMode => ComplexEuclidean 1) 2 mode)

/-- Actual single smooth tests of the solved variational problem. The sole
test restriction is its prescribed zero inner value; its outer value is free. -/
theorem annularVariationalSolution_scalar_test (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * length))
    (source : AnnularForcing lower) (innerValue : AnnularBoundary)
    (mode : HighAnnularMode) (profile : ℝ → ℝ) (smooth : ContDiff ℝ ∞ profile)
    (innerZero : profile lower = 0) (vector : ComplexEuclidean 1) :
    annularFormValue parameters lower length positive lengthPositive widthHalf widthLength
      (annularVariationalSolution parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue)
      (annularScalarTest lower length positive mode profile smooth vector) =
    annularFunctionalValue parameters lower length positive bounded lengthPositive widthHalf widthLength source
      (annularScalarTest lower length positive mode profile smooth vector) :=
  annularVariationalSolution_weak parameters lower length positive bounded lengthPositive widthHalf widthLength source innerValue
    ⟨_, annularScalarTest_inner_zero lower length positive bounded lengthPositive mode profile smooth innerZero vector⟩

end Grad.AnnularReconstruction
