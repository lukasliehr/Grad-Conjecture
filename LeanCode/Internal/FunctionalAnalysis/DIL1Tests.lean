import DIL1Field

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.GenericCarriers (CellValues PhysicalValue FieldL2)
open Grad.WeightedJets (TestFunction)
open scoped ContDiff

namespace Grad.SpatialDilation

theorem integral_spatialMap (domain : Set Spatial) (measurableDomain : MeasurableSet domain)
    (scale : Scale) (integrand : Spatial → ℂ) :
    (∫ point in pullDomain scale domain, integrand (scale.val • point)) =
      (scale.val ^ 2)⁻¹ • ∫ point in domain, integrand point := by
  calc
    _ = ∫ point, integrand point ∂Measure.map (spatialMap scale)
        (volume.restrict (pullDomain scale domain)) :=
      (integral_map_equiv
        (Homeomorph.smul (isUnit_iff_ne_zero.mpr scale.property.1.ne').unit).toMeasurableEquiv integrand).symm
    _ = _ := by
      rw [map_measure domain measurableDomain scale, integral_smul_measure, jacobian,
        ENNReal.toReal_ofReal (inv_nonneg.mpr (sq_nonneg scale.val))]

theorem integral_rawValue (dimension : ℕ) (domain : Set Spatial) (measurableDomain : MeasurableSet domain)
    (scale : Scale) (test : Spatial → ℝ) (field : FieldL2 dimension domain)
    (cell : ℤ) (vector : PhysicalValue dimension) :
    (∫ point in pullDomain scale domain, test point • inner ℂ vector
      (rawValue dimension domain measurableDomain scale field point cell)) =
      (scale.val ^ 2)⁻¹ • ∫ point in domain,
        test (scale.val⁻¹ • point) • inner ℂ vector (field point cell) := by
  calc
    _ = ∫ point in pullDomain scale domain, test point • inner ℂ vector (field (scale.val • point) cell) := by
      apply integral_congr_ae
      filter_upwards [rawValue_ae dimension domain measurableDomain scale field] with point equality
      rw [equality]
    _ = _ := by
      convert integral_spatialMap domain measurableDomain scale
        (fun point => test (scale.val⁻¹ • point) • inner ℂ vector (field point cell)) using 1
      congr 1
      funext point
      rw [smul_smul, inv_mul_cancel₀ scale.property.1.ne', one_smul]

theorem orderedDerivative_scale (scalar : ℝ) (rank : ℕ) (word : Fin rank → Fin 2)
    (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) :
    Grad.WeakTesting.orderedTestDerivative rank word (fun point => test (scalar • point)) =
      fun point => scalar ^ rank * Grad.WeakTesting.orderedTestDerivative rank word test (scalar • point) := by
  funext point
  unfold Grad.WeakTesting.orderedTestDerivative
  rw [iteratedFDeriv_comp_const_smul scalar
    (smooth.of_le (by exact_mod_cast (le_top : (rank : ℕ∞) ≤ ⊤)))]
  rfl

def pulledTest (radius : ℝ) (scale : Scale) (test : TestFunction (expandedDisk radius scale)) :
    TestFunction (disk radius) where
  toFun := fun point => test.toFun (scale.val⁻¹ • point)
  smooth := test.smooth.comp (contDiff_id.const_smul scale.val⁻¹)
  compact := test.compact.comp_homeomorph
    (Homeomorph.smul (isUnit_iff_ne_zero.mpr (inv_ne_zero scale.property.1.ne')).unit)
  supported := by
    intro point membership
    have supportAt := tsupport_comp_subset_preimage test.toFun (continuous_const_smul scale.val⁻¹) membership
    have inside := test.supported supportAt
    change scale.val • (scale.val⁻¹ • point) ∈ disk radius at inside
    simpa only [smul_smul, mul_inv_cancel₀ scale.property.1.ne', one_smul] using inside

theorem pulledTest_derivative (radius : ℝ) (scale : Scale)
    (test : TestFunction (expandedDisk radius scale)) (rank : ℕ) (word : Fin rank → Fin 2) :
    Grad.WeakTesting.orderedTestDerivative rank word (pulledTest radius scale test).toFun =
      fun point => scale.val⁻¹ ^ rank *
        Grad.WeakTesting.orderedTestDerivative rank word test.toFun (scale.val⁻¹ • point) :=
  orderedDerivative_scale scale.val⁻¹ rank word test.toFun test.smooth

theorem testPairing_rawValue (dimension : ℕ) (radius : ℝ) (scale : Scale)
    (test : TestFunction (expandedDisk radius scale)) (field : FieldL2 dimension (disk radius))
    (cell : ℤ) (vector : PhysicalValue dimension) :
    Grad.WeightedJets.testPairing dimension (expandedDisk radius scale) cell vector test
        (rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale field) =
      (scale.val ^ 2)⁻¹ • Grad.WeightedJets.testPairing dimension (disk radius) cell vector
        (pulledTest radius scale test) field := by
  calc
    _ = ∫ point in expandedDisk radius scale, test.toFun point • inner ℂ vector
        (rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale field point cell) :=
      Grad.WeightedJets.testPairing_apply dimension (expandedDisk radius scale) cell vector test _
    _ = (scale.val ^ 2)⁻¹ • ∫ point in disk radius,
        (pulledTest radius scale test).toFun point • inner ℂ vector (field point cell) :=
      integral_rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale test.toFun field cell vector
    _ = _ := congrArg (fun value : ℂ => (scale.val ^ 2)⁻¹ • value)
      (Grad.WeightedJets.testPairing_apply dimension (disk radius) cell vector (pulledTest radius scale test) field).symm

theorem test_goal : TestGoal := by
  refine ⟨orderedDerivative_scale, ?_⟩
  intro radius scale test
  refine ⟨pulledTest radius scale test, rfl, pulledTest_derivative radius scale test, ?_⟩
  intro dimension field cell vector
  exact ⟨testPairing_rawValue dimension radius scale test field cell vector,
    integral_rawValue dimension (disk radius) Metric.isOpen_ball.measurableSet scale test.toFun field cell vector⟩

end Grad.SpatialDilation
