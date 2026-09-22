import AKBJ20ScalarMeanPuncturedTranspose
import AKBE2ProjectedForceAxisRemoval

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators Topology
namespace Grad.ActualScalarWeakEquations
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianStartup Grad.CartesianState
open Grad.ActualCartesianWeakEquations Grad.WeightedAxisRemoval Grad.ActualAnnularExhaustion

def scalarP0Test (test : Spatial → ℝ) : Spatial → ℝ := test - startupAngularTest (fun _ => 1) test

theorem scalarP0Test_smooth (test : Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) :
    ContDiff ℝ ∞ (scalarP0Test test) := smooth.sub (startupAngularTest_smooth _ contDiff_const test smooth)

theorem scalarP0Test_compact (test : Spatial → ℝ) (compact : HasCompactSupport test) :
    HasCompactSupport (scalarP0Test test) := compact.sub (startupAngularTest_compact _ test compact)

theorem scalarP0Test_supported (test : Spatial → ℝ) (supported : tsupport test ⊆ openUnitDisk) :
    tsupport (scalarP0Test test) ⊆ openUnitDisk :=
  (tsupport_sub _ _).trans (union_subset supported (startupAngularTest_supported _ test supported))

theorem scalarP0Test_away (test : Spatial → ℝ) (away : (0 : Spatial) ∉ tsupport test) :
    (0 : Spatial) ∉ tsupport (scalarP0Test test) := by
  apply notMem_tsupport_iff_eventuallyEq.mpr
  filter_upwards [notMem_tsupport_iff_eventuallyEq.mp away,
    notMem_tsupport_iff_eventuallyEq.mp (originalAngularTest_away (fun _ => 1) test away)] with point first second
  change test point - startupAngularTest (fun _ => 1) test point = 0
  rw [first,second,sub_self]

theorem scalarP0Test_axisCutoff (epsilon : ℝ) (test : Spatial → ℝ) :
    scalarP0Test (axisCutoffTest epsilon test) = axisCutoffTest epsilon (scalarP0Test test) := by
  have average := startupAngularTest_radial_product (fun _ => 1) (axisCutoff epsilon) test
    (fun angle point => axisCutoff_same_norm epsilon _ _ (LinearIsometryEquiv.norm_map _ _))
  unfold scalarP0Test axisCutoffTest
  rw [average]
  funext point
  simp only [Pi.sub_apply]
  ring

/-- Projected scalar divergence crosses the axis using the same flux and flux/r bounds. The original scalar source is tested without adding a projection. -/
theorem projectedScalar_equation_remove_axis (source zeroth : Spatial → ℂ) (flux : Fin 2 → Spatial → ℂ)
    (sourceIntegrable : IntegrableOn source openUnitDisk)
    (zerothIntegrable : IntegrableOn zeroth openUnitDisk)
    (fluxIntegrable : ∀ direction, IntegrableOn (flux direction) openUnitDisk)
    (weightedIntegrable : ∀ direction, IntegrableOn (fun point => ‖point‖⁻¹ * ‖flux direction point‖) openUnitDisk)
    (punctured : ∀ (test : Spatial → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test →
      tsupport test ⊆ openUnitDisk → (0 : Spatial) ∉ tsupport test →
      (∫ point in openUnitDisk, test point • source point) -
        (∫ point in openUnitDisk, scalarP0Test test point • zeroth point) =
        -(∑ direction : Fin 2, ∫ point in openUnitDisk,
          fderiv ℝ (scalarP0Test test) point (spatialDirection direction) • flux direction point)) :
    ∀ (test : Spatial → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test → tsupport test ⊆ openUnitDisk →
      (∫ point in openUnitDisk, test point • source point) -
        (∫ point in openUnitDisk, scalarP0Test test point • zeroth point) =
        -(∑ direction : Fin 2, ∫ point in openUnitDisk,
          fderiv ℝ (scalarP0Test test) point (spatialDirection direction) • flux direction point) := by
  intro test smooth compact supported
  have away : ∀ᵐ point ∂volume.restrict openUnitDisk, point ≠ (0 : Spatial) := by simp [ae_iff]
  let epsilon := originalExhaustionRadius (1 : ℝ)
  have positive : ∀ index, 0 < epsilon index := originalExhaustionRadius_positive 1 (by norm_num)
  have vanishing : Tendsto epsilon atTop (𝓝 0) := originalExhaustionRadius_tendsto 1
  have left := (axisCutoffTest_integral_tendsto (volume.restrict openUnitDisk) away epsilon positive vanishing
    test smooth compact source sourceIntegrable).sub
      (axisCutoffTest_integral_tendsto (volume.restrict openUnitDisk) away epsilon positive vanishing
        (scalarP0Test test) (scalarP0Test_smooth test smooth) (scalarP0Test_compact test compact) zeroth zerothIntegrable)
  have right := (tendsto_finsetSum Finset.univ (fun direction _ =>
    axisCutoffTest_derivative_integral_tendsto (volume.restrict openUnitDisk) away epsilon positive vanishing
      (scalarP0Test test) (scalarP0Test_smooth test smooth) (scalarP0Test_compact test compact) (flux direction)
      (fluxIntegrable direction) (weightedIntegrable direction) (spatialDirection direction))).neg
  have equality (index : ℕ) :
      (∫ point in openUnitDisk, axisCutoffTest (epsilon index) test point • source point) -
        (∫ point in openUnitDisk, axisCutoffTest (epsilon index) (scalarP0Test test) point • zeroth point) =
      -(∑ direction : Fin 2, ∫ point in openUnitDisk,
        fderiv ℝ (axisCutoffTest (epsilon index) (scalarP0Test test)) point (spatialDirection direction) • flux direction point) := by
    simpa only [scalarP0Test_axisCutoff] using punctured (axisCutoffTest (epsilon index) test)
      (axisCutoffTest_smooth _ test smooth) (axisCutoffTest_compact _ test compact)
      ((axisCutoffTest_support _ test).trans supported) (axisCutoffTest_away _ (positive index) test)
  exact tendsto_nhds_unique (left.congr' (Eventually.of_forall equality)) right

end Grad.ActualScalarWeakEquations
