import AKBJ22ScalarProjectedClassicalTest

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1100000
open Set Filter MeasureTheory
open scoped ContDiff BigOperators
namespace Grad.ActualScalarWeakEquations
open Grad.PDEBootstrap Grad.ClosedJets Grad.CartesianStartup Grad.CartesianState
open Grad.PhysicalAxisEquation Grad.ActualCartesianWeakEquations
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.RepresentedKernel.SpatialProduct

def scalarDivergenceValue (flux : Fin 2 → Spatial → ℂ) (zeroth : Spatial → ℂ) (point : Spatial) : ComplexEuclidean 1 :=
  WithLp.toLp 2 (fun _ => (∑ direction : Fin 2, directionDerivative direction (flux direction) point) + zeroth point)

/-- The literal projected Cartesian scalar equation supplies its full-disk weak row. The axial zeroth term stays inside P0 and the actual source stays outside. -/
theorem originalProjectedScalarDivergence_weak
    (flux : Fin 2 → Spatial → ℂ) (zeroth source : Spatial → ℂ)
    (fluxSmooth : ∀ direction, ContDiffOn ℝ ∞ (flux direction) (openUnitDisk \ {(0 : Spatial)}))
    (zerothContinuous : ContinuousOn zeroth (openUnitDisk \ {(0 : Spatial)}))
    (sourceIntegrable : IntegrableOn source openUnitDisk) (zerothIntegrable : IntegrableOn zeroth openUnitDisk)
    (fluxIntegrable : ∀ direction, IntegrableOn (flux direction) openUnitDisk)
    (weightedIntegrable : ∀ direction, IntegrableOn (fun point => ‖point‖⁻¹ * ‖flux direction point‖) openUnitDisk)
    (equation : ∀ point : ClosedDisk, 0 < ‖point.val‖ → ‖point.val‖ < 1 →
      source point.val = scalarDivergenceValue flux zeroth point.val 0 -
        closedAngularMean (fun closed : ClosedDisk => scalarDivergenceValue flux zeroth closed.val) point 0) :
    ∀ (test : Spatial → ℝ), ContDiff ℝ ∞ test → HasCompactSupport test → tsupport test ⊆ openUnitDisk →
      (∫ point in openUnitDisk, test point • source point) -
        (∫ point in openUnitDisk, scalarP0Test test point • zeroth point) =
        -(∑ direction : Fin 2, ∫ point in openUnitDisk,
          fderiv ℝ (scalarP0Test test) point (spatialDirection direction) • flux direction point) := by
  have openPunctured : IsOpen (openUnitDisk \ {(0 : Spatial)}) := openUnitDisk_isOpen.sdiff isClosed_singleton
  have divergenceContinuous : ContinuousOn (fun point => ∑ direction : Fin 2, directionDerivative direction (flux direction) point)
      (openUnitDisk \ {(0 : Spatial)}) :=
    continuousOn_finsetSum _ (fun direction _ => (directionDerivative_smooth openPunctured direction (fluxSmooth direction)).continuousOn)
  have rawContinuous : ContinuousOn (scalarDivergenceValue flux zeroth) (openUnitDisk \ {(0 : Spatial)}) := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 1 => ℂ)).comp_continuousOn
    exact continuousOn_pi.mpr (fun _ => divergenceContinuous.add zerothContinuous)
  apply projectedScalar_equation_remove_axis source zeroth flux sourceIntegrable zerothIntegrable fluxIntegrable weightedIntegrable
  intro test smooth compact supported away
  have projected := scalarProjected_classicalTest (scalarDivergenceValue flux zeroth) rawContinuous source sourceIntegrable equation
    test smooth compact supported away
  have smoothTest := scalarP0Test_smooth test smooth
  have compactTest := scalarP0Test_compact test compact
  have supportedTest := scalarP0Test_supported test supported
  have awayTest := scalarP0Test_away test away
  have divIntegrable := scalarPunctured_testIntegrable _ divergenceContinuous (scalarP0Test test) smoothTest compactTest supportedTest awayTest
  have zerothTest := Grad.WeightedAxisRemoval.compactTest_smul_integrable (volume.restrict openUnitDisk)
    (scalarP0Test test) smoothTest compactTest zeroth zerothIntegrable
  have sumIntegral : (∫ point in openUnitDisk, scalarP0Test test point • scalarDivergenceValue flux zeroth point 0) =
      (∫ point in openUnitDisk, scalarP0Test test point • (∑ direction : Fin 2, directionDerivative direction (flux direction) point)) +
        ∫ point in openUnitDisk, scalarP0Test test point • zeroth point := by
    change (∫ point in openUnitDisk, scalarP0Test test point • ((∑ direction : Fin 2, directionDerivative direction (flux direction) point) + zeroth point)) = _
    simp_rw [smul_add]
    exact integral_add divIntegrable zerothTest
  rw [projected,sumIntegral,add_sub_cancel_right]
  exact punctured_classical_divergence_weak flux _ fluxSmooth (fun _ _ => rfl)
    (scalarP0Test test) smoothTest compactTest supportedTest awayTest

end Grad.ActualScalarWeakEquations
