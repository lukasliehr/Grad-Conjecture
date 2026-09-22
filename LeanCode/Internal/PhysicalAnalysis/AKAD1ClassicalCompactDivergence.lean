import AKAB20OriginalEnergyAxisRemoval
import GC18APIntegrationByParts

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators

namespace Grad.PhysicalAxisEquation
open Grad.PDEBootstrap Grad.RepresentedKernel.SpatialProduct
open Grad.GaugeCoefficients.Physical.RadialLedger

theorem vectorFirstDerivative_ibp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (domain : Set Spatial) (openDomain : IsOpen domain)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test)
    (testCompact : HasCompactSupport test) (testSupported : tsupport test ⊆ domain)
    (function : Spatial → E) (functionSmooth : ContDiffOn ℝ ∞ function domain)
    (direction : Fin 2) :
    (∫ point in domain, test point • directionDerivative direction function point) =
      -∫ point in domain,
        Grad.WeakTesting.Commutation.differentiate direction test point • function point := by
  let testDerivative := Grad.WeakTesting.Commutation.differentiate direction test
  let functionDerivative := directionDerivative direction function
  have testDerivativeSmooth : ContDiff ℝ ∞ testDerivative :=
    Grad.WeakTesting.Commutation.differentiate_contDiff direction test testSmooth
  have testDerivativeCompact : HasCompactSupport testDerivative :=
    differentiate_compact direction test testCompact
  have testDerivativeSupported : tsupport testDerivative ⊆ domain :=
    (differentiate_support direction test).trans testSupported
  have functionDerivativeSmooth : ContDiffOn ℝ ∞ functionDerivative domain :=
    directionDerivative_smooth openDomain direction functionSmooth
  have leftIntegrable : Integrable (fun point => test point • functionDerivative point) volume :=
    smul_integrable_of_tsupport_subset domain openDomain test testSmooth.continuous testCompact
      testSupported functionDerivative functionDerivativeSmooth.continuousOn
  have rightIntegrable : Integrable (fun point => testDerivative point • function point) volume :=
    smul_integrable_of_tsupport_subset domain openDomain testDerivative testDerivativeSmooth.continuous
      testDerivativeCompact testDerivativeSupported function functionSmooth.continuousOn
  have productIntegrable : Integrable (fun point => test point • function point) volume :=
    smul_integrable_of_tsupport_subset domain openDomain test testSmooth.continuous testCompact
      testSupported function functionSmooth.continuousOn
  have global := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
    (μ := volume) (f := test) (g := function) (v := spatialDirection direction)
      rightIntegrable leftIntegrable productIntegrable
      (fun point _membership => testSmooth.differentiable (by simp) point)
      (fun point membership =>
        (functionSmooth.contDiffAt (openDomain.mem_nhds (testSupported membership))).differentiableAt
          (by simp))
  change (∫ point, test point • functionDerivative point) =
      -∫ point, testDerivative point • function point at global
  rw [setIntegral_eq_integral_smul_of_tsupport_subset domain test testSupported functionDerivative,
    setIntegral_eq_integral_smul_of_tsupport_subset domain testDerivative testDerivativeSupported function]
  exact global

/-- The literal classical divergence equation yields the same weak identity
on compact tests inside its smooth open domain. Existing local support and
integration-by-parts infrastructure supplies every boundary cancellation. -/
theorem classical_divergence_compact_test {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (domain : Set Spatial) (openDomain : IsOpen domain)
    (flux : Fin 2 → Spatial → E) (source : Spatial → E)
    (smooth : ∀ index, ContDiffOn ℝ ∞ (flux index) domain)
    (equation : ∀ point ∈ domain, source point =
      ∑ index : Fin 2, directionDerivative index (flux index) point)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test)
    (compact : HasCompactSupport test) (supported : tsupport test ⊆ domain) :
    (∫ point in domain, test point • source point) =
      -(∑ index : Fin 2, ∫ point in domain,
        (fderiv ℝ test point (spatialDirection index)) • flux index point) := by
  have integrable (index : Fin 2) : IntegrableOn
      (fun point => test point • directionDerivative index (flux index) point) domain :=
    (smul_integrable_of_tsupport_subset domain openDomain test testSmooth.continuous compact
      supported _ (directionDerivative_smooth openDomain index (smooth index)).continuousOn).integrableOn
  calc
    _ = ∫ point in domain, ∑ index : Fin 2, test point • directionDerivative index (flux index) point := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem openDomain.measurableSet] with point inside
      rw [equation point inside,Finset.smul_sum]
    _ = ∑ index : Fin 2, ∫ point in domain, test point • directionDerivative index (flux index) point :=
      integral_finsetSum Finset.univ (fun index _ => integrable index)
    _ = _ := by
      simp_rw [vectorFirstDerivative_ibp domain openDomain test testSmooth compact supported
        _ (smooth _) _]
      rw [Finset.sum_neg_distrib]
      rfl

end Grad.PhysicalAxisEquation
