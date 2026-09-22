import RKWD1Pointwise
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open Grad.RepresentedKernel.SpatialProduct
open scoped BigOperators ContDiff Topology

namespace Grad.RepresentedKernel.WeakDerivatives

theorem continuous_smul_of_tsupport_subset {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] (domain : Set Spatial) (openDomain : IsOpen domain)
    (scalar : Spatial → ℝ) (scalarContinuous : Continuous scalar)
    (supported : tsupport scalar ⊆ domain) (vector : Spatial → Value)
    (vectorContinuous : ContinuousOn vector domain) :
    Continuous (fun point => scalar point • vector point) := by
  rw [continuous_iff_continuousAt]
  intro point
  by_cases inside : point ∈ domain
  · exact scalarContinuous.continuousAt.smul
      ((vectorContinuous point inside).continuousAt (openDomain.mem_nhds inside))
  · have outsideSupport : point ∉ tsupport scalar := fun membership => inside (supported membership)
    have neighborhood : (tsupport scalar)ᶜ ∈ 𝓝 point :=
      (isClosed_tsupport scalar).isOpen_compl.mem_nhds outsideSupport
    have zeroGerm : (fun source => scalar source • vector source) =ᶠ[𝓝 point] fun _ => 0 := by
      filter_upwards [neighborhood] with source sourceOutside
      rw [image_eq_zero_of_notMem_tsupport sourceOutside, zero_smul]
    exact (continuousAt_congr zeroGerm).mpr continuousAt_const

theorem smul_integrable_of_tsupport_subset {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℝ Value] [ProperSpace Spatial]
    (domain : Set Spatial) (openDomain : IsOpen domain)
    (scalar : Spatial → ℝ) (scalarContinuous : Continuous scalar)
    (compact : HasCompactSupport scalar) (supported : tsupport scalar ⊆ domain)
    (vector : Spatial → Value) (vectorContinuous : ContinuousOn vector domain) :
    Integrable (fun point => scalar point • vector point) volume :=
  (continuous_smul_of_tsupport_subset domain openDomain scalar scalarContinuous supported
    vector vectorContinuous).integrable_of_hasCompactSupport compact.smul_right

theorem setIntegral_eq_integral_smul_of_tsupport_subset {Value : Type*}
    [NormedAddCommGroup Value] [NormedSpace ℝ Value]
    (domain : Set Spatial) (scalar : Spatial → ℝ) (supported : tsupport scalar ⊆ domain)
    (vector : Spatial → Value) :
    (∫ point in domain, scalar point • vector point) = ∫ point, scalar point • vector point := by
  have equality :
      (∫ point in domain, scalar point • vector point) =
        ∫ point in Set.univ, scalar point • vector point := by
    symm
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero MeasurableSet.univ
      (Set.subset_univ domain)
    intro point outside
    have scalarZero : scalar point = 0 := by
      by_contra nonzero
      exact outside.2 (supported (subset_tsupport scalar nonzero))
    rw [scalarZero, zero_smul]
  simpa only [Measure.restrict_univ] using equality

theorem differentiate_eq_ordered (direction : Fin 2) (test : Spatial → ℝ) :
    Grad.WeakTesting.Commutation.differentiate direction test =
      Grad.WeakTesting.orderedTestDerivative 1 (fun _ => direction) test := by
  funext point
  change fderiv ℝ test point (spatialDirection direction) =
    iteratedFDeriv ℝ 1 test point (fun _ => spatialDirection direction)
  rw [iteratedFDeriv_one_apply]

theorem differentiate_compact (direction : Fin 2) (test : Spatial → ℝ)
    (compact : HasCompactSupport test) :
    HasCompactSupport (Grad.WeakTesting.Commutation.differentiate direction test) := by
  rw [differentiate_eq_ordered direction test]
  exact Grad.WeakTesting.orderedTestDerivative_hasCompactSupport 1 (fun _ => direction) test compact

theorem differentiate_support (direction : Fin 2) (test : Spatial → ℝ) :
    tsupport (Grad.WeakTesting.Commutation.differentiate direction test) ⊆ tsupport test := by
  rw [differentiate_eq_ordered direction test]
  exact Grad.WeakTesting.orderedTestDerivative_support_subset 1 (fun _ => direction) test

theorem firstDerivative_ibp (domain : Set Spatial) (openDomain : IsOpen domain)
    (test : Spatial → ℝ) (testSmooth : ContDiff ℝ ∞ test)
    (testCompact : HasCompactSupport test) (testSupported : tsupport test ⊆ domain)
    (function : Spatial → ℂ) (functionSmooth : ContDiffOn ℝ ∞ function domain)
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

theorem listDerivative_append_test (first second : List (Fin 2)) (test : Spatial → ℝ) :
    Grad.WeakTesting.Commutation.listDerivative (first ++ second) test =
      Grad.WeakTesting.Commutation.listDerivative first
        (Grad.WeakTesting.Commutation.listDerivative second test) := by
  simp only [Grad.WeakTesting.Commutation.listDerivative, List.foldr_append]

theorem listDerivative_ibp (domain : Set Spatial) (openDomain : IsOpen domain)
    (derivatives : List (Fin 2)) (test : Spatial → ℝ)
    (testSmooth : ContDiff ℝ ∞ test) (testCompact : HasCompactSupport test)
    (testSupported : tsupport test ⊆ domain) (function : Spatial → ℂ)
    (functionSmooth : ContDiffOn ℝ ∞ function domain) :
    (∫ point in domain, test point • listDerivative derivatives function point) =
      (-1 : ℂ) ^ derivatives.length * ∫ point in domain,
        Grad.WeakTesting.Commutation.listDerivative derivatives test point • function point := by
  induction derivatives generalizing test with
  | nil => simp [Grad.WeakTesting.Commutation.listDerivative, listDerivative]
  | cons direction rest induction =>
      let testDerivative := Grad.WeakTesting.Commutation.differentiate direction test
      have testDerivativeSmooth : ContDiff ℝ ∞ testDerivative :=
        Grad.WeakTesting.Commutation.differentiate_contDiff direction test testSmooth
      have testDerivativeCompact : HasCompactSupport testDerivative :=
        differentiate_compact direction test testCompact
      have testDerivativeSupported : tsupport testDerivative ⊆ domain :=
        (differentiate_support direction test).trans testSupported
      have restSmooth : ContDiffOn ℝ ∞ (listDerivative rest function) domain :=
        listDerivative_smooth openDomain rest functionSmooth
      have firstStep := firstDerivative_ibp domain openDomain test testSmooth testCompact testSupported
        (listDerivative rest function) restSmooth direction
      have remaining := induction testDerivative testDerivativeSmooth testDerivativeCompact
        testDerivativeSupported
      have reordered :
          Grad.WeakTesting.Commutation.listDerivative rest testDerivative =
            Grad.WeakTesting.Commutation.listDerivative (direction :: rest) test := by
        rw [show testDerivative = Grad.WeakTesting.Commutation.listDerivative [direction] test from rfl]
        rw [← listDerivative_append_test rest [direction] test]
        exact Grad.WeakTesting.Commutation.listDerivative_perm
          (List.perm_append_singleton direction rest) test testSmooth
      change (∫ point in domain, test point •
          directionDerivative direction (listDerivative rest function) point) = _
      rw [firstStep, remaining, reordered]
      simp only [List.length_cons, pow_succ]
      ring

theorem orderedScalar_ibp (domain : Set Spatial) (openDomain : IsOpen domain)
    (rank : ℕ) (word : Word rank) (test : Spatial → ℝ)
    (testSmooth : ContDiff ℝ ∞ test) (testCompact : HasCompactSupport test)
    (testSupported : tsupport test ⊆ domain) (function : Spatial → ℂ)
    (functionSmooth : ContDiffOn ℝ ∞ function domain) :
    (∫ point in domain, test point • wordDerivative rank word function point) =
      (-1 : ℂ) ^ rank * ∫ point in domain,
        Grad.WeakTesting.orderedTestDerivative rank word test point • function point := by
  have identity := listDerivative_ibp domain openDomain (List.ofFn word) test testSmooth
    testCompact testSupported function functionSmooth
  rw [Grad.WeakTesting.Commutation.listDerivative_ofFn rank word test testSmooth] at identity
  have classical := listDerivative_ofFn openDomain rank word functionSmooth
  calc
    _ = ∫ point in domain, test point • listDerivative (List.ofFn word) function point := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem openDomain.measurableSet] with point inside
      rw [classical inside]
    _ = _ := by simpa only [List.length_ofFn] using identity

end Grad.RepresentedKernel.WeakDerivatives
