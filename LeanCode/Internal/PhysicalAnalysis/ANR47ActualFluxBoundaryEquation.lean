import ANR46ActualBoundaryForm

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarRestriction Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.BoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

private theorem normalize_boundary_form (period : ℝ) (nonzero : period ≠ 0) (first second boundary : ℂ)
    (law : period • (first + second) + 2 * (period • boundary) = 0) :
    first + second + 2 * boundary = 0 := by
  rw [two_mul] at law ⊢
  have combined : period • (first + second + (boundary + boundary)) = 0 := by
    simpa only [smul_add] using law
  exact (smul_eq_zero.mp combined).resolve_left nonzero

private theorem combine_gradient_forcing (period : ℝ) (gradient laplacian first second third flux forcing : ℂ)
    (gradientLaw : gradient = period • (first + second)) (laplacianLaw : laplacian = period • third)
    (fluxLaw : flux = first) (forcingLaw : forcing = second + third) :
    gradient + laplacian = period • (flux + forcing) := by
  rw [gradientLaw, laplacianLaw, fluxLaw, forcingLaw]
  simp only [smul_add]
  abel

/-- Exact radial boundary identity inherited from AN18, expressed in the
same genuine weak flux and its L2 derivative. The boundary test is allowed
to be nonzero at r=1. -/
theorem weakInverse_flux_boundary_equation (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameter : ℝ) (source : highDiskL2) (mode : ℤ) (high : mode ∉ lowAngularModes)
    (vector : ComplexEuclidean 1) (test : ℝ → ℝ) (smooth : ContDiff ℝ ∞ test)
    (supported : tsupport test ⊆ Ioi lower) :
    collarPairing lower ⟨deriv test, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩ vector
      (weakRadialFlux lower positive bounded mode parameter source) +
    collarPairing lower ⟨test, smooth.continuous⟩ vector
      (weakRadialFluxDerivative lower positive bounded mode parameter source) +
    2 * (test 1 • inner ℂ vector (diskBoundaryFourier (highRobinWeakInverse parameter source).val (mode, 0))) = 0 := by
  let field := (highRobinWeakInverse parameter source).val
  let jet := boundaryCharacterJet mode vector test smooth (collarSupport_away lower positive test supported)
  let testMap : C(ℝ, ℝ) := ⟨test, smooth.continuous⟩
  let derivativeMap : C(ℝ, ℝ) := ⟨deriv test, (contDiff_infty_iff_deriv.mp smooth).2.continuous⟩
  let firstMap : C(ℝ, ℝ) := ⟨fun radius => radius * deriv test radius, continuous_id.mul derivativeMap.continuous⟩
  let secondMap : C(ℝ, ℝ) := testMap * radialPotentialCurve lower positive mode
  let thirdMap : C(ℝ, ℝ) := ⟨fun radius => radius * test radius, continuous_id.mul smooth.continuous⟩
  let value := diskRadialValue lower positive bounded mode field
  let slope := diskRadialSlope lower positive bounded mode field
  let laplacian := weakRadialLaplacian lower positive bounded mode parameter source
  have firstProduct : derivativeMap * radialRadiusCurve = firstMap := by
    apply ContinuousMap.ext
    intro radius
    exact mul_comm _ _
  have thirdProduct : testMap * radialRadiusCurve = thirdMap := by
    apply ContinuousMap.ext
    intro radius
    exact mul_comm _ _
  have fluxLaw : collarPairing lower derivativeMap vector
      (weakRadialFlux lower positive bounded mode parameter source) =
      collarPairing lower firstMap vector slope :=
    (collarScalar_pairing 1 lower radialRadiusCurve derivativeMap vector slope).trans
      (congrArg (fun profile : C(ℝ, ℝ) => collarPairing lower profile vector slope) firstProduct)
  have forceAddition := (collarPairing lower testMap vector).map_add
    (collarScalar 1 lower (radialPotentialCurve lower positive mode) value)
    (collarScalar 1 lower radialRadiusCurve laplacian)
  have forceFirst := collarScalar_pairing 1 lower (radialPotentialCurve lower positive mode) testMap vector value
  have forceSecond := (collarScalar_pairing 1 lower radialRadiusCurve testMap vector laplacian).trans
    (congrArg (fun profile : C(ℝ, ℝ) => collarPairing lower profile vector laplacian) thirdProduct)
  have forcingLaw : collarPairing lower testMap vector (weakRadialFluxDerivative lower positive bounded mode parameter source) =
      collarPairing lower secondMap vector value + collarPairing lower thirdMap vector laplacian :=
    forceAddition.trans (congrArg₂ (fun first second : ℂ => first + second) forceFirst forceSecond)
  have gradientLaw := boundaryCharacter_gradient_completed lower positive bounded mode vector test smooth supported field
  have laplacianLaw := boundaryCharacterJet_ordinary lower positive bounded mode vector test smooth supported
    (weakLaplacianValue parameter source)
  have combined := combine_gradient_forcing (2 * Real.pi) _ _ _ _ _ _ _ gradientLaw laplacianLaw fluxLaw forcingLaw
  have boundaryLaw := boundaryCharacter_boundary_pairing mode vector test smooth
    (collarSupport_away lower positive test supported) field
  have transformed := congrArg₂ (fun first boundary : ℂ => first + 2 * boundary) combined boundaryLaw
  have actual := weakInverse_boundary_form parameter source mode high vector test smooth
    (collarSupport_away lower positive test supported)
  have scaled := transformed.symm.trans actual
  exact normalize_boundary_form (2 * Real.pi) (by positivity) _ _ _ scaled

end Grad.CircularHighRegularity
