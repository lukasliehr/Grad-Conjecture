import ANR48RadialEndpointIntegration

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.CircularHighRegularity
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.CircularHighWeak
open Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.GaugeCoefficients.Physical.WeightedTrace

private def outerRadialTest (lower : ℝ) (bounded : lower < 1) : ContDiffBump (1 : ℝ) where
  rIn := (1 - lower) / 4
  rOut := (1 - lower) / 2
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

private theorem outerRadialTest_support (lower : ℝ) (bounded : lower < 1) :
    tsupport (outerRadialTest lower bounded) ⊆ Ioi lower := by
  rw [(outerRadialTest lower bounded).tsupport_eq]
  intro radius inside
  change dist radius 1 ≤ (1 - lower) / 2 at inside
  rw [Real.dist_eq, abs_le] at inside
  change lower < radius
  linarith

private theorem outerRadialTest_lower (lower : ℝ) (bounded : lower < 1) :
    outerRadialTest lower bounded lower = 0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro inside
  exact (lt_irrefl lower) (outerRadialTest_support lower bounded inside)

private theorem outerRadialTest_upper (lower : ℝ) (bounded : lower < 1) :
    outerRadialTest lower bounded 1 = 1 := by
  apply (outerRadialTest lower bounded).one_of_mem_closedBall
  change dist (1 : ℝ) 1 ≤ (1 - lower) / 4
  rw [dist_self]
  linarith

private theorem radialVector_eq_zero (value : ComplexEuclidean 1)
    (vanishes : ∀ vector, inner ℂ vector value = 0) : value = 0 := by
  exact (inner_self_eq_zero (𝕜 := ℂ)).mp (vanishes value)

private theorem radialFlux_boundary_trace (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (flux : WeightedRadialH1 1 lower) (value slope : CollarL2 (ComplexEuclidean 1) lower)
    (boundary : ComplexEuclidean 1)
    (valueLaw : collarH1Coordinate (ComplexEuclidean 1) lower 0 (weightedToOrdinary 1 lower positive bounded.le flux) = value)
    (slopeLaw : collarH1Coordinate (ComplexEuclidean 1) lower 1 (weightedToOrdinary 1 lower positive bounded.le flux) = slope)
    (equation : ∀ vector,
      collarPairing lower ⟨deriv (outerRadialTest lower bounded), (contDiff_infty_iff_deriv.mp (outerRadialTest lower bounded).contDiff).2.continuous⟩ vector value +
      collarPairing lower ⟨outerRadialTest lower bounded, ((outerRadialTest lower bounded).contDiff (n := ⊤)).continuous⟩ vector slope +
      2 * (outerRadialTest lower bounded 1 • inner ℂ vector boundary) = 0) :
    weightedRadialTrace 1 lower positive bounded 1 flux + (2 : ℝ) • boundary = 0 := by
  apply radialVector_eq_zero
  intro vector
  have parts := weightedRadial_endpoint_parts 1 lower positive bounded flux vector
    (outerRadialTest lower bounded) (outerRadialTest lower bounded).contDiff
  rw [valueLaw, slopeLaw, outerRadialTest_lower, outerRadialTest_upper, zero_smul, one_smul, sub_zero] at parts
  have law := equation vector
  rw [outerRadialTest_upper, one_smul, parts] at law
  simpa only [inner_add_right, inner_smul_right, Complex.coe_smul, two_smul, two_mul] using law

/-- The actual weak flux belongs to the genuine radial graph, and its
outer trace satisfies the Robin identity inherited from the full disk form. -/
theorem weakInverse_outer_flux (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (parameter : ℝ) (source : highDiskL2) (mode : ℤ) (high : mode ∉ lowAngularModes) :
    ∃ flux : WeightedRadialH1 1 lower,
      collarH1Coordinate (ComplexEuclidean 1) lower 0 (weightedToOrdinary 1 lower positive bounded.le flux) =
        weakRadialFlux lower positive bounded.le mode parameter source ∧
      collarH1Coordinate (ComplexEuclidean 1) lower 1 (weightedToOrdinary 1 lower positive bounded.le flux) =
        weakRadialFluxDerivative lower positive bounded.le mode parameter source ∧
      weightedRadialTrace 1 lower positive bounded 1 flux +
        (2 : ℝ) • diskBoundaryFourier (highRobinWeakInverse parameter source).val (mode, 0) = 0 := by
  have existence := compactWeakPair_in_weightedCompletion 1 lower positive bounded
    (weakRadialFlux lower positive bounded.le mode parameter source)
    (weakRadialFluxDerivative lower positive bounded.le mode parameter source)
    (weakInverse_radial_flux lower positive bounded.le mode parameter source)
  obtain ⟨flux, valueLaw, slopeLaw⟩ := existence
  refine ⟨flux, valueLaw, slopeLaw, ?_⟩
  exact radialFlux_boundary_trace lower positive bounded flux _ _ _ valueLaw slopeLaw
    (fun vector => weakInverse_flux_boundary_equation lower positive bounded.le parameter source mode high vector
      (outerRadialTest lower bounded) (outerRadialTest lower bounded).contDiff
      (outerRadialTest_support lower bounded))

end Grad.CircularHighRegularity
