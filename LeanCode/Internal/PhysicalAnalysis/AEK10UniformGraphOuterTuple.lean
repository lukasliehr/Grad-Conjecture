import AEK9UniformSourceOuterTrace

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.AnnularSourceGraph

/-- Lowering an endpoint split grade is a contraction. -/
theorem annularEndpointInclusion_bound (parameters : PhaseParameters)
    (dimension : ℕ) (radius : ℝ)
    (lowAngular lowCell highAngular highCell : ℕ)
    (angularLe : lowAngular ≤ highAngular) (cellLe : lowCell ≤ highCell)
    (field : AnnularEndpointTrace parameters dimension radius highAngular highCell) :
    ‖annularEndpointInclusion parameters dimension radius lowAngular lowCell
      highAngular highCell angularLe cellLe field‖ ≤ ‖field‖ := by
  unfold annularEndpointInclusion
  simpa only [one_mul] using lpTwoMap_bound
    (sourceGradeFamily (ComplexEuclidean dimension) lowAngular lowCell
      highAngular highCell) 1 zero_le_one
    (sourceGradeFamily_bound _ _ _ _ _ angularLe cellLe) field

/-- Uniform outer estimate for the `F0` coordinate of the genuine graph. -/
theorem highGraphOuterTuple_f0_bound (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (grade : ℕ)
    (graphs : HighRadialSourceGraphs parameters lower grade) :
    ‖highGraphOuterTuple parameters lower positive
      (lowerHalf.trans_lt (by norm_num)) grade graphs 0‖ ≤
      uniformSourceOuterConstant * ‖graphs.1‖ := by
  have inclusion := annularEndpointInclusion_bound parameters 1
    (radialEndpointRadius lower 1) 0 0 1 0 (by omega) (by omega)
    (totalSourceTrace parameters 1 lower positive
      (lowerHalf.trans_lt (by norm_num)) 1 0 grade 1 graphs.1)
  have trace := annularSourceTrace_outer_uniform_bound parameters 1 lower positive
    lowerHalf 1 0 graphs.1
  exact inclusion.trans (by
    simpa only [totalSourceTrace] using trace)

/-- Uniform outer estimate for the exact normalized angular derivative
`RF0` of the same genuine `F0` graph. -/
theorem highGraphOuterTuple_rf0_bound (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (grade : ℕ)
    (graphs : HighRadialSourceGraphs parameters lower grade) :
    ‖highGraphOuterTuple parameters lower positive
      (lowerHalf.trans_lt (by norm_num)) grade graphs 1‖ ≤
      uniformSourceOuterConstant * ‖graphs.1‖ := by
  have angular := totalEndpointAngular_bound parameters 1
    (radialEndpointRadius lower 1) 0 grade
    (totalSourceTrace parameters 1 lower positive
      (lowerHalf.trans_lt (by norm_num)) 1 0 grade 1 graphs.1)
  have trace := annularSourceTrace_outer_uniform_bound parameters 1 lower positive
    lowerHalf 1 0 graphs.1
  exact angular.trans (by
    simpa only [totalSourceTrace] using trace)

/-- Uniform outer estimate for the genuine `F2` graph. -/
theorem highGraphOuterTuple_f2_bound (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2) (grade : ℕ)
    (graphs : HighRadialSourceGraphs parameters lower grade) :
    ‖highGraphOuterTuple parameters lower positive
      (lowerHalf.trans_lt (by norm_num)) grade graphs 2‖ ≤
      uniformSourceOuterConstant * ‖graphs.2‖ := by
  have trace := annularSourceTrace_outer_uniform_bound parameters 1 lower positive
    lowerHalf 0 0 graphs.2
  rw [highGraphOuterTuple_f2]
  simpa only [totalSourceTrace] using trace

/-- A three-coordinate `L2` tuple is controlled by the sum of its coordinate
norms.  This elementary helper keeps the public graph estimate transparent. -/
theorem sourceBoundaryTuple_norm_le_sum (source : SourceBoundaryTuple) :
    ‖source‖ ≤ ‖source 0‖ + ‖source 1‖ + ‖source 2‖ := by
  have sourceSq := PiLp.norm_sq_eq_of_L2
    (fun _ : Fin 3 => SourceBoundary 1) source
  rw [Fin.sum_univ_three] at sourceSq
  apply (sq_le_sq₀ (norm_nonneg source)
    (add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))).mp
  rw [sourceSq]
  nlinarith [mul_nonneg (norm_nonneg (source 0)) (norm_nonneg (source 1)),
    mul_nonneg (norm_nonneg (source 0)) (norm_nonneg (source 2)),
    mul_nonneg (norm_nonneg (source 1)) (norm_nonneg (source 2))]

/-- The literal `(F0,RF0,F2)` outer tuple is uniformly controlled by the two
genuine radial source graph norms, with no inner-radius loss. -/
theorem highGraphOuterTuple_uniform_bound (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (grade : ℕ) (graphs : HighRadialSourceGraphs parameters lower grade) :
    ‖highGraphOuterTuple parameters lower positive
      (lowerHalf.trans_lt (by norm_num)) grade graphs‖ ≤
      uniformSourceOuterConstant *
        (2 * ‖graphs.1‖ + ‖graphs.2‖) := by
  have tuple := sourceBoundaryTuple_norm_le_sum
    (highGraphOuterTuple parameters lower positive
      (lowerHalf.trans_lt (by norm_num)) grade graphs)
  have f0 := highGraphOuterTuple_f0_bound parameters lower positive lowerHalf grade graphs
  have rf0 := highGraphOuterTuple_rf0_bound parameters lower positive lowerHalf grade graphs
  have f2 := highGraphOuterTuple_f2_bound parameters lower positive lowerHalf grade graphs
  calc
    _ ≤ ‖highGraphOuterTuple parameters lower positive
          (lowerHalf.trans_lt (by norm_num)) grade graphs 0‖ +
        ‖highGraphOuterTuple parameters lower positive
          (lowerHalf.trans_lt (by norm_num)) grade graphs 1‖ +
        ‖highGraphOuterTuple parameters lower positive
          (lowerHalf.trans_lt (by norm_num)) grade graphs 2‖ := tuple
    _ ≤ uniformSourceOuterConstant * ‖graphs.1‖ +
        uniformSourceOuterConstant * ‖graphs.1‖ +
        uniformSourceOuterConstant * ‖graphs.2‖ :=
      add_le_add (add_le_add f0 rf0) f2
    _ = uniformSourceOuterConstant *
        (2 * ‖graphs.1‖ + ‖graphs.2‖) := by ring

end Grad.AnnularCurrentSource
