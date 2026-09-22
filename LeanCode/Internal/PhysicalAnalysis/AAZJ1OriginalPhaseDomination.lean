import AAZ18ExactPhysicalRadialConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularJointRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace









open Grad.AnnularRadialJets Grad.AnnularRegularity

/-- The exact AG12 phase lower bound follows from the original admissible
PhaseParameters witness; no extra width is introduced. -/
theorem annularPhase_lower (parameters : PhaseParameters) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (cell : ℤ) :
    (parameters.sigma0 - parameters.gamma) * cellFrequency cell ≤ radialPhase parameters radius cell := by
  rw [radialPhase_decompose]
  have frequencyPositive := cellFrequency_pos cell
  have gap := concaveGap_nonneg (radius * cellFrequency cell) (mul_nonneg nonnegative frequencyPositive.le)
  have gamma := parameters_gamma_nonnegative parameters
  have radial := mul_nonneg gamma (sub_nonneg.mpr bounded)
  have frequency := mul_nonneg radial frequencyPositive.le
  have correction := mul_nonneg gamma gap
  unfold phaseWidth
  nlinarith

theorem annularPhase_positive (parameters : PhaseParameters) (radius : ℝ)
    (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (cell : ℤ) :
    0 < radialPhase parameters radius cell :=
  (mul_pos (sub_pos.mpr (parameters_gamma_lt_sigma0 parameters)) (cellFrequency_pos cell)).trans_le
    (annularPhase_lower parameters radius nonnegative bounded cell)

theorem annularInversePhase_le_one (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (mode : HighAnnularMode) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |annularInversePhase parameters mode.val.2 radius| ≤ 1 := by
  change |Real.exp (-radialPhase parameters radius mode.val.2)| ≤ 1
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
    (annularPhase_positive parameters radius (positive.trans_le inside.1).le inside.2 mode.val.2).le)

/-- Removing the original phase is a contraction in the SAME sqrt(r)
storage, uniformly in both Fourier indices. This is derived, not assumed. -/
theorem annularUnphase_norm_le (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (mode : HighAnnularMode) (field : RadialL2 1 lower) :
    ‖collarScalar 1 lower (annularInversePhase parameters mode.val.2) field‖ ≤ ‖field‖ := by
  have bounded := annularInversePhase_le_one parameters lower positive mode
  rw [← scalarRadialMap_eq_collarScalar lower (annularInversePhase parameters mode.val.2) 1 bounded field]
  simpa only [one_mul] using scalarRadialMap_bound lower (annularInversePhase parameters mode.val.2) 1 bounded field

end Grad.AnnularJointRegularity
