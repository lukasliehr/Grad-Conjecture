import ADY7OriginalLowPhysicalCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularLowEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace
open Grad.CircularHighRegularity Grad.PhaseAlgebra
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The physical fields determine the whole completed low graph. -/
theorem lowPhysicalSection_injective (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) :
    Function.Injective (fun field : lowEnergyGraph lower length positive =>
      lowPhysicalSection parameters lower length positive bounded field) := by
  intro first second same
  apply lowEnergyGraph_value_injective lower length positive
  apply lp.ext
  funext index
  apply collarScalar_injective_of_pos lower (lowStorageInverse lower positive)
    (lowPowerCurve_pos lower (7 / 4 : ℝ) positive)
  have sectionSame : lowEnergySection lower length positive bounded first index =
      lowEnergySection lower length positive bounded second index := by
    apply ContinuousMap.ext
    intro radius
    rw [← lowPhysicalSection_encode parameters lower length positive bounded first index radius,
      ← lowPhysicalSection_encode parameters lower length positive bounded second index radius]
    have physicalSame := congrArg (fun fields => fields index radius) same
    exact congrArg (fun value : ComplexEuclidean 1 => lowPhysicalFactor parameters length radius.val index • value) physicalSame
  have equality := congrArg (radialSectionL2 1 lower positive bounded.le) sectionSame
  rw [lowEnergySection_bulk, lowEnergySection_bulk] at equality
  exact equality

/-- Exact original incoming xi row, with the low amplitude and frequency retained. -/
theorem lowIncomingTrace_physical_xi (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : lowEnergyGraph lower length positive)
    (mode : LowAnnularMode) :
    lowIncomingTrace lower length positive bounded field (0, mode) =
      (lower ^ (-(7 / 4 : ℝ)) * (Real.sqrt (lowMu length lower mode.val.2))⁻¹) •
        (Real.exp (radialPhase parameters lower mode.val.2) •
          ((lowAmplitude length parameters.gamma mode * lowMu length lower mode.val.2) •
            lowPhysicalSection parameters lower length positive bounded field (0, mode)
              ⟨lower, le_rfl, bounded.le⟩)) := by
  have encoded := lowPhysicalSection_xi parameters lower length positive bounded field mode ⟨lower, le_rfl, bounded.le⟩
  rw [encoded, lowIncomingTrace_apply]
  rfl

/-- BF1-2's low carrier prerequisite: the literal complete injective graph,
its exact smooth density, its genuine bounded incoming trace, and original
physical realization are simultaneously available for every fixed collar. -/
theorem originalLowCarrier_consumer (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) :
    IsClosed (lowEnergyGraph lower length positive : Set (LowEnergyAmbient lower)) ∧
    Function.Injective (fun field : lowEnergyGraph lower length positive => field.val 0) ∧
    (LinearMap.range (lowFiniteSmoothCore lower length positive bounded)).topologicalClosure =
      (lowEnergyGraph lower length positive).restrictScalars ℝ ∧
    Function.Injective (fun field : lowEnergyGraph lower length positive =>
      lowPhysicalSection parameters lower length positive bounded field) ∧
    (∀ field : lowEnergyGraph lower length positive,
      ‖field‖ ^ 2 = ‖field.val 0‖ ^ 2 + ‖field.val 1‖ ^ 2) ∧
    (∀ field : lowEnergyGraph lower length positive,
      ‖lowIncomingTrace lower length positive bounded field‖ ≤
        (2 * lowIncomingConstant lower) * ‖field‖) ∧
    (∀ field : lowEnergyGraph lower length positive, ∀ mode : LowAnnularMode,
      lowIncomingTrace lower length positive bounded field (1, mode) =
        (lower ^ (-(7 / 4 : ℝ)) * (Real.sqrt (lowMu length lower mode.val.2))⁻¹) •
          (Real.exp (radialPhase parameters lower mode.val.2) •
            (lowRotationSymbol mode • lowPhysicalPSection parameters lower length positive bounded field mode
              ⟨lower, le_rfl, bounded.le⟩))) :=
  ⟨lowEnergyGraph_closed lower length positive,
    lowEnergyGraph_value_injective lower length positive,
    lowFiniteSmoothCore_closure lower length positive bounded,
    lowPhysicalSection_injective parameters lower length positive bounded,
    lowEnergyGraph_norm_sq lower length positive,
    lowIncomingLinear_bound lower length positive bounded,
    lowIncomingTrace_physical_p parameters lower length positive bounded⟩

end Grad.AnnularLowEnergy
