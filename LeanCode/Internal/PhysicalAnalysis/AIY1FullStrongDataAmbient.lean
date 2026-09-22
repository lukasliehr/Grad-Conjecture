import AIS5SingleHilbertNormBF13
import AIR8ExactKnownLowResponseConsumer

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace Grad.AnnularStrongData
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentSource Grad.AnnularKnownLow Grad.AnnularLowEnergy

/-- One shared source tuple.  The seven bulk slots of the existing balanced
ambient are read as `(F0,RF0,F2,f)` and `(g,Rg,0)`; the final zero slot is
imposed below, so it contributes nothing to the literal six-row BF4 norm.
The two radial source graphs occur once.  The second summand is the genuine
BE18 incoming low coordinate, without an extra radial tilt. -/
abbrev StrongDataAmbient (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) :=
  WithLp 2 (ActualHighKnownAmbient parameters lower angular cell × LowEnergyBoundary)

def strongSharedProjection (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) : StrongDataAmbient parameters lower angular cell →L[ℝ]
      ActualHighKnownAmbient parameters lower angular cell :=
  (ContinuousLinearMap.fst ℝ _ _).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap

def strongLowIncomingProjection (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) : StrongDataAmbient parameters lower angular cell →L[ℝ]
      LowEnergyBoundary :=
  (ContinuousLinearMap.snd ℝ _ _).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap

/-- The angular relation uses the actual unbounded symbol `i m`, checked
mode by mode against the independent completed `Rg` row.  It imposes no
radial derivative of `g`. -/
def strongAngularResidual (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) (mode : ℤ × ℤ) :
    StrongDataAmbient parameters lower angular cell →L[ℝ] RadialL2 1 lower :=
  ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => RadialL2 1 lower) 2 mode).restrictScalars ℝ).comp
      ((highKnownWeightedQc parameters lower angular cell).comp
        (strongSharedProjection parameters lower angular cell)) -
    (((Complex.I * (mode.1 : ℂ)) •
      lp.evalCLM ℂ (fun _ : ℤ × ℤ => RadialL2 1 lower) 2 mode).restrictScalars ℝ).comp
      ((highKnownWeightedG parameters lower angular cell).comp
        (strongSharedProjection parameters lower angular cell))

def strongAngularCarrier (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) : Submodule ℝ (StrongDataAmbient parameters lower angular cell) :=
  ⨅ mode : ℤ × ℤ, (strongAngularResidual parameters lower angular cell mode).ker

theorem strongAngularCarrier_mem_iff (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) (data : StrongDataAmbient parameters lower angular cell) :
    data ∈ strongAngularCarrier parameters lower angular cell ↔
      ∀ mode : ℤ × ℤ,
        highKnownWeightedQc parameters lower angular cell data.ofLp.1 mode =
          (Complex.I * (mode.1 : ℂ)) •
            highKnownWeightedG parameters lower angular cell data.ofLp.1 mode := by
  simp only [strongAngularCarrier, Submodule.mem_iInf, LinearMap.mem_ker]
  change (∀ mode : ℤ × ℤ,
    highKnownWeightedQc parameters lower angular cell data.ofLp.1 mode -
      (Complex.I * (mode.1 : ℂ)) •
        highKnownWeightedG parameters lower angular cell data.ofLp.1 mode = 0) ↔ _
  simp only [sub_eq_zero]

theorem strongAngularCarrier_closed (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) :
    IsClosed (strongAngularCarrier parameters lower angular cell :
      Set (StrongDataAmbient parameters lower angular cell)) := by
  simp only [strongAngularCarrier, Submodule.coe_iInf]
  exact isClosed_iInter (fun mode =>
    (strongAngularResidual parameters lower angular cell mode).isClosed_ker)

end Grad.AnnularStrongData
