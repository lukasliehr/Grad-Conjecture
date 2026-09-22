import AEE20ActualRadialReferenceSolutions

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory Function intervalIntegral
open scoped Topology NNReal Nat BigOperators ENNReal
namespace Grad.AnnularLowCompletion
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularFluxTrace Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- Both physical components of one genuine low Fourier mode. -/
def lowPairRadialGraph (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : LowAnnularMode) (first second : WeightedRadialH1 1 lower) : lowEnergyGraph lower length positive :=
  lowSingleRadialGraph lower length positive bounded (0, mode) first +
    lowSingleRadialGraph lower length positive bounded (1, mode) second

theorem lowPairRadialGraph_value (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : LowAnnularMode) (first second : WeightedRadialH1 1 lower) (row : Fin 2) (other : LowAnnularMode) :
    lowEnergyValue lower positive (row, other) (lowPairRadialGraph lower length positive bounded mode first second).val =
      if other = mode then if row = 0 then lowRadialValue lower positive bounded first
        else lowRadialValue lower positive bounded second else 0 := by
  change lowEnergyValue lower positive (row, other) (_ + _) = _
  rw [map_add, lowSingleRadialGraph_value, lowSingleRadialGraph_value]
  fin_cases row <;> by_cases same : other = mode <;> simp [same]

theorem lowPairRadialGraph_derivative (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : LowAnnularMode) (first second : WeightedRadialH1 1 lower) (row : Fin 2) (other : LowAnnularMode) :
    lowEnergyDerivative lower length positive (row, other) (lowPairRadialGraph lower length positive bounded mode first second).val =
      if other = mode then if row = 0 then lowRadialSlope lower positive bounded first
        else lowRadialSlope lower positive bounded second else 0 := by
  change lowEnergyDerivative lower length positive (row, other) (_ + _) = _
  rw [map_add, lowSingleRadialGraph_derivative, lowSingleRadialGraph_derivative]
  fin_cases row <;> by_cases same : other = mode <;> simp [same]

def lowIncomingFactor (lower length : ℝ) (mode : LowAnnularMode) : ℝ :=
  lower ^ (-(7 / 4 : ℝ)) * (Real.sqrt (lowMu length lower mode.val.2))⁻¹

theorem lowIncomingFactor_pos (lower length : ℝ) (positive : 0 < lower) (mode : LowAnnularMode) :
    0 < lowIncomingFactor lower length mode := by
  exact mul_pos (Real.rpow_pos_of_pos positive _) (inv_pos.mpr (Real.sqrt_pos.mpr (lowMu_pos length lower mode.val.2 positive)))

theorem lowPairRadialGraph_incoming (lower length : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (mode : LowAnnularMode) (first second : WeightedRadialH1 1 lower) (row : Fin 2) (other : LowAnnularMode) :
    lowIncomingTrace lower length positive bounded (lowPairRadialGraph lower length positive bounded mode first second) (row, other) =
      if other = mode then lowIncomingFactor lower length mode •
        (if row = 0 then weightedRadialTrace 1 lower positive bounded 0 first
        else weightedRadialTrace 1 lower positive bounded 0 second) else 0 := by
  unfold lowPairRadialGraph
  rw [map_add, lp.coeFn_add, Pi.add_apply, lowSingleRadialGraph_incoming, lowSingleRadialGraph_incoming]
  fin_cases row <;> by_cases same : other = mode <;> simp [same, lowIncomingFactor]

end Grad.AnnularLowCompletion
