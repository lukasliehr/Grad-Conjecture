import AKR36TotalOriginalSmoothCoreLinearMap

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore Grad.AnnularReconstruction Grad.AnnularSmoothCore Grad.PhaseAlgebra
open Grad.AnnularOriginalHigh Grad.AnnularOriginalLow Grad.AnnularLowEnergy Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.GaugeCoefficients.Physical.WeightedTrace

open Grad.AnnularWeightedSmoothness Grad.GaugeCoefficients.Physical.Ledger

open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularHighTilt

open Grad.AnnularFullGraph

open Grad.AnnularHighRadial Grad.AnnularTiltedReference Grad.AnnularOmegaGraph Grad.CircularHighRegularity

open Grad.AnnularCurrentLow
open Grad.AnnularCurrentSource
open Grad.AnnularStrongData
open Grad.AnnularForwardDatum Grad.AnnularForwardTraces Grad.AnnularStrongOrbit
open Grad.GaugeCoefficients.Physical.Allocation

attribute [local instance] traceOriginalRealNormed traceOriginalRealModule originalAmbientRealNormed
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule
  forwardBoundaryRealNormed forwardBoundaryRealModule

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (domain : lower ≤ min (1/2) length) (lengthPositive : 0 < length)
    (widthHalf : parameters.gamma ≤ 1/2) (widthLength : parameters.gamma ≤ Real.sqrt 5/(6*length))
    (state : RetainedInverseState parameters length compact)
    (small : physicalBudget parameters state.val.val.field state.val.val.rho state.val.val.epsilon 8 ≤ coupledPrimitiveRadius parameters length compact)

def literalOriginalCoreGraphMap := originalTupleGraphLinear parameters length compact lower positive
  ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) lengthPositive state

theorem literalOriginalCoreGraphMap_range :
    Set.range (literalOriginalCoreGraphMap parameters length compact lower positive domain lengthPositive state) =
      CoreAnn parameters length compact lower positive domain lengthPositive state :=
  (coreAnn_eq_totalTupleRange parameters length compact lower positive domain lengthPositive state).symm

include small in
/-- Closure of the TOTAL literal original smooth core in the five original
norms is exactly the observed original equation graph. Totality is now proved
for every admissible tuple, rather than inserted into the core predicate. -/
theorem totalOriginalCoreClosure_eq_originalEquationGraph :
    closure (Set.range (literalOriginalCoreGraphMap parameters length compact lower positive domain lengthPositive state)) =
      OriginalObservedEquationGraph parameters length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive
        widthHalf widthLength state := by
  rw [literalOriginalCoreGraphMap_range]
  exact representedCoreClosure_eq_originalObservedEquationGraph parameters length compact lower positive domain lengthPositive
    widthHalf widthLength state small

include small in
theorem everyLiteralTuple_originalEquation (tuple : OriginalSmoothTuple parameters lower) :
    literalOriginalCoreGraphMap parameters length compact lower positive domain lengthPositive state tuple ∈
      OriginalObservedEquationGraph parameters length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive
        widthHalf widthLength state :=
  coreAnn_subset_originalObservedEquationGraph parameters length compact lower positive domain lengthPositive
    widthHalf widthLength state small
    (originalTupleGraphImage_mem_core parameters length compact lower positive state tuple domain lengthPositive)

include small in
/-- The completed total core has the same bounded canonical datum recovery;
no independent incoming data are attached to an arbitrary smooth tuple. -/
theorem totalOriginalCoreClosure_recovery (point : OriginalFiveBlockAmbient parameters lower length positive)
    (inside : point ∈ closure (Set.range (literalOriginalCoreGraphMap parameters length compact lower positive domain lengthPositive state))) :
    let pair := originalForwardPair parameters length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive state point
    OriginalStrongCoupledEquation parameters length compact lower positive (domain.trans (min_le_left _ _)) lengthPositive
      widthHalf widthLength state pair.1 pair.2 ∧ originalFiveBlockObservation parameters lower length positive pair = point := by
  apply representedCoreClosure_recovery parameters length compact lower positive domain lengthPositive widthHalf widthLength state small point
  simpa only [literalOriginalCoreGraphMap_range,CoreAnnClosure] using inside

end Grad.AnnularOriginalCoreRealization
