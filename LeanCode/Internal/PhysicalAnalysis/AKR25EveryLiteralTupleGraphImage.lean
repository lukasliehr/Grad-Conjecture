import AKR24ActualFullTupleResidualGraphs

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

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (tuple : OriginalSmoothTuple parameters lower)

/-- Every literal admissible four-field tuple has its actual five-block
image, including both genuine copied H1 sources and computed full residuals. -/
def originalTupleGraphImage : OriginalFiveBlockAmbient parameters lower length positive :=
  WithLp.toLp 2 (tupleOriginalRetained parameters lower length positive bounded tuple,
    WithLp.toLp 2 (WithLp.toLp 2
      (tupleOriginalSourceGraph parameters lower positive bounded tuple 2 1 0,
       tupleOriginalSourceGraph parameters lower positive bounded tuple 3 0 0),
      WithLp.toLp 2 (tupleOriginalF1 parameters length compact lower positive bounded state tuple,
        tupleOriginalG3 parameters length compact lower positive bounded state tuple)))

theorem originalTupleGraphImage_represents (lengthPositive : 0 < length) :
    OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple
      (originalTupleGraphImage parameters length compact lower positive bounded state tuple) := by
  constructor
  · exact tupleWeightedRetained_pressure parameters lower length positive bounded tuple lengthPositive
  · exact fun radius mode => (tupleWeightedRetained_Xi parameters lower length positive bounded tuple lengthPositive radius mode).symm
  · filter_upwards [tupleSourceF0_physical parameters lower positive bounded tuple] with radius same
    exact fun mode => (same mode).symm
  · filter_upwards [tupleSourceF2_physical parameters lower positive bounded tuple] with radius same
    exact fun mode => (same mode).symm
  · filter_upwards [tupleOriginalF1_physical parameters length compact lower positive bounded state tuple] with radius same
    exact fun inside mode => (same inside mode).symm
  · filter_upwards [tupleOriginalG3_physical parameters length compact lower positive bounded state tuple] with radius same
    exact fun inside mode => (same inside mode).symm

/-- Totality on the original c <= min(1/2,L) domain. The image is constructed
from the literal tuple; no PDE or residual graph premise narrows this domain. -/
theorem everyOriginalSmoothTuple_hasGraphImage (domain : lower ≤ min (1/2) length)
    (lengthPositive : 0 < length) :
    ∃ point : OriginalFiveBlockAmbient parameters lower length positive,
      OriginalTupleObservation parameters length compact lower positive
        ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) lengthPositive state tuple point :=
  ⟨originalTupleGraphImage parameters length compact lower positive
    ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) state tuple,
    originalTupleGraphImage_represents parameters length compact lower positive
      ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) state tuple lengthPositive⟩

theorem originalTupleGraphImage_mem_core (domain : lower ≤ min (1/2) length) (lengthPositive : 0 < length) :
    originalTupleGraphImage parameters length compact lower positive
      ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) state tuple ∈
      CoreAnn parameters length compact lower positive domain lengthPositive state :=
  ⟨tuple,originalTupleGraphImage_represents parameters length compact lower positive
    ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) state tuple lengthPositive⟩

end Grad.AnnularOriginalCoreRealization
