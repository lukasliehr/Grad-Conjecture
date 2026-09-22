import AKR26FaithfulOriginalRetainedGraph

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

variable {parameters : PhaseParameters} {length compact lower : ℝ} {positive : 0 < lower} {bounded : lower < 1}
    {lengthPositive : 0 < length} {state : RetainedInverseState parameters length compact}
    {tuple : OriginalSmoothTuple parameters lower}

theorem originalTupleObservation_unique {first second : OriginalFiveBlockAmbient parameters lower length positive}
    (firstSame : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple first)
    (secondSame : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple second) :
    first = second := by
  have retained : first.ofLp.1 = second.ofLp.1 := by
    apply (originalCoupledEquivalence parameters lower length positive bounded.le lengthPositive).injective
    apply sameCoupledCoefficients_faithful parameters lower length positive bounded lengthPositive
    · exact fun radius mode => (firstSame.scalar radius mode).symm.trans (secondSame.scalar radius mode)
    · intro radius mode
      by_cases zero : mode.1 = 0
      · rcases mode with ⟨angular,cell⟩
        change angular = 0 at zero
        subst angular
        rw [sameCoupledXCoefficient_meanZero,sameCoupledXCoefficient_meanZero]
      · have same := (firstSame.pressure radius mode).symm.trans (secondSame.pressure radius mode)
        have nonzero : angularInverseMultiplier mode ≠ 0 := by
          rw [angularInverseMultiplier,if_neg zero]
          exact inv_ne_zero (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr zero))
        exact smul_right_injective (ComplexEuclidean 1) nonzero same
  exact (WithLp.equiv 2 _).injective (Prod.ext retained (firstSame.sourceBlocks_unique secondSame))

/-- There is one exact graph image for every original tuple; retained and
source derivative coordinates admit no independent choices. -/
theorem everyOriginalSmoothTuple_hasUniqueGraphImage
    (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (domain : lower ≤ min (1/2) length) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) (tuple : OriginalSmoothTuple parameters lower) :
    ∃! point : OriginalFiveBlockAmbient parameters lower length positive,
      OriginalTupleObservation parameters length compact lower positive
        ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) lengthPositive state tuple point := by
  let bounded : lower < 1 := (domain.trans (min_le_left _ _)).trans_lt (by norm_num)
  refine ⟨originalTupleGraphImage parameters length compact lower positive bounded state tuple,
    originalTupleGraphImage_represents parameters length compact lower positive bounded state tuple lengthPositive, ?_⟩
  intro point represented
  exact originalTupleObservation_unique represented
    (originalTupleGraphImage_represents parameters length compact lower positive bounded state tuple lengthPositive)

theorem coreAnn_eq_totalTupleRange (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (domain : lower ≤ min (1/2) length) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) :
    CoreAnn parameters length compact lower positive domain lengthPositive state =
      Set.range (originalTupleGraphImage parameters length compact lower positive
        ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) state) := by
  ext point
  constructor
  · rintro ⟨tuple,represented⟩
    refine ⟨tuple,?_⟩
    exact originalTupleObservation_unique
      (originalTupleGraphImage_represents parameters length compact lower positive
        ((domain.trans (min_le_left _ _)).trans_lt (by norm_num)) state tuple lengthPositive) represented
  · rintro ⟨tuple,rfl⟩
    exact originalTupleGraphImage_mem_core parameters length compact lower positive state tuple domain lengthPositive

end Grad.AnnularOriginalCoreRealization
