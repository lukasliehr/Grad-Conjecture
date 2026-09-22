import AEK13UniformGraphKnownBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceBoundaryTrace Grad.AxisCore Grad.RealFixedRanges
open Grad.AnnularVariational Grad.AnnularCurrentEnergy
open Grad.AnnularReconstruction Grad.BoundaryKernelAction
open Grad.ActualBoundaryPrimitives Grad.ActualBoundaryInverse

attribute [local instance] Grad.AnnularCurrentEnergy.energyNormed
  Grad.AnnularCurrentEnergy.energySeminormed
  Grad.AnnularCurrentEnergy.energyRealNormed
  Grad.AnnularCurrentEnergy.energyRealModule

section DataFunctional

variable (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1 / 2)
    (lengthPositive : 0 < L) (widthHalf : parameters.gamma ≤ 1 / 2)
    (widthLength : parameters.gamma ≤ Real.sqrt 5 / (6 * L))
    (state : RetainedInverseState parameters L compact)
    (angular cell : ℕ)

/-- The graph-native known functional attached to a coherent BF2 packet. -/
def ActualHighGraphKnownData.functional
    (data : ActualHighGraphKnownData parameters lower angular cell) :
    annularEnergySpace lower L positive →L[ℝ] ℝ :=
  actualHighGraphKnownFunctional parameters L compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state angular cell data.weighted
      data.auxiliary data.graphs data.datum

/-- Restriction of the graph-native functional to zero incoming trace. -/
def ActualHighGraphKnownData.zeroFunctional
    (data : ActualHighGraphKnownData parameters lower angular cell) :
    annularInnerZero lower L positive
      (lowerHalf.trans_lt (by norm_num)) lengthPositive →L[ℝ] ℝ :=
  actualHighGraphKnownZeroFunctional parameters L compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state angular cell data.weighted
      data.auxiliary data.graphs data.datum

/-- Uniform BF13 size of a coherent graph-native packet. -/
def ActualHighGraphKnownData.functionalSize
    (data : ActualHighGraphKnownData parameters lower angular cell) : ℝ :=
  actualHighGraphKnownFunctionalSize parameters L compact lower state angular cell
    data.weighted data.auxiliary data.graphs data.datum

theorem ActualHighGraphKnownData.functional_apply_bound
    (data : ActualHighGraphKnownData parameters lower angular cell)
    (test : annularEnergySpace lower L positive) :
    ‖data.functional parameters L compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state angular cell test‖ ≤
      data.functionalSize parameters L compact lower state angular cell * ‖test‖ :=
  actualHighGraphKnownFunctional_apply_bound parameters L compact lower positive
    lowerHalf lengthPositive widthHalf widthLength state angular cell data.weighted
      data.auxiliary data.graphs data.datum test

/-- Operator norm BF13 estimate at every split grade, including `(0,0)`. -/
theorem ActualHighGraphKnownData.zeroFunctional_norm
    (data : ActualHighGraphKnownData parameters lower angular cell) :
    ‖data.zeroFunctional parameters L compact lower positive lowerHalf lengthPositive
      widthHalf widthLength state angular cell‖ ≤
      data.functionalSize parameters L compact lower state angular cell := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (actualHighGraphKnownFunctionalSize_nonnegative parameters L compact lower state
      angular cell data.weighted data.auxiliary data.graphs data.datum)
  intro test
  change ‖data.functional parameters L compact lower positive lowerHalf lengthPositive
    widthHalf widthLength state angular cell test.val‖ ≤ _
  exact data.functional_apply_bound parameters L compact lower positive lowerHalf
    lengthPositive widthHalf widthLength state angular cell test.val

/-- A legacy source-range packet forgets only its redundant ambient source
representative and becomes graph-native data. -/
def ActualHighKnownData.toGraphData
    (large : 3 ≤ angular + cell + 2)
    (data : ActualHighKnownData parameters L lower positive
      (lowerHalf.trans_lt (by norm_num)) angular cell large) :
    ActualHighGraphKnownData parameters lower angular cell where
  weighted := data.weighted
  auxiliary := data.auxiliary
  graphs := data.graphs
  datum := data.datum
  innerValue := data.innerValue
  weightedGraph := data.weightedGraph

/-- The graph-native functional is exactly the stable AEK5 functional on a
legacy compatible source-range packet. -/
theorem ActualHighKnownData.toGraphData_functional_eq
    (large : 3 ≤ angular + cell + 2)
    (data : ActualHighKnownData parameters L lower positive
      (lowerHalf.trans_lt (by norm_num)) angular cell large) :
    (data.toGraphData parameters L lower positive lowerHalf angular cell large).functional
        parameters L compact lower positive lowerHalf lengthPositive widthHalf
          widthLength state angular cell =
      data.functional parameters L compact lower positive lowerHalf lengthPositive
        widthHalf widthLength state angular cell large := by
  exact actualHighGraphKnownFunctional_eq_known parameters L compact lower positive
    lowerHalf lengthPositive widthHalf widthLength state angular cell data.weighted
      data.auxiliary data.graphs data.datum data.source.val data.outerGraph

end DataFunctional
end Grad.AnnularCurrentSource
