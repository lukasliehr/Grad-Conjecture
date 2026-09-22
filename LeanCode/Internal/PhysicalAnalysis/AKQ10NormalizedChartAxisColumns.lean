import AKQ9ActualOriginalAxisFrame
import AXC4ActualExtraction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.SourceCollar Grad.SourceCollarCoefficients
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.AxisSplit Grad.ChartAxisSplit
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical Grad.GaugeCoefficients.Physical.Frame
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.RadialLedger Grad.NonlinearDivision

def planarReferenceCore (parameters : PhaseParameters) : ACore parameters 3 :=
  Grad.NonlinearQuotientBounds.valueMapCore parameters tamePlanarInclusion (tamePlanarCoordinateField parameters)

/-- SC2 takes displacement from iota*y; the normalized chart stores the
total physical field. This subtraction is essential to the same A0=aM. -/
def normalizedChartDisplacement (parameters : PhaseParameters) (seed : Seed.Parameters)
    (inside : seed ∈ Seed.parameterDomain) (state : ChartState parameters) : ACore parameters 3 :=
  (normalizedChart parameters seed inside state).1 - planarReferenceCore parameters

theorem normalizedChartDisplacement_axis_zero (parameters : PhaseParameters) (seed : Seed.Parameters)
    (inside : seed ∈ Seed.parameterDomain) (state : ChartState parameters)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (state.2.1.val cell)) (cell : ℤ) :
    ((normalizedChartDisplacement parameters seed inside state).val cell).value closedOrigin = 0 := by
  change originValue ((normalizedChartDisplacement parameters seed inside state).val cell) = 0
  rw [normalizedChartDisplacement,acore_val_sub,originValue_sub,
    normalizedChart_origin_zero seed inside state zeroJets]
  rw [planarReferenceCore,valueMapCore_originValue,tamePlanarCoordinate_origin_zero,map_zero,sub_zero]

theorem originalPlanarDerivative_eq_coreValue (parameters : PhaseParameters) (field : ACore parameters 3)
    (direction : Fin 2) (point : ClosedDisk) (angle : ℝ) :
    ordinaryDerivativeExtension (originalCoefficientCore parameters field) (fun _ : Fin 1 => direction) 0
      (point,(angle : CellCircle)) = coreValue (partialCore parameters direction field) point angle := by
  rw [← (originalDerivative_hasSum parameters field (fun _ : Fin 1 => direction) 0 angle point).tsum_eq]
  unfold coreValue
  apply tsum_congr
  intro cell
  rw [apFourierPhase_eq]
  simp only [cellDerivativeFactor,pow_zero,one_smul]
  rfl

theorem originalFrame_planarColumn (parameters : PhaseParameters) (length epsilon : ℝ)
    (field : ACore parameters 3) (point : ClosedDisk) (angle : ℝ) (direction : Fin 2) (row : Fin 3) :
    originalPhysicalFrameMatrix parameters length epsilon field angle point row direction.castSucc =
      (tamePlanarInclusion (EuclideanSpace.single direction 1) +
        coreValue (partialCore parameters direction field) point angle) row := by
  have first : ordinaryDerivativeExtension (originalCoefficientCore parameters field) firstPlanarDerivativeWord 0
      (point,(angle : CellCircle)) = coreValue (partialCore parameters 0 field) point angle :=
    originalPlanarDerivative_eq_coreValue parameters field 0 point angle
  have second : ordinaryDerivativeExtension (originalCoefficientCore parameters field) secondPlanarDerivativeWord 0
      (point,(angle : CellCircle)) = coreValue (partialCore parameters 1 field) point angle :=
    originalPlanarDerivative_eq_coreValue parameters field 1 point angle
  unfold originalPhysicalFrameMatrix originalPhysicalFrameDeviation
  dsimp only
  rw [operatorMatrix_add,referenceFrame_matrix]
  fin_cases direction <;> fin_cases row <;>
    simp [operatorMatrix,columnEmbedding_apply,tamePlanarInclusion,first,second]

/-- Both actual planar columns at the axis are the supplied AM columns
a*iota(M e_j)+e_T*tau_j, for the SAME normalized chart displacement. -/
theorem normalizedChartDisplacement_planarColumn (parameters : PhaseParameters) (length epsilon : ℝ)
    (seed : Seed.Parameters) (inside : seed ∈ Seed.parameterDomain) (state : ChartState parameters)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (state.2.1.val cell))
    (angle : ℝ) (direction : Fin 2) (row : Fin 3) :
    originalPhysicalFrameMatrix parameters length epsilon
      (normalizedChartDisplacement parameters seed inside state) angle closedOrigin row direction.castSucc =
      (coefficientValue (rootChart state.1) angle •
        tamePlanarInclusion (harmonicSeedOperator (seed 0) (seed 1) (seed 2) (seed 3) angle
          (EuclideanSpace.single direction 1)) +
        tameTangentInclusion (planarValue state.1 angle direction • EuclideanSpace.single 0 1)) row := by
  rw [originalFrame_planarColumn]
  change (tamePlanarInclusion (EuclideanSpace.single direction 1) +
    coreValue (partialCore parameters direction (normalizedChartDisplacement parameters seed inside state)) originPoint angle) row = _
  rw [normalizedChartDisplacement,map_sub,coreValue_subtract,normalizedChart_firstJet seed inside state zeroJets,
    planarReferenceCore,partialCore_valueMap,coreValue_valueMap,axisDerivative_tamePlanarCoordinate]
  have cancel (first second : ComplexEuclidean 3) : first + (second - first) = second := by abel
  rw [cancel]

end Grad.FinitePhysicalJetLift
