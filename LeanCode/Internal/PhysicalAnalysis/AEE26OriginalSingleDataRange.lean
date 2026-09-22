import AEE25OriginalSmoothDataDensity

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

theorem lowContinuousSingleSource_mem_range (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (index : LowAnnularIndex) (curve : C(ℝ, ℂ)) :
    lowBulkSingleData lower index (lowScalarStoredCurve lower positive curve) ∈
      Set.range (lowReferenceDataOperator parameters length lower lengthPositive positive bounded) := by
  rcases index with ⟨row, mode⟩
  have rowCases : row = 0 ∨ row = 1 := by omega
  rcases rowCases with rfl | rfl
  · simpa [lowPairContinuousData, lowBulkSingleData, lowBulkDataInjection, lowScalarStoredCurve_zero] using
      lowPairContinuousData_mem_range parameters length lower lengthPositive positive bounded mode curve 0 0 0
  · simpa [lowPairContinuousData, lowBulkSingleData, lowBulkDataInjection, lowScalarStoredCurve_zero] using
      lowPairContinuousData_mem_range parameters length lower lengthPositive positive bounded mode 0 curve 0 0

theorem lowBoundarySingle_mem_range (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (index : LowAnnularIndex) (value : ComplexEuclidean 1) :
    lowBoundarySingleData lower index value ∈
      Set.range (lowReferenceDataOperator parameters length lower lengthPositive positive bounded) := by
  rcases index with ⟨row, mode⟩
  obtain ⟨initial, initialLaw⟩ := scalarOne_surjective ((lowIncomingFactor lower length mode)⁻¹ • value)
  have corrected : lowIncomingFactor lower length mode • scalarOne initial = value := by
    rw [initialLaw, smul_smul, mul_inv_cancel₀ (lowIncomingFactor_pos lower length positive mode).ne', one_smul]
  have rowCases : row = 0 ∨ row = 1 := by omega
  rcases rowCases with rfl | rfl
  · simpa [lowPairContinuousData, lowBoundarySingleData, lowBoundaryDataInjection, lowScalarStoredCurve_zero, corrected] using
      lowPairContinuousData_mem_range parameters length lower lengthPositive positive bounded mode 0 0 initial 0
  · simpa [lowPairContinuousData, lowBoundarySingleData, lowBoundaryDataInjection, lowScalarStoredCurve_zero, corrected] using
      lowPairContinuousData_mem_range parameters length lower lengthPositive positive bounded mode 0 0 0 initial

/-- Completion of the actual source class inside the already proved closed range. -/
theorem lowBulkSingle_mem_range (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (index : LowAnnularIndex) (value : CollarL2 (ComplexEuclidean 1) lower) :
    lowBulkSingleData lower index value ∈
      Set.range (lowReferenceDataOperator parameters length lower lengthPositive positive bounded) := by
  apply isClosed_property (lowSmoothStoredSource_denseRange lower positive)
    ((lowReferenceDataOperator_closed_range parameters length lower lengthPositive positive bounded).preimage
      (lowBulkSingleData lower index).continuous) _ value
  intro core
  rw [lowSmoothStoredSource_actual]
  exact lowContinuousSingleSource_mem_range parameters length lower lengthPositive positive bounded index _

end Grad.AnnularLowCompletion
