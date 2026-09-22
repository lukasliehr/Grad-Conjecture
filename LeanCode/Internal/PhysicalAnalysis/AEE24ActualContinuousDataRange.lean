import AEE23LiteralContinuousLowData

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

/-- Every actual two-component continuous modal Cauchy datum is attained. -/
theorem lowPairContinuousData_mem_range (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1) (mode : LowAnnularMode)
    (forcingFirst forcingSecond : C(ℝ, ℂ)) (initialFirst initialSecond : ℂ) :
    lowPairContinuousData lower length positive mode forcingFirst forcingSecond initialFirst initialSecond ∈
      Set.range (lowReferenceDataOperator parameters length lower lengthPositive positive bounded) := by
  obtain ⟨first, second, firstTrace, secondTrace, equations⟩ :=
    lowRadialReferenceSolution_exists parameters length lower mode positive bounded
      forcingFirst forcingSecond initialFirst initialSecond
  refine ⟨lowPairRadialGraph lower length positive bounded mode first second, ?_⟩
  apply (WithLp.prodContinuousLinearEquiv 2 ℂ (LowEnergyBulk lower) LowEnergyBoundary).injective
  apply Prod.ext
  · apply lp.ext
    funext index
    rcases index with ⟨row, other⟩
    apply collarScalar_injective_of_pos lower (lowStorageInverse lower positive)
      (lowPowerCurve_pos lower (7 / 4 : ℝ) positive)
    apply Lp.ext
    filter_upwards [lowPairRadialGraph_residual parameters length lower lengthPositive positive bounded
      mode first second forcingFirst forcingSecond equations row other,
      lowPairContinuousData_residual_ae lower length positive mode forcingFirst forcingSecond
        initialFirst initialSecond row other] with radius actual expected
    exact actual.trans expected.symm
  · apply lp.ext
    funext index
    rcases index with ⟨row, other⟩
    change lowIncomingTrace lower length positive bounded
      (lowPairRadialGraph lower length positive bounded mode first second) (row, other) =
      (lowPairContinuousData lower length positive mode forcingFirst forcingSecond initialFirst initialSecond).ofLp.2 (row, other)
    rw [lowPairRadialGraph_incoming, lowPairContinuousData_incoming, firstTrace, secondTrace]
    split_ifs <;> rfl

end Grad.AnnularLowCompletion
