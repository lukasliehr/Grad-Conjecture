import AIU14IndependentPhysicalSourceEquation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Grad.AnnularFullSource
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularCurrentSource Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularCrossMaps
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowVolterra Grad.AnnularCurrentLow
open Grad.CircularHighRegularity

/-- On the original independently completed low graph, the actual forward
Cauchy operator is equivalent to the genuine incoming trace and the normalized
weak derivative equation. No derivative is assigned by an inverse. -/
theorem independentLowPhysicalSource_iff (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < L)
    (state : RetainedInverseState parameters L compact)
    (data : LowEnergyData lower) (field : lowEnergyGraph lower L positive) :
    lowCurrentDataOperator parameters L compact lower lengthPositive positive bounded state field = data ↔
      lowIncomingTrace lower L positive bounded field = data.ofLp.2 ∧
      ∀ index : LowAnnularIndex,
        collarScalar 1 lower (lowMuInverseCurve lower L positive index.2.val.2)
          (lowEnergyDerivative lower L positive index field.val) =
        lowCurrentGeneratorValue parameters L compact lower lengthPositive positive bounded.le state field index +
          lowDataResidual lower positive data index := by
  constructor
  · intro equation
    have incoming := congrArg (fun result : LowEnergyData lower => result.ofLp.2) equation
    have residual := congrArg (fun result : LowEnergyData lower => result.ofLp.1) equation
    change field.val 1 - lowCurrentBulk parameters L compact lower lengthPositive positive bounded.le state (field.val 0) = data.ofLp.1 at residual
    have slope : field.val 1 = lowCurrentBulk parameters L compact lower lengthPositive positive bounded.le state (field.val 0) + data.ofLp.1 :=
      (sub_eq_iff_eq_add.mp residual).trans (add_comm _ _)
    refine ⟨incoming, ?_⟩
    intro index
    rw [lowEnergy_normalized_derivative, slope]
    change collarScalar 1 lower (lowStorageInverse lower positive) (_ + _) = _
    exact map_add _ _ _
  · rintro ⟨incoming, equations⟩
    have slope : field.val 1 = lowCurrentBulk parameters L compact lower lengthPositive positive bounded.le state (field.val 0) + data.ofLp.1 := by
      apply lp.ext
      funext index
      apply collarScalar_injective_of_pos lower (lowStorageInverse lower positive)
        (lowPowerCurve_pos lower (7 / 4 : ℝ) positive)
      have row := equations index
      rw [lowEnergy_normalized_derivative] at row
      change collarScalar 1 lower (lowStorageInverse lower positive) (field.val 1 index) =
        collarScalar 1 lower (lowStorageInverse lower positive)
          (lowCurrentBulk parameters L compact lower lengthPositive positive bounded.le state (field.val 0) index) +
        collarScalar 1 lower (lowStorageInverse lower positive) (data.ofLp.1 index) at row
      change collarScalar 1 lower (lowStorageInverse lower positive) (field.val 1 index) =
        collarScalar 1 lower (lowStorageInverse lower positive)
          (lowCurrentBulk parameters L compact lower lengthPositive positive bounded.le state (field.val 0) index + data.ofLp.1 index)
      rw [map_add]
      exact row
    apply (WithLp.prodContinuousLinearEquiv 2 ℂ (LowEnergyBulk lower) LowEnergyBoundary).injective
    apply Prod.ext
    · change field.val 1 - lowCurrentBulk parameters L compact lower lengthPositive positive bounded.le state (field.val 0) = data.ofLp.1
      rw [slope]
      abel
    · exact incoming

end Grad.AnnularFullSource
