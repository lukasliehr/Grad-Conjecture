import AKU84ActualFixedReferenceLift

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2600000
set_option maxRecDepth 4000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds Grad.NonlinearDivision
open Grad.QuotientProjection Grad.NonlinearRange Grad.NonlinearProduct Grad.CompletedReality
open Grad.GaugeCoefficients.Physical.Allocation Grad.Q24Realization Grad.ExhaustionSourceAllocation
open Grad.AxisSplit Grad.AxisJet Grad.FlatSourceProjection Grad.RealFixedRanges Grad.PhysicalCoordinates
open Grad.ConstrainedTransfer Grad.ChartAxisLift Grad.ChartAxisProjections

variable (parameters : PhaseParameters) (reference : Seed.Parameters) (insideR : reference ∈ Seed.parameterDomain)
  (seed : Seed.Parameters) (insideS : seed ∈ Seed.parameterDomain) (base : RealJointCore parameters reference insideR)

def actualFiniteCurrentChart : ChartState parameters :=
  physicalFixedReferenceTransfer parameters reference insideR seed insideS (smoothingChartCore parameters base.2.val)

def actualFiniteCurrentField : ACore parameters 3 :=
  normalizedChartDisplacement parameters seed insideS (actualFiniteCurrentChart parameters reference insideR seed insideS base)

def actualFiniteCurrentScalar : ACore parameters 1 :=
  (normalizedChart parameters seed insideS (actualFiniteCurrentChart parameters reference insideR seed insideS base)).2

theorem actualFiniteCurrentChart_zeroJets :
    ∀ cell, ZeroCartesianFirstJets (((actualFiniteCurrentChart parameters reference insideR seed insideS base).2.1).val cell) :=
  toPhysicalCore_zeroJets parameters _
    (Gauges.seedTransfer_zero_first_jets parameters reference insideR seed insideS base.2.val.2.1
      (smoothState_constraints parameters reference insideR base.2).1.1)

theorem actualFiniteCurrentField_axis_zero :
    ∀ cell, ((actualFiniteCurrentField parameters reference insideR seed insideS base).val cell).value closedOrigin = 0 :=
  normalizedChartDisplacement_axis_zero parameters seed insideS _
    (actualFiniteCurrentChart_zeroJets parameters reference insideR seed insideS base)

theorem actualFiniteCurrentField_total :
    planarReferenceCore parameters+actualFiniteCurrentField parameters reference insideR seed insideS base =
      (normalizedChart parameters seed insideS (actualFiniteCurrentChart parameters reference insideR seed insideS base)).1 := by
  unfold actualFiniteCurrentField normalizedChartDisplacement
  abel

theorem actualFiniteCurrentState_eq :
    physicalReferenceState parameters reference insideR seed insideS (realJointCoreToJoint parameters reference insideR base) =
      ((base.1 : ℂ),planarReferenceCore parameters+actualFiniteCurrentField parameters reference insideR seed insideS base,
        actualFiniteCurrentScalar parameters reference insideR seed insideS base) := by
  rw [actualFiniteCurrentField_total]
  rfl

theorem actualFiniteCurrent_real
    (axis : ChartAxisCondition (smoothingChartCore parameters base.2.val)) :
    cartesianCoreConjugation parameters (planarReferenceCore parameters+actualFiniteCurrentField parameters reference insideR seed insideS base) =
      planarReferenceCore parameters+actualFiniteCurrentField parameters reference insideR seed insideS base := by
  rw [actualFiniteCurrentField_total]
  apply (normalizedChart_real seed insideS (actualFiniteCurrentChart parameters reference insideR seed insideS base) (stateAxis_real reference insideR base) axis ?_ ?_).1
  · change cartesianCoreConjugation parameters (toPhysicalCore parameters
      (Gauges.seedTransfer parameters reference insideR seed insideS base.2.val.2.1)) = _
    rw [toPhysicalCore_conjugate,seedTransfer_conjugate,(stateChart_real parameters reference insideR base.2).2.1]
    rfl
  · exact (stateChart_real parameters reference insideR base.2).2.2

end Grad.FinitePhysicalJetLift
