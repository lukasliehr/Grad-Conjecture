import AJL2SmoothStoredSourceConstruction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
namespace Grad.AnnularSmoothSources
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularStrongOrbit
open Grad.AnnularCurrentSource Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularKnownLow

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (core : OriginalSmoothSourceCore parameters)

def originalSmoothF0Row : FiniteSmoothStoredRow lower
    (unweightedSourceF0Bulk parameters lower
      (originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.1.ofLp.1) :=
  (finiteGraphSmoothRow parameters 1 lower positive core.1.1.1).scalar
    (fun mode => (sourceGradeRatio 0 0 1 0 mode : ℂ)) (by
      intro mode
      change sourceGradeRatio 0 0 1 0 mode • weightedRadialCoordinate 1 lower 0
        ((originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.1.ofLp.1 mode) = _
      rw [(originalSmoothStrongData_graph_modes parameters lower positive bounded core mode).1]
      change sourceGradeRatio 0 0 1 0 mode • weightedRadialCoordinate 1 lower 0
        (weightedRadialCoreInto 1 lower (core.1.1.1 mode)) =
        (sourceGradeRatio 0 0 1 0 mode : ℂ) • weightedRadialCoordinate 1 lower 0
          (finiteSourceCore parameters 1 lower 0 0 core.1.1.1 mode)
      rw [finiteSourceCore_apply]
      exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _)

def originalSmoothRF0Row : FiniteSmoothStoredRow lower
    (unweightedSourceRF0Bulk parameters lower
      (originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.1.ofLp.1) :=
  (finiteGraphSmoothRow parameters 1 lower positive core.1.1.1).scalar
    sourceAngularRatio (by
      intro mode
      change sourceAngularRatio mode • weightedRadialCoordinate 1 lower 0
        ((originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.1.ofLp.1 mode) = _
      rw [(originalSmoothStrongData_graph_modes parameters lower positive bounded core mode).1]
      change sourceAngularRatio mode • weightedRadialCoordinate 1 lower 0
        (weightedRadialCoreInto 1 lower (core.1.1.1 mode)) =
        sourceAngularRatio mode • weightedRadialCoordinate 1 lower 0
          (finiteSourceCore parameters 1 lower 0 0 core.1.1.1 mode)
      rw [finiteSourceCore_apply])

def originalSmoothF2Row : FiniteSmoothStoredRow lower
    (unweightedSourceF2Bulk parameters lower
      (originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.1.ofLp.2) := by
  rw [(originalSmoothStrongData_graphs parameters lower positive bounded core).2]
  exact finiteGraphSmoothRow parameters 1 lower positive (meanFreeRadialCore core.1.1.2)

def originalSmoothFRow : FiniteSmoothStoredRow lower
    ((originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.2.ofLp.1) := by
  rw [(originalSmoothStrongData_forcing parameters lower positive bounded core).1]
  exact finiteOrdinarySmoothRow 1 lower (meanFreeRadialCore core.1.2.1)

def originalSmoothGRow : FiniteSmoothStoredRow lower
    (originalAngularDecode lower
      (originalSmoothStrongData parameters lower positive bounded core).val.ofLp.1.ofLp.2.ofLp.2) := by
  rw [(originalSmoothStrongData_forcing parameters lower positive bounded core).2]
  exact (finiteOrdinarySmoothRow 1 lower (meanFreeRadialCore core.1.2.2)).scalar
    (fun mode => (((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ)) (fun _ => rfl)

variable (length : ℝ) (lengthPositive : 0 < length)

/-- All four stored known rows are the original source reconstruction. -/
def smoothStrongKnownRow (slot : Fin 4) : FiniteSmoothStoredRow lower
    (strongKnownBulk parameters lower positive bounded
      ((strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core) slot) := by
  have same := congrArg (fun data : StrongDataCarrier parameters lower positive bounded 0 0 =>
    strongKnownBulk parameters lower positive bounded data slot)
    (strongSmoothDenseMap_actual parameters lower length positive bounded lengthPositive core)
  rw [same]
  refine Fin.cases ?_ (fun second => Fin.cases ?_ (fun third => Fin.cases ?_
    (fun fourth => Fin.cases ?_ (fun impossible => Fin.elim0 impossible) fourth) third) second) slot
  · exact (originalSmoothF0Row parameters lower positive bounded core).highWeight positive bounded
  · exact (originalSmoothRF0Row parameters lower positive bounded core).highWeight positive bounded
  · exact (originalSmoothF2Row parameters lower positive bounded core).highWeight positive bounded
  · exact (originalSmoothFRow parameters lower positive bounded core).highWeight positive bounded

/-- The independent genuine g row, derived from the same strengthened g. -/
def smoothStrongGRow : FiniteSmoothStoredRow lower
    ((strongToLow parameters lower positive bounded 0 0
      ((strongSmoothDenseMap parameters lower length positive bounded lengthPositive).mapping core)).ofLp.1.ofLp.2) := by
  have same := congrArg (fun data : StrongDataCarrier parameters lower positive bounded 0 0 =>
    (strongToLow parameters lower positive bounded 0 0 data).ofLp.1.ofLp.2)
    (strongSmoothDenseMap_actual parameters lower length positive bounded lengthPositive core)
  rw [same]
  exact (originalSmoothGRow parameters lower positive bounded core).highWeight positive bounded

end Grad.AnnularSmoothSources
