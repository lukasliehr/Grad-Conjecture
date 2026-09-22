import AJE40FiniteSourceCutPrimitives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set Filter
open scoped Topology BigOperators
namespace Grad.AnnularStrongOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularKernelOrbit Grad.AnnularCurrentSource
open Grad.BoundaryKernelAction Grad.ActualBoundaryPrimitives Grad.AnnularStrongData Grad.AnnularKernelL2 Grad.AnnularOrbitGenerators Grad.AnnularHighTilt

private theorem cutPoint {E F : Type*} [Zero E] [Zero F] (mapping : E → F) (zero : mapping 0 = 0)
    (condition : Prop) [Decidable condition] (value : E) :
    mapping (if condition then value else 0) = if condition then mapping value else 0 := by
  split_ifs
  · rfl
  · exact zero

theorem annularSourceCoordinate_cut (parameters : PhaseParameters) (dimension : ℕ)
    (lower : ℝ) (angular cell : ℕ) (coordinate : Fin 2) (support : Finset (ℤ × ℤ))
    (field : AnnularSourceH1 parameters dimension lower angular cell) :
    annularSourceCoordinate parameters dimension lower angular cell coordinate (sourceLpCut support field) =
      sourceLpCut support (annularSourceCoordinate parameters dimension lower angular cell coordinate field) := by
  apply lp.ext
  funext mode
  rw [annularSourceCoordinate_apply,sourceLpCut_apply,sourceLpCut_apply]
  exact cutPoint (weightedRadialCoordinate dimension lower coordinate) (map_zero _) _ _

theorem bulkInclusion_cut (parameters : PhaseParameters) (dimension : ℕ) (lower : ℝ)
    (lowAngular lowCell highAngular highCell : ℕ) (angularLe : lowAngular ≤ highAngular)
    (cellLe : lowCell ≤ highCell) (support : Finset (ℤ × ℤ))
    (field : AnnularSourceBulk parameters dimension lower highAngular highCell) :
    annularBulkInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe
      (sourceLpCut support field) = sourceLpCut support
        (annularBulkInclusion parameters dimension lower lowAngular lowCell highAngular highCell angularLe cellLe field) := by
  apply lp.ext
  funext mode
  rw [sourceLpCut_apply]
  change sourceGradeRatio lowAngular lowCell highAngular highCell mode • sourceLpCut support field mode = _
  rw [sourceLpCut_apply]
  exact cutPoint (fun value : RadialL2 dimension lower => sourceGradeRatio lowAngular lowCell highAngular highCell mode • value)
    (smul_zero _) _ _

theorem sourceAngularBulk_cut (lower : ℝ) (support : Finset (ℤ × ℤ)) (field : DivisionRow 1 lower) :
    sourceAngularBulk lower (sourceLpCut support field) = sourceLpCut support (sourceAngularBulk lower field) := by
  apply lp.ext
  funext mode
  rw [sourceAngularBulk_mode,sourceLpCut_apply,sourceLpCut_apply]
  exact cutPoint (fun value : RadialL2 1 lower => sourceAngularRatio mode • value) (smul_zero _) _ _

theorem unweightedSourceF0Bulk_cut (parameters : PhaseParameters) (lower : ℝ)
    (support : Finset (ℤ × ℤ)) (field : HighF0SourceGraph parameters lower) :
    unweightedSourceF0Bulk parameters lower (sourceLpCut support field) = sourceLpCut support (unweightedSourceF0Bulk parameters lower field) := by
  change annularBulkInclusion parameters 1 lower 0 0 1 0 (by omega) (by omega)
    (annularSourceCoordinate parameters 1 lower 1 0 0 (sourceLpCut support field)) = _
  rw [annularSourceCoordinate_cut,bulkInclusion_cut]
  rfl

theorem unweightedSourceRF0Bulk_cut (parameters : PhaseParameters) (lower : ℝ)
    (support : Finset (ℤ × ℤ)) (field : HighF0SourceGraph parameters lower) :
    unweightedSourceRF0Bulk parameters lower (sourceLpCut support field) = sourceLpCut support (unweightedSourceRF0Bulk parameters lower field) := by
  change sourceAngularBulk lower (annularSourceCoordinate parameters 1 lower 1 0 0 (sourceLpCut support field)) = _
  rw [annularSourceCoordinate_cut,sourceAngularBulk_cut]
  rfl

theorem unweightedSourceF2Bulk_cut (parameters : PhaseParameters) (lower : ℝ)
    (support : Finset (ℤ × ℤ)) (field : HighF2SourceGraph parameters lower) :
    unweightedSourceF2Bulk parameters lower (sourceLpCut support field) = sourceLpCut support (unweightedSourceF2Bulk parameters lower field) :=
  annularSourceCoordinate_cut parameters 1 lower 0 0 0 support field

theorem divisionHighWeight_cut (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (support : Finset (ℤ × ℤ)) (field : DivisionRow 1 lower) :
    divisionHighWeight lower positive bounded (sourceLpCut support field) = sourceLpCut support (divisionHighWeight lower positive bounded field) := by
  apply lp.ext
  funext mode
  rw [divisionHighWeight_mode,sourceLpCut_apply,sourceLpCut_apply]
  exact cutPoint
    (scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
      (lower ^ (-highTiltExponent)) (highNegativePower_bound lower positive bounded)) (map_zero _) _ _

def outerDatumCut (parameters : PhaseParameters) (angular cell : ℕ) (support : Finset (ℤ × ℤ)) :
    HighBoundaryPrimitive parameters angular cell →L[ℝ] HighBoundaryPrimitive parameters angular cell :=
  ((sourceLpCut support).comp ((highAngularSubmodule parameters angular cell 1).subtypeL.restrictScalars ℝ)).codRestrict
    ((highAngularSubmodule parameters angular cell 1).restrictScalars ℝ) (by
      intro field mode low
      change negativeTraceCoefficient parameters angular cell (sourceLpCut support field.val) mode = 0
      unfold negativeTraceCoefficient
      rw [sourceLpCut_apply]
      by_cases inside : mode ∈ support
      · rw [if_pos inside]
        exact field.property mode low
      · rw [if_neg inside,smul_zero])

theorem outerDatumCut_val (parameters : PhaseParameters) (angular cell : ℕ) (support : Finset (ℤ × ℤ))
    (field : HighBoundaryPrimitive parameters angular cell) :
    (outerDatumCut parameters angular cell support field).val = sourceLpCut support field.val := rfl

theorem outerDatumCut_bound (parameters : PhaseParameters) (angular cell : ℕ) (support : Finset (ℤ × ℤ))
    (field : HighBoundaryPrimitive parameters angular cell) :
    ‖outerDatumCut parameters angular cell support field‖ ≤ ‖field‖ := sourceLpCut_bound support field.val

theorem outerDatumCut_tendsto (parameters : PhaseParameters) (angular cell : ℕ)
    (field : HighBoundaryPrimitive parameters angular cell) :
    Tendsto (fun support => outerDatumCut parameters angular cell support field) atTop (𝓝 field) :=
  (tendsto_subtype_rng).mpr (sourceLpCut_tendsto field.val)

end Grad.AnnularStrongOrbit
