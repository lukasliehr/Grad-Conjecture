import AIY2ClosedSharedStrongCarrier

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongData
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceCollarFullSource Grad.AnnularSourceGraph Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentGreen Grad.AnnularCurrentSource
open Grad.AnnularKnownLow Grad.AnnularLowEnergy

theorem strongHighRow_bound (lower : ℝ) (row : DivisionRow 1 lower) :
    ‖highRowProjection lower row‖ ≤ ‖row‖ := by
  change ‖highBulkIntoFull lower (highFullRestriction lower row)‖ ≤ _
  rw [(highBulkIntoFull lower).norm_map]
  exact highFullRestrictionValue_bound lower row

theorem strongHighRow_idempotent (lower : ℝ) (row : DivisionRow 1 lower) :
    highRowProjection lower (highRowProjection lower row) = highRowProjection lower row :=
  (highRowProjection_fixed_iff lower _).mpr (fun mode low =>
    highRowProjection_low lower row mode low)

/-- Only the full f row is projected; every original source coordinate stays
unchanged. -/
def strongHighWeightedMap (lower : ℝ) :
    HighKnownSourceBulk lower →L[ℝ] HighKnownSourceBulk lower :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => DivisionRow 1 lower)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![(highSourceF0 lower).restrictScalars ℝ,
      (highSourceRF0 lower).restrictScalars ℝ, (highSourceF2 lower).restrictScalars ℝ,
      ((highRowProjection lower).comp (highSourceF lower)).restrictScalars ℝ])

/-- The auxiliary high datum is exactly `(Qg,0,0)`; the actual Rg norm
coordinate does not become a spurious high qc forcing. -/
def strongHighAuxiliaryMap (lower : ℝ) :
    HighAuxiliarySourceBulk lower →L[ℝ] HighAuxiliarySourceBulk lower :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => DivisionRow 1 lower)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi ![((highRowProjection lower).comp
      (highSourceG lower)).restrictScalars ℝ, 0, 0])

def strongHighBulkMap (lower : ℝ) :
    HighKnownBulkHilbert lower →L[ℝ] HighKnownBulkHilbert lower :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    (((strongHighWeightedMap lower).prodMap (strongHighAuxiliaryMap lower)).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap)

def strongHighAmbientMap (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) : ActualHighKnownAmbient parameters lower angular cell →L[ℝ]
      ActualHighKnownAmbient parameters lower angular cell :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).symm.toContinuousLinearMap.comp
    (((strongHighBulkMap lower).prodMap
      (ContinuousLinearMap.id ℝ (HighKnownGraphBoundaryHilbert parameters lower angular cell))).comp
      (WithLp.prodContinuousLinearEquiv 2 ℝ _ _).toContinuousLinearMap)

variable (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)

theorem strongHighAmbientMap_mem
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    strongHighAmbientMap parameters lower angular cell data.val.ofLp.1 ∈
      ActualHighKnownCarrier parameters lower positive bounded angular cell := by
  constructor
  · apply (highKnownCompatibilityCarrier_mem_iff parameters lower positive bounded angular cell _).mpr
    exact StrongDataCarrier.compatibility parameters lower positive bounded angular cell data
  · apply (highKnownSupportCarrier_mem_iff parameters lower angular cell _).mpr
    refine ⟨(StrongDataCarrier.mean_free parameters lower positive bounded angular cell data).1,
      strongHighRow_idempotent lower _, strongHighRow_idempotent lower _, ?_, ?_⟩
    · exact map_zero _
    · exact map_zero _

/-- Bounded exact high restriction of the one shared original strong datum. -/
def strongToHigh :
    StrongDataCarrier parameters lower positive bounded angular cell →L[ℝ]
      ActualHighKnownCarrier parameters lower positive bounded angular cell :=
  ((strongHighAmbientMap parameters lower angular cell).comp
    ((strongSharedProjection parameters lower angular cell).comp
      (StrongDataCarrier parameters lower positive bounded angular cell).subtypeL)).codRestrict
    (ActualHighKnownCarrier parameters lower positive bounded angular cell)
    (strongHighAmbientMap_mem parameters lower positive bounded angular cell)

theorem strongToHigh_exact
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    let high := ActualHighKnownCarrier.toGraphKnownData parameters lower positive bounded angular cell
      (strongToHigh parameters lower positive bounded angular cell data)
    high.weighted 0 = data.val.ofLp.1.ofLp.1.ofLp.1 0 ∧
    high.weighted 1 = data.val.ofLp.1.ofLp.1.ofLp.1 1 ∧
    high.weighted 2 = data.val.ofLp.1.ofLp.1.ofLp.1 2 ∧
    high.weighted 3 = highRowProjection lower (data.val.ofLp.1.ofLp.1.ofLp.1 3) ∧
    high.auxiliary 0 = highRowProjection lower (data.val.ofLp.1.ofLp.1.ofLp.2 0) ∧
    high.auxiliary 1 = 0 ∧ high.auxiliary 2 = 0 ∧
    high.graphs = (data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1,
      data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2) ∧
    high.datum = data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1 ∧
    high.innerValue = data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Grad.AnnularStrongData
