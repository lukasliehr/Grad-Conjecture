import AIS2ClosedWeightedGraphCompatibility
import AID1ActualHighOutputCoordinates
import SCS5MeanFreeRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.SourceCollarFullSource Grad.AnnularSourceGraph Grad.AnnularVariational
open Grad.AnnularCurrentEnergy Grad.AnnularCurrentGreen Grad.ActualBoundaryPrimitives

section Carrier

variable (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)

/-- Orthogonal Fourier restriction followed by the literal zero extension.
Its fixed points are exactly scalar rows supported on the high set. -/
def highRowProjection (lower : ℝ) :
    DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower :=
  (highBulkIntoFull lower).toContinuousLinearMap.comp (highFullRestriction lower)

theorem highRowProjection_high (lower : ℝ) (row : DivisionRow 1 lower)
    (mode : HighAnnularMode) :
    highRowProjection lower row mode.val = row mode.val := by
  change highBulkIntoFull lower (highFullRestriction lower row) mode.val = row mode.val
  rw [highBulkIntoFull_high, highFullRestriction_apply]

theorem highRowProjection_low (lower : ℝ) (row : DivisionRow 1 lower)
    (mode : ℤ × ℤ) (low : ¬ 3 ≤ |mode.1|) :
    highRowProjection lower row mode = 0 := by
  change highBulkIntoFull lower (highFullRestriction lower row) mode = 0
  exact highBulkIntoFull_low lower _ mode low

theorem highRowProjection_fixed_iff (lower : ℝ) (row : DivisionRow 1 lower) :
    highRowProjection lower row = row ↔
      ∀ mode : ℤ × ℤ, ¬ 3 ≤ |mode.1| → row mode = 0 := by
  constructor
  · intro fixed mode low
    rw [← fixed, highRowProjection_low lower row mode low]
  · intro supported
    apply lp.ext
    funext mode
    by_cases high : 3 ≤ |mode.1|
    · exact highRowProjection_high lower row ⟨mode, high⟩
    · rw [highRowProjection_low lower row mode high, supported mode high]

theorem meanFreeRow_fixed_iff (lower : ℝ) (row : DivisionRow 1 lower) :
    meanFreeRow lower row = row ↔
      ∀ mode : ℤ × ℤ, mode.1 = 0 → row mode = 0 := by
  constructor
  · intro fixed mode zero
    rw [← fixed, meanFreeRow_apply, if_pos zero]
  · intro meanFree
    apply lp.ext
    funext mode
    rw [meanFreeRow_apply]
    split_ifs with zero
    · exact (meanFree mode zero).symm
    · rfl

def highKnownF2MeanResidual :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  ((meanFreeRow lower).restrictScalars ℝ).comp
      (highKnownWeightedF2 parameters lower angular cell) -
    highKnownWeightedF2 parameters lower angular cell

def highKnownFHighResidual :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  ((highRowProjection lower).restrictScalars ℝ).comp
      (highKnownWeightedF parameters lower angular cell) -
    highKnownWeightedF parameters lower angular cell

def highKnownGHighResidual :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  ((highRowProjection lower).restrictScalars ℝ).comp
      (highKnownWeightedG parameters lower angular cell) -
    highKnownWeightedG parameters lower angular cell

def highKnownQcHighResidual :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  ((highRowProjection lower).restrictScalars ℝ).comp
      (highKnownWeightedQc parameters lower angular cell) -
    highKnownWeightedQc parameters lower angular cell

def highKnownRqvHighResidual :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  ((highRowProjection lower).restrictScalars ℝ).comp
      (highKnownWeightedRqv parameters lower angular cell) -
    highKnownWeightedRqv parameters lower angular cell

/-- The closed AK8 support conditions, isolated from the radial graph
compatibility so that each analytic constraint is checked independently. -/
def highKnownSupportCarrier :
    Submodule ℝ (ActualHighKnownAmbient parameters lower angular cell) :=
  (highKnownF2MeanResidual parameters lower angular cell).ker ⊓
    (highKnownFHighResidual parameters lower angular cell).ker ⊓
    (highKnownGHighResidual parameters lower angular cell).ker ⊓
    (highKnownQcHighResidual parameters lower angular cell).ker ⊓
    (highKnownRqvHighResidual parameters lower angular cell).ker

theorem highKnownSupportCarrier_mem_iff
    (data : ActualHighKnownAmbient parameters lower angular cell) :
    data ∈ highKnownSupportCarrier parameters lower angular cell ↔
    meanFreeRow lower (highKnownWeightedF2 parameters lower angular cell data) =
        highKnownWeightedF2 parameters lower angular cell data ∧
      highRowProjection lower (highKnownWeightedF parameters lower angular cell data) =
        highKnownWeightedF parameters lower angular cell data ∧
      highRowProjection lower (highKnownWeightedG parameters lower angular cell data) =
        highKnownWeightedG parameters lower angular cell data ∧
      highRowProjection lower (highKnownWeightedQc parameters lower angular cell data) =
        highKnownWeightedQc parameters lower angular cell data ∧
      highRowProjection lower (highKnownWeightedRqv parameters lower angular cell data) =
        highKnownWeightedRqv parameters lower angular cell data := by
  rw [highKnownSupportCarrier]
  simp only [Submodule.mem_inf, LinearMap.mem_ker]
  constructor
  · rintro ⟨⟨⟨⟨f2Mean, fHigh⟩, gHigh⟩, qcHigh⟩, rqvHigh⟩
    change meanFreeRow lower (highKnownWeightedF2 parameters lower angular cell data) -
      highKnownWeightedF2 parameters lower angular cell data = 0 at f2Mean
    change highRowProjection lower (highKnownWeightedF parameters lower angular cell data) -
      highKnownWeightedF parameters lower angular cell data = 0 at fHigh
    change highRowProjection lower (highKnownWeightedG parameters lower angular cell data) -
      highKnownWeightedG parameters lower angular cell data = 0 at gHigh
    change highRowProjection lower (highKnownWeightedQc parameters lower angular cell data) -
      highKnownWeightedQc parameters lower angular cell data = 0 at qcHigh
    change highRowProjection lower (highKnownWeightedRqv parameters lower angular cell data) -
      highKnownWeightedRqv parameters lower angular cell data = 0 at rqvHigh
    exact ⟨sub_eq_zero.mp f2Mean, sub_eq_zero.mp fHigh,
      sub_eq_zero.mp gHigh, sub_eq_zero.mp qcHigh, sub_eq_zero.mp rqvHigh⟩
  · rintro ⟨f2Mean, fHigh, gHigh, qcHigh, rqvHigh⟩
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · change meanFreeRow lower (highKnownWeightedF2 parameters lower angular cell data) -
        highKnownWeightedF2 parameters lower angular cell data = 0
      exact sub_eq_zero.mpr f2Mean
    · change highRowProjection lower (highKnownWeightedF parameters lower angular cell data) -
        highKnownWeightedF parameters lower angular cell data = 0
      exact sub_eq_zero.mpr fHigh
    · change highRowProjection lower (highKnownWeightedG parameters lower angular cell data) -
        highKnownWeightedG parameters lower angular cell data = 0
      exact sub_eq_zero.mpr gHigh
    · change highRowProjection lower (highKnownWeightedQc parameters lower angular cell data) -
        highKnownWeightedQc parameters lower angular cell data = 0
      exact sub_eq_zero.mpr qcHigh
    · change highRowProjection lower (highKnownWeightedRqv parameters lower angular cell data) -
        highKnownWeightedRqv parameters lower angular cell data = 0
      exact sub_eq_zero.mpr rqvHigh

theorem highKnownSupportCarrier_closed :
    IsClosed (highKnownSupportCarrier parameters lower angular cell :
      Set (ActualHighKnownAmbient parameters lower angular cell)) :=
  ((((highKnownF2MeanResidual parameters lower angular cell).isClosed_ker.inter
      (highKnownFHighResidual parameters lower angular cell).isClosed_ker).inter
      (highKnownGHighResidual parameters lower angular cell).isClosed_ker).inter
      (highKnownQcHighResidual parameters lower angular cell).isClosed_ker).inter
      (highKnownRqvHighResidual parameters lower angular cell).isClosed_ker

/-- The exact complete high extended BF2 data carrier.  Besides the closed
weighted/source-graph identities it retains AK8's mean-free `F2` and high
supports for `f_h`, `g_h`, `q_c`, and `q_v`. -/
def ActualHighKnownCarrier :
    Submodule ℝ (ActualHighKnownAmbient parameters lower angular cell) :=
  highKnownCompatibilityCarrier parameters lower positive bounded angular cell ⊓
    highKnownSupportCarrier parameters lower angular cell

theorem ActualHighKnownCarrier_closed :
    IsClosed (ActualHighKnownCarrier parameters lower positive bounded angular cell :
      Set (ActualHighKnownAmbient parameters lower angular cell)) :=
  (highKnownCompatibilityCarrier_closed parameters lower positive bounded angular cell).inter
    (highKnownSupportCarrier_closed parameters lower angular cell)

instance actualHighKnownCarrierComplete :
    CompleteSpace (ActualHighKnownCarrier parameters lower positive bounded angular cell) :=
  (ActualHighKnownCarrier_closed parameters lower positive bounded angular cell).completeSpace_coe

theorem ActualHighKnownCarrier.weightedGraphCompatibility
    (data : ActualHighKnownCarrier parameters lower positive bounded angular cell) :
    WeightedGraphCompatibility parameters lower (angular + cell)
      (highKnownF0GraphProjection parameters lower angular cell data,
        highKnownF2GraphProjection parameters lower angular cell data)
      (highKnownWeightedProjection parameters lower angular cell data) := by
  apply (highKnownCompatibilityCarrier_mem_iff parameters lower positive bounded
    angular cell data.val).mp
  exact data.property.1

theorem ActualHighKnownCarrier.support_coordinates
    (data : ActualHighKnownCarrier parameters lower positive bounded angular cell) :
    meanFreeRow lower (highKnownWeightedF2 parameters lower angular cell data) =
        highKnownWeightedF2 parameters lower angular cell data ∧
      highRowProjection lower (highKnownWeightedF parameters lower angular cell data) =
        highKnownWeightedF parameters lower angular cell data ∧
      highRowProjection lower (highKnownWeightedG parameters lower angular cell data) =
        highKnownWeightedG parameters lower angular cell data ∧
      highRowProjection lower (highKnownWeightedQc parameters lower angular cell data) =
        highKnownWeightedQc parameters lower angular cell data ∧
      highRowProjection lower (highKnownWeightedRqv parameters lower angular cell data) =
        highKnownWeightedRqv parameters lower angular cell data := by
  apply (highKnownSupportCarrier_mem_iff parameters lower angular cell data.val).mp
  exact data.property.2

def actualHighKnownWeighted :
    ActualHighKnownCarrier parameters lower positive bounded angular cell →L[ℝ]
      HighKnownSourceBulk lower :=
  (highKnownWeightedProjection parameters lower angular cell).comp
    (ActualHighKnownCarrier parameters lower positive bounded angular cell).subtypeL

def actualHighKnownAuxiliary :
    ActualHighKnownCarrier parameters lower positive bounded angular cell →L[ℝ]
      HighAuxiliarySourceBulk lower :=
  (highKnownAuxiliaryProjection parameters lower angular cell).comp
    (ActualHighKnownCarrier parameters lower positive bounded angular cell).subtypeL

def actualHighKnownF0Graph :
    ActualHighKnownCarrier parameters lower positive bounded angular cell →L[ℝ]
      HighF0SourceGraph parameters lower :=
  (highKnownF0GraphProjection parameters lower angular cell).comp
    (ActualHighKnownCarrier parameters lower positive bounded angular cell).subtypeL

def actualHighKnownF2Graph :
    ActualHighKnownCarrier parameters lower positive bounded angular cell →L[ℝ]
      HighF2SourceGraph parameters lower :=
  (highKnownF2GraphProjection parameters lower angular cell).comp
    (ActualHighKnownCarrier parameters lower positive bounded angular cell).subtypeL

def actualHighKnownDatum :
    ActualHighKnownCarrier parameters lower positive bounded angular cell →L[ℝ]
      HighBoundaryPrimitive parameters angular cell :=
  (highKnownDatumProjection parameters lower angular cell).comp
    (ActualHighKnownCarrier parameters lower positive bounded angular cell).subtypeL

def actualHighKnownIncoming :
    ActualHighKnownCarrier parameters lower positive bounded angular cell →L[ℝ]
      AnnularBoundary :=
  (highKnownIncomingProjection parameters lower angular cell).comp
    (ActualHighKnownCarrier parameters lower positive bounded angular cell).subtypeL

def ActualHighKnownCarrier.graphs
    (data : ActualHighKnownCarrier parameters lower positive bounded angular cell) :
    HighRadialSourceGraphs parameters lower (angular + cell) :=
  (actualHighKnownF0Graph parameters lower positive bounded angular cell data,
    actualHighKnownF2Graph parameters lower positive bounded angular cell data)

/-- Forget only the Hilbert packaging and support witnesses.  The resulting
record is exactly the accepted AEK graph-native datum. -/
def ActualHighKnownCarrier.toGraphKnownData
    (data : ActualHighKnownCarrier parameters lower positive bounded angular cell) :
    ActualHighGraphKnownData parameters lower angular cell where
  weighted := actualHighKnownWeighted parameters lower positive bounded angular cell data
  auxiliary := actualHighKnownAuxiliary parameters lower positive bounded angular cell data
  graphs := ActualHighKnownCarrier.graphs parameters lower positive bounded angular cell data
  datum := actualHighKnownDatum parameters lower positive bounded angular cell data
  innerValue := actualHighKnownIncoming parameters lower positive bounded angular cell data
  weightedGraph := ActualHighKnownCarrier.weightedGraphCompatibility parameters lower positive
    bounded angular cell data

theorem ActualHighKnownCarrier.original_supports
    (data : ActualHighKnownCarrier parameters lower positive bounded angular cell) :
    (∀ mode : ℤ × ℤ, mode.1 = 0 →
      (ActualHighKnownCarrier.toGraphKnownData parameters lower positive bounded angular cell
        data).weighted 2 mode = 0) ∧
    (∀ mode : ℤ × ℤ, ¬ 3 ≤ |mode.1| →
      (ActualHighKnownCarrier.toGraphKnownData parameters lower positive bounded angular cell
        data).weighted 3 mode = 0) ∧
    (∀ slot : Fin 3, ∀ mode : ℤ × ℤ, ¬ 3 ≤ |mode.1| →
      (ActualHighKnownCarrier.toGraphKnownData parameters lower positive bounded angular cell
        data).auxiliary slot mode = 0) := by
  have support := ActualHighKnownCarrier.support_coordinates parameters lower positive bounded
    angular cell data
  refine ⟨(meanFreeRow_fixed_iff lower _).mp support.1, ?_, ?_⟩
  · exact (highRowProjection_fixed_iff lower _).mp support.2.1
  intro slot
  fin_cases slot
  · exact (highRowProjection_fixed_iff lower _).mp support.2.2.1
  · exact (highRowProjection_fixed_iff lower _).mp support.2.2.2.1
  · exact (highRowProjection_fixed_iff lower _).mp support.2.2.2.2

end Carrier

end Grad.AnnularCurrentSource
