import AIS1HighKnownHilbertAmbient

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularCurrentEnergy

section Compatibility

variable (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ)

def highKnownWeightedF0 :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  (highSourceF0 lower).restrictScalars ℝ |>.comp
    (highKnownWeightedProjection parameters lower angular cell)

def highKnownWeightedRF0 :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  (highSourceRF0 lower).restrictScalars ℝ |>.comp
    (highKnownWeightedProjection parameters lower angular cell)

def highKnownWeightedF2 :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  (highSourceF2 lower).restrictScalars ℝ |>.comp
    (highKnownWeightedProjection parameters lower angular cell)

def highKnownWeightedF :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  (highSourceF lower).restrictScalars ℝ |>.comp
    (highKnownWeightedProjection parameters lower angular cell)

def highKnownWeightedG :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  (highSourceG lower).restrictScalars ℝ |>.comp
    (highKnownAuxiliaryProjection parameters lower angular cell)

def highKnownWeightedQc :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  (highSourceQc lower).restrictScalars ℝ |>.comp
    (highKnownAuxiliaryProjection parameters lower angular cell)

def highKnownWeightedRqv :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  (highSourceRqv lower).restrictScalars ℝ |>.comp
    (highKnownAuxiliaryProjection parameters lower angular cell)

def highKnownGraphWeightedF0 :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  (divisionHighWeight lower positive bounded).restrictScalars ℝ |>.comp
    ((unweightedSourceF0Bulk parameters lower).comp
      (highKnownF0GraphProjection parameters lower angular cell))

def highKnownGraphWeightedRF0 :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  (divisionHighWeight lower positive bounded).restrictScalars ℝ |>.comp
    ((unweightedSourceRF0Bulk parameters lower).comp
      (highKnownF0GraphProjection parameters lower angular cell))

def highKnownGraphWeightedF2 :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  (divisionHighWeight lower positive bounded).restrictScalars ℝ |>.comp
    ((unweightedSourceF2Bulk parameters lower).comp
      (highKnownF2GraphProjection parameters lower angular cell))

def highKnownF0CompatibilityResidual :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  highKnownWeightedF0 parameters lower angular cell -
    highKnownGraphWeightedF0 parameters lower positive bounded angular cell

def highKnownRF0CompatibilityResidual :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  highKnownWeightedRF0 parameters lower angular cell -
    highKnownGraphWeightedRF0 parameters lower positive bounded angular cell

def highKnownF2CompatibilityResidual :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] DivisionRow 1 lower :=
  highKnownWeightedF2 parameters lower angular cell -
    highKnownGraphWeightedF2 parameters lower positive bounded angular cell

/-- AEK's pointwise compatibility is exactly equality in the three completed
weighted scalar rows.  This is the closedness bridge for BF2. -/
theorem weightedGraphCompatibility_iff_rows
    (f0 : HighF0SourceGraph parameters lower)
    (f2 : HighF2SourceGraph parameters lower)
    (weighted : HighKnownSourceBulk lower) :
    WeightedGraphCompatibility parameters lower (angular + cell) (f0, f2) weighted ↔
      weighted 0 = divisionHighWeight lower positive bounded
        (unweightedSourceF0Bulk parameters lower f0) ∧
      weighted 1 = divisionHighWeight lower positive bounded
        (unweightedSourceRF0Bulk parameters lower f0) ∧
      weighted 2 = divisionHighWeight lower positive bounded
        (unweightedSourceF2Bulk parameters lower f2) := by
  constructor
  · intro compatible
    have f0Law := divisionHighWeight_ae lower positive bounded
      (unweightedSourceF0Bulk parameters lower f0)
    have rf0Law := divisionHighWeight_ae lower positive bounded
      (unweightedSourceRF0Bulk parameters lower f0)
    have f2Law := divisionHighWeight_ae lower positive bounded
      (unweightedSourceF2Bulk parameters lower f2)
    constructor
    · apply lp.ext
      funext mode
      apply Lp.ext
      filter_upwards [compatible, f0Law] with radius actual stored
      exact (actual mode).1.trans (stored mode).symm
    constructor
    · apply lp.ext
      funext mode
      apply Lp.ext
      filter_upwards [compatible, rf0Law] with radius actual stored
      exact (actual mode).2.1.trans (stored mode).symm
    · apply lp.ext
      funext mode
      apply Lp.ext
      filter_upwards [compatible, f2Law] with radius actual stored
      exact (actual mode).2.2.trans (stored mode).symm
  · rintro ⟨f0Equal, rf0Equal, f2Equal⟩
    unfold WeightedGraphCompatibility
    rw [f0Equal, rf0Equal, f2Equal, ae_all_iff]
    intro mode
    filter_upwards [ae_all_iff.mp (divisionHighWeight_ae lower positive bounded
        (unweightedSourceF0Bulk parameters lower f0)) mode,
      ae_all_iff.mp (divisionHighWeight_ae lower positive bounded
        (unweightedSourceRF0Bulk parameters lower f0)) mode,
      ae_all_iff.mp (divisionHighWeight_ae lower positive bounded
        (unweightedSourceF2Bulk parameters lower f2)) mode]
        with radius first second third
    exact ⟨first, second, third⟩

/-- The compatible weighted/source-graph pairs form a closed real submodule
of the literal Hilbert sum. -/
def highKnownCompatibilityCarrier :
    Submodule ℝ (ActualHighKnownAmbient parameters lower angular cell) :=
  (highKnownF0CompatibilityResidual parameters lower positive bounded angular cell).ker ⊓
    (highKnownRF0CompatibilityResidual parameters lower positive bounded angular cell).ker ⊓
      (highKnownF2CompatibilityResidual parameters lower positive bounded angular cell).ker

theorem highKnownCompatibilityCarrier_mem_iff
    (data : ActualHighKnownAmbient parameters lower angular cell) :
    data ∈ highKnownCompatibilityCarrier parameters lower positive bounded angular cell ↔
      WeightedGraphCompatibility parameters lower (angular + cell)
        (highKnownF0GraphProjection parameters lower angular cell data,
          highKnownF2GraphProjection parameters lower angular cell data)
        (highKnownWeightedProjection parameters lower angular cell data) := by
  change ((highKnownF0CompatibilityResidual parameters lower positive bounded angular cell) data = 0 ∧
    (highKnownRF0CompatibilityResidual parameters lower positive bounded angular cell) data = 0) ∧
      (highKnownF2CompatibilityResidual parameters lower positive bounded angular cell) data = 0 ↔ _
  simp only [highKnownF0CompatibilityResidual, highKnownRF0CompatibilityResidual,
    highKnownF2CompatibilityResidual, sub_apply, sub_eq_zero,
    highKnownWeightedF0, highKnownWeightedRF0, highKnownWeightedF2,
    highKnownGraphWeightedF0, highKnownGraphWeightedRF0, highKnownGraphWeightedF2,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    highKnownWeightedProjection_apply, highKnownF0GraphProjection_apply,
    highKnownF2GraphProjection_apply]
  rw [weightedGraphCompatibility_iff_rows parameters lower positive bounded angular cell
    data.ofLp.2.ofLp.1.ofLp.1 data.ofLp.2.ofLp.1.ofLp.2 data.ofLp.1.ofLp.1]
  constructor
  · rintro ⟨⟨first, second⟩, third⟩
    exact ⟨first, second, third⟩
  · rintro ⟨first, second, third⟩
    exact ⟨⟨first, second⟩, third⟩

theorem highKnownCompatibilityCarrier_closed :
    IsClosed (highKnownCompatibilityCarrier parameters lower positive bounded angular cell :
      Set (ActualHighKnownAmbient parameters lower angular cell)) :=
  ((highKnownF0CompatibilityResidual parameters lower positive bounded angular cell).isClosed_ker.inter
    (highKnownRF0CompatibilityResidual parameters lower positive bounded angular cell).isClosed_ker).inter
      (highKnownF2CompatibilityResidual parameters lower positive bounded angular cell).isClosed_ker

end Compatibility

end Grad.AnnularCurrentSource
