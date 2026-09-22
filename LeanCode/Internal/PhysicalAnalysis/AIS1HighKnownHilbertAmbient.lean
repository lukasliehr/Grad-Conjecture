import AEK16ExactBaseBF13Consumer
import ADZ1SmoothHighPowers

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularCurrentEnergy
open Grad.ActualBoundaryPrimitives Grad.AnnularHighTilt

/-- The first genuine radial graph in BF2, carrying `F0` and hence `RF0`. -/
abbrev HighF0SourceGraph (parameters : PhaseParameters) (lower : ℝ) :=
  AnnularTotalSourceH1 parameters 1 lower 1 0 0

/-- The second genuine radial graph in BF2, carrying `F2`. -/
abbrev HighF2SourceGraph (parameters : PhaseParameters) (lower : ℝ) :=
  AnnularTotalSourceH1 parameters 1 lower 0 0 0

/-- Hilbert pair of the seven independently normed bulk coordinates. -/
abbrev HighKnownBulkHilbert (lower : ℝ) :=
  WithLp 2 (HighKnownSourceBulk lower × HighAuxiliarySourceBulk lower)

/-- Hilbert pair of the two genuine radial source graphs. -/
abbrev HighKnownGraphHilbert (parameters : PhaseParameters) (lower : ℝ) :=
  WithLp 2 (HighF0SourceGraph parameters lower × HighF2SourceGraph parameters lower)

/-- Hilbert pair of physical outer datum and physical incoming value. -/
abbrev HighKnownBoundaryHilbert (parameters : PhaseParameters) (angular cell : ℕ) :=
  WithLp 2 (HighBoundaryPrimitive parameters angular cell × AnnularBoundary)

/-- Balanced Hilbert sum of the graph and boundary coordinates. -/
abbrev HighKnownGraphBoundaryHilbert (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) :=
  WithLp 2 (HighKnownGraphHilbert parameters lower ×
    HighKnownBoundaryHilbert parameters angular cell)

/-- The literal Hilbert sum of all BF2 high known coordinates.  The four
tilted bulk rows, three auxiliary rows, two genuine radial graphs, physical
outer datum, and physical incoming value are independently normed. -/
abbrev ActualHighKnownAmbient (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) :=
  WithLp 2 (HighKnownBulkHilbert lower ×
    HighKnownGraphBoundaryHilbert parameters lower angular cell)

private def hilbertFst {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : WithLp 2 (E × F) →L[ℝ] E :=
  (ContinuousLinearMap.fst ℝ E F).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap

private def hilbertSnd {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : WithLp 2 (E × F) →L[ℝ] F :=
  (ContinuousLinearMap.snd ℝ E F).comp
    (WithLp.prodContinuousLinearEquiv 2 ℝ E F).toContinuousLinearMap

def highKnownWeightedProjection (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ]
      HighKnownSourceBulk lower :=
  (hilbertFst (E := HighKnownSourceBulk lower)
      (F := HighAuxiliarySourceBulk lower)).comp
    (hilbertFst (E := HighKnownBulkHilbert lower)
      (F := HighKnownGraphBoundaryHilbert parameters lower angular cell))

def highKnownAuxiliaryProjection (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ]
      HighAuxiliarySourceBulk lower :=
  (hilbertSnd (E := HighKnownSourceBulk lower)
      (F := HighAuxiliarySourceBulk lower)).comp
    (hilbertFst (E := HighKnownBulkHilbert lower)
      (F := HighKnownGraphBoundaryHilbert parameters lower angular cell))

def highKnownF0GraphProjection (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ]
      HighF0SourceGraph parameters lower :=
  (hilbertFst (E := HighF0SourceGraph parameters lower)
      (F := HighF2SourceGraph parameters lower)).comp
    ((hilbertFst (E := HighKnownGraphHilbert parameters lower)
      (F := HighKnownBoundaryHilbert parameters angular cell)).comp
      (hilbertSnd (E := HighKnownBulkHilbert lower)
        (F := HighKnownGraphBoundaryHilbert parameters lower angular cell)))

def highKnownF2GraphProjection (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ]
      HighF2SourceGraph parameters lower :=
  (hilbertSnd (E := HighF0SourceGraph parameters lower)
      (F := HighF2SourceGraph parameters lower)).comp
    ((hilbertFst (E := HighKnownGraphHilbert parameters lower)
      (F := HighKnownBoundaryHilbert parameters angular cell)).comp
      (hilbertSnd (E := HighKnownBulkHilbert lower)
        (F := HighKnownGraphBoundaryHilbert parameters lower angular cell)))

def highKnownDatumProjection (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ]
      HighBoundaryPrimitive parameters angular cell :=
  (hilbertFst (E := HighBoundaryPrimitive parameters angular cell)
      (F := AnnularBoundary)).comp
    ((hilbertSnd (E := HighKnownGraphHilbert parameters lower)
      (F := HighKnownBoundaryHilbert parameters angular cell)).comp
      (hilbertSnd (E := HighKnownBulkHilbert lower)
        (F := HighKnownGraphBoundaryHilbert parameters lower angular cell)))

def highKnownIncomingProjection (parameters : PhaseParameters) (lower : ℝ)
    (angular cell : ℕ) :
    ActualHighKnownAmbient parameters lower angular cell →L[ℝ] AnnularBoundary :=
  (hilbertSnd (E := HighBoundaryPrimitive parameters angular cell)
      (F := AnnularBoundary)).comp
    ((hilbertSnd (E := HighKnownGraphHilbert parameters lower)
      (F := HighKnownBoundaryHilbert parameters angular cell)).comp
      (hilbertSnd (E := HighKnownBulkHilbert lower)
        (F := HighKnownGraphBoundaryHilbert parameters lower angular cell)))

@[simp] theorem highKnownWeightedProjection_apply (parameters : PhaseParameters)
    (lower : ℝ) (angular cell : ℕ)
    (data : ActualHighKnownAmbient parameters lower angular cell) :
    highKnownWeightedProjection parameters lower angular cell data =
      data.ofLp.1.ofLp.1 := rfl

@[simp] theorem highKnownAuxiliaryProjection_apply (parameters : PhaseParameters)
    (lower : ℝ) (angular cell : ℕ)
    (data : ActualHighKnownAmbient parameters lower angular cell) :
    highKnownAuxiliaryProjection parameters lower angular cell data =
      data.ofLp.1.ofLp.2 := rfl

@[simp] theorem highKnownF0GraphProjection_apply (parameters : PhaseParameters)
    (lower : ℝ) (angular cell : ℕ)
    (data : ActualHighKnownAmbient parameters lower angular cell) :
    highKnownF0GraphProjection parameters lower angular cell data =
      data.ofLp.2.ofLp.1.ofLp.1 := rfl

@[simp] theorem highKnownF2GraphProjection_apply (parameters : PhaseParameters)
    (lower : ℝ) (angular cell : ℕ)
    (data : ActualHighKnownAmbient parameters lower angular cell) :
    highKnownF2GraphProjection parameters lower angular cell data =
      data.ofLp.2.ofLp.1.ofLp.2 := rfl

@[simp] theorem highKnownDatumProjection_apply (parameters : PhaseParameters)
    (lower : ℝ) (angular cell : ℕ)
    (data : ActualHighKnownAmbient parameters lower angular cell) :
    highKnownDatumProjection parameters lower angular cell data =
      data.ofLp.2.ofLp.2.ofLp.1 := rfl

@[simp] theorem highKnownIncomingProjection_apply (parameters : PhaseParameters)
    (lower : ℝ) (angular cell : ℕ)
    (data : ActualHighKnownAmbient parameters lower angular cell) :
    highKnownIncomingProjection parameters lower angular cell data =
      data.ofLp.2.ofLp.2.ofLp.2 := rfl

/-- Bounded multiplication by the literal BF storage factor `r^(-9/4)` on
every scalar Fourier row.  Positivity of the fixed collar gives boundedness. -/
def divisionHighWeight (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) :
    DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower :=
  complexLpTwoMap
    (fun _ => scalarRadialMap lower
      (highPowerCurve lower (-highTiltExponent) positive)
      (lower ^ (-highTiltExponent))
      (fun radius inside => highNegativePower_bound lower positive bounded radius inside))
    (lower ^ (-highTiltExponent)) (Real.rpow_pos_of_pos positive _).le
    (fun _ field => scalarRadialMap_bound lower
      (highPowerCurve lower (-highTiltExponent) positive)
      (lower ^ (-highTiltExponent))
      (fun radius inside => highNegativePower_bound lower positive bounded radius inside) field)

theorem divisionHighWeight_mode (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : DivisionRow 1 lower) (mode : ℤ × ℤ) :
    divisionHighWeight lower positive bounded field mode =
      scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
        (lower ^ (-highTiltExponent))
        (fun radius inside => highNegativePower_bound lower positive bounded radius inside)
        (field mode) := rfl

/-- Pointwise realization of the bounded row multiplier in the exact AEK
compatibility convention. -/
theorem divisionHighWeight_ae (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (field : DivisionRow 1 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      divisionHighWeight lower positive bounded field mode radius =
        ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ) • field mode radius := by
  rw [ae_all_iff]
  intro mode
  filter_upwards [scalarRadialMap_ae lower
    (highPowerCurve lower (-highTiltExponent) positive)
    (lower ^ (-highTiltExponent))
    (fun radius inside => highNegativePower_bound lower positive bounded radius inside)
    (field mode), ae_restrict_mem measurableSet_Icc] with radius weighted inside
  rw [divisionHighWeight_mode, weighted,
    highPowerCurve_physical lower (-highTiltExponent) positive radius inside]
  simp only [highTiltExponent]
  have exponent : (-(9 / 4) : ℝ) = -9 / 4 := by ring
  rw [exponent, RCLike.real_smul_eq_coe_smul (K := ℂ)]
  rfl

end Grad.AnnularCurrentSource
