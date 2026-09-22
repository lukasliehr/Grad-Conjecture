import AJB24OriginalLowSolutionLeibnizBound

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped ContDiff
namespace Grad.AnnularLowOrbit
open Grad.ClosedJets Grad.CartesianState Grad.AnnularLowEnergy Grad.AnnularVariational
open Grad.AnnularOrbitGenerators Grad.AnnularCoupledOrbit

/-- Actual projection of the independently prescribed original bulk datum. -/
def lowDataBulkProjection (lower : ℝ) : LowEnergyData lower →L[ℂ] LowEnergyBulk lower :=
  (ContinuousLinearMap.fst ℂ (LowEnergyBulk lower) LowEnergyBoundary).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ (LowEnergyBulk lower) LowEnergyBoundary).toContinuousLinearMap

/-- Actual projection of the independently prescribed original incoming datum. -/
def lowDataIncomingProjection (lower : ℝ) : LowEnergyData lower →L[ℂ] LowEnergyBoundary :=
  (ContinuousLinearMap.snd ℂ (LowEnergyBulk lower) LowEnergyBoundary).comp
    (WithLp.prodContinuousLinearEquiv 2 ℂ (LowEnergyBulk lower) LowEnergyBoundary).toContinuousLinearMap

theorem lowDataCellGenerator_bulk (lower : ℝ) (data : LowEnergyData lower)
    (smooth : ContDiff ℝ ∞ (fun time : ℝ => lowDataTranslationEquivalence lower (0, time) data))
    (order : ℕ) (index : LowAnnularIndex) :
    (actualLowDataCellGenerator lower data order).ofLp.1 index =
      (Complex.I * (index.2.val.2 : ℂ)) ^ order • data.ofLp.1 index := by
  have result := smoothLpCharacterOrbit_coordinates (lowDataBulkProjection lower)
    (fun time => lowDataTranslationEquivalence lower (0, time) data) smooth
    (fun other : LowAnnularIndex => other.2.val.2) data.ofLp.1
    (fun time other => by
      change lowBulkTranslation lower (0, time) data.ofLp.1 other = _
      rw [lowBulkTranslation_apply, orbitCharacter_cell]) order index
  exact result

theorem lowDataCellGenerator_incoming (lower : ℝ) (data : LowEnergyData lower)
    (smooth : ContDiff ℝ ∞ (fun time : ℝ => lowDataTranslationEquivalence lower (0, time) data))
    (order : ℕ) (index : LowAnnularIndex) :
    (actualLowDataCellGenerator lower data order).ofLp.2 index =
      (Complex.I * (index.2.val.2 : ℂ)) ^ order • data.ofLp.2 index := by
  apply smoothCharacterOrbit_generator
    ((lp.evalCLM ℂ (fun _ : LowAnnularIndex => ComplexEuclidean 1) 2 index).comp (lowDataIncomingProjection lower))
    (fun time => lowDataTranslationEquivalence lower (0, time) data) smooth (index.2.val.2) (data.ofLp.2 index) _ order
  intro time
  change lowBoundaryTranslation (0, time) data.ofLp.2 index = _
  rw [lowBoundaryTranslation_apply, orbitCharacter_cell]

theorem lowData_component_norms (lower : ℝ) (data : LowEnergyData lower) :
    ‖data.ofLp.1‖ ≤ ‖data‖ ∧ ‖data.ofLp.2‖ ≤ ‖data‖ := by
  have squared := WithLp.prod_norm_sq_eq_of_L2 data
  change ‖data‖ ^ 2 = ‖data.ofLp.1‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 at squared
  constructor <;> nlinarith only [squared, norm_nonneg data, norm_nonneg data.ofLp.1, norm_nonneg data.ofLp.2,
    sq_nonneg ‖data.ofLp.1‖, sq_nonneg ‖data.ofLp.2‖]

theorem lowData_norm_le_components (lower : ℝ) (data : LowEnergyData lower) :
    ‖data‖ ≤ ‖data.ofLp.1‖ + ‖data.ofLp.2‖ := by
  have squared := WithLp.prod_norm_sq_eq_of_L2 data
  change ‖data‖ ^ 2 = ‖data.ofLp.1‖ ^ 2 + ‖data.ofLp.2‖ ^ 2 at squared
  nlinarith only [squared, norm_nonneg data, norm_nonneg data.ofLp.1, norm_nonneg data.ofLp.2,
    mul_nonneg (norm_nonneg data.ofLp.1) (norm_nonneg data.ofLp.2)]

/-- The literal BF insertion frequency on every original low index. -/
def lowInsertedFrequency (index : LowAnnularIndex) : ℝ :=
  annularFrequency index.2.val.1 index.2.val.2

theorem lowInsertedFrequency_positive (index : LowAnnularIndex) : 0 < lowInsertedFrequency index := by
  unfold lowInsertedFrequency annularFrequency
  positivity

theorem lowInsertedFrequency_cell (index : LowAnnularIndex) : |(index.2.val.2 : ℝ)| ≤ lowInsertedFrequency index := by
  unfold lowInsertedFrequency annularFrequency
  linarith only [abs_nonneg (index.2.val.1 : ℝ)]

end Grad.AnnularLowOrbit
