import AEK2LiteralSourceCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal

namespace Grad.AnnularCurrentSource

open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularCurrentEnergy

/-- The two genuine completed radial source graphs.  The first graph stores
`F0` at split angular grade one; the second stores `F2` at split grade zero.
Both retain the same independently inserted total grade. -/
abbrev HighRadialSourceGraphs (parameters : PhaseParameters) (lower : ℝ) (grade : ℕ) :=
  AnnularTotalSourceH1 parameters 1 lower 1 0 grade ×
    AnnularTotalSourceH1 parameters 1 lower 0 0 grade

/-- Lower the stored `F0` bulk from split angular grade one to the normalized
scalar row used by the completed eight-slot action. -/
def unweightedSourceF0Bulk (parameters : PhaseParameters) (lower : ℝ) :
    AnnularTotalSourceH1 parameters 1 lower 1 0 0 →L[ℝ] DivisionRow 1 lower :=
  (annularBulkInclusion parameters 1 lower 0 0 1 0 (by omega) (by omega)).comp
    (annularSourceCoordinate parameters 1 lower 1 0 0)

/-- Literal normalized angular generator `i m/(1+|m|)` on a completed
scalar radial row. -/
def sourceAngularBulk (lower : ℝ) :
    DivisionRow 1 lower →L[ℂ] DivisionRow 1 lower :=
  complexLpTwoMap
    (fun mode => sourceAngularRatio mode • ContinuousLinearMap.id ℂ (RadialL2 1 lower))
    1 zero_le_one (fun mode field => by
      change ‖sourceAngularRatio mode • field‖ ≤ 1 * ‖field‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (sourceAngularRatio_bound mode) (norm_nonneg field))

theorem sourceAngularBulk_mode (lower : ℝ) (field : DivisionRow 1 lower)
    (mode : ℤ × ℤ) :
    sourceAngularBulk lower field mode = sourceAngularRatio mode • field mode := rfl

theorem sourceAngularBulk_bound (lower : ℝ) (field : DivisionRow 1 lower) :
    ‖sourceAngularBulk lower field‖ ≤ ‖field‖ := by
  simpa only [sourceAngularBulk, one_mul] using complexLpTwoMap_bound
    (fun mode : ℤ × ℤ =>
      sourceAngularRatio mode • ContinuousLinearMap.id ℂ (RadialL2 1 lower))
    1 zero_le_one (fun mode field => by
      change ‖sourceAngularRatio mode • field‖ ≤ 1 * ‖field‖
      rw [norm_smul]
      exact mul_le_mul_of_nonneg_right (sourceAngularRatio_bound mode) (norm_nonneg field)) field

/-- The `RF0` bulk is derived from the same genuine `F0` graph by the exact
normalized angular Fourier generator. -/
def unweightedSourceRF0Bulk (parameters : PhaseParameters) (lower : ℝ) :
    AnnularTotalSourceH1 parameters 1 lower 1 0 0 →L[ℝ] DivisionRow 1 lower :=
  (sourceAngularBulk lower).restrictScalars ℝ |>.comp
    (annularSourceCoordinate parameters 1 lower 1 0 0)

/-- The stored `F2` bulk coordinate from its genuine split-grade-zero graph. -/
def unweightedSourceF2Bulk (parameters : PhaseParameters) (lower : ℝ) :
    AnnularTotalSourceH1 parameters 1 lower 0 0 0 →L[ℝ] DivisionRow 1 lower :=
  annularSourceCoordinate parameters 1 lower 0 0 0

theorem unweightedSourceF0Bulk_bound (parameters : PhaseParameters) (lower : ℝ)
    (field : AnnularTotalSourceH1 parameters 1 lower 1 0 0) :
    ‖unweightedSourceF0Bulk parameters lower field‖ ≤ ‖field‖ := by
  have inclusion := lpTwoMap_bound
    (sourceGradeFamily (RadialL2 1 lower) 0 0 1 0) 1 zero_le_one
    (sourceGradeFamily_bound (RadialL2 1 lower) 0 0 1 0 (by omega) (by omega))
    (annularSourceCoordinate parameters 1 lower 1 0 0 field)
  change ‖annularBulkInclusion parameters 1 lower 0 0 1 0 (by omega) (by omega)
    (annularSourceCoordinate parameters 1 lower 1 0 0 field)‖ ≤ ‖field‖
  have inclusionBound :
      ‖annularBulkInclusion parameters 1 lower 0 0 1 0 (by omega) (by omega)
        (annularSourceCoordinate parameters 1 lower 1 0 0 field)‖ ≤
      ‖annularSourceCoordinate parameters 1 lower 1 0 0 field‖ := by
    simpa only [annularBulkInclusion, one_mul] using inclusion
  exact inclusionBound.trans
    (annularSourceCoordinate_bound parameters 1 lower 1 0 0 field)

theorem unweightedSourceRF0Bulk_bound (parameters : PhaseParameters) (lower : ℝ)
    (field : AnnularTotalSourceH1 parameters 1 lower 1 0 0) :
    ‖unweightedSourceRF0Bulk parameters lower field‖ ≤ ‖field‖ :=
  (sourceAngularBulk_bound lower
      (annularSourceCoordinate parameters 1 lower 1 0 0 field)).trans
    (by simpa using annularSourceCoordinate_bound parameters 1 lower 1 0 0 field)

theorem unweightedSourceF2Bulk_bound (parameters : PhaseParameters) (lower : ℝ)
    (field : AnnularTotalSourceH1 parameters 1 lower 0 0 0) :
    ‖unweightedSourceF2Bulk parameters lower field‖ ≤ ‖field‖ :=
  annularSourceCoordinate_bound parameters 1 lower 0 0 0 field

/-- The unweighted graph-side witness derived from the two source graphs and
an independent `f` row.  This witness records exact graph coefficients only;
the uniformly normed tilted forcing packet is supplied independently below. -/
def unweightedGraphBulkWitness (parameters : PhaseParameters) (lower : ℝ) (grade : ℕ)
    (graphs : HighRadialSourceGraphs parameters lower grade)
    (f : DivisionRow 1 lower) : HighKnownSourceBulk lower :=
  WithLp.toLp 2 ![unweightedSourceF0Bulk parameters lower graphs.1,
    unweightedSourceRF0Bulk parameters lower graphs.1,
    unweightedSourceF2Bulk parameters lower graphs.2, f]

@[simp] theorem unweightedGraphBulkWitness_f0 (parameters : PhaseParameters) (lower : ℝ)
    (grade : ℕ) (graphs : HighRadialSourceGraphs parameters lower grade)
    (f : DivisionRow 1 lower) :
    unweightedGraphBulkWitness parameters lower grade graphs f 0 =
      unweightedSourceF0Bulk parameters lower graphs.1 := rfl

@[simp] theorem unweightedGraphBulkWitness_rf0 (parameters : PhaseParameters) (lower : ℝ)
    (grade : ℕ) (graphs : HighRadialSourceGraphs parameters lower grade)
    (f : DivisionRow 1 lower) :
    unweightedGraphBulkWitness parameters lower grade graphs f 1 =
      unweightedSourceRF0Bulk parameters lower graphs.1 := rfl

@[simp] theorem unweightedGraphBulkWitness_f2 (parameters : PhaseParameters) (lower : ℝ)
    (grade : ℕ) (graphs : HighRadialSourceGraphs parameters lower grade)
    (f : DivisionRow 1 lower) :
    unweightedGraphBulkWitness parameters lower grade graphs f 2 =
      unweightedSourceF2Bulk parameters lower graphs.2 := rfl

@[simp] theorem unweightedGraphBulkWitness_f (parameters : PhaseParameters) (lower : ℝ)
    (grade : ℕ) (graphs : HighRadialSourceGraphs parameters lower grade)
    (f : DivisionRow 1 lower) :
    unweightedGraphBulkWitness parameters lower grade graphs f 3 = f := rfl


/-- Exact compatibility between the genuine unweighted radial graphs and the
independently normed BF2 tilted packet.  Only `F0`, `RF0`, and `F2` have graph
traces.  The equality is the literal storage multiplication by `r^(-9/4)`;
`f` remains an independent L2 row and has no endpoint trace. -/
def WeightedGraphCompatibility (parameters : PhaseParameters) (lower : ℝ)
    (grade : ℕ) (graphs : HighRadialSourceGraphs parameters lower grade)
    (weighted : HighKnownSourceBulk lower) : Prop :=
  ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
    weighted 0 mode radius =
        ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ) •
          unweightedSourceF0Bulk parameters lower graphs.1 mode radius ∧
    weighted 1 mode radius =
        ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ) •
          unweightedSourceRF0Bulk parameters lower graphs.1 mode radius ∧
    weighted 2 mode radius =
        ((radius ^ (-9 / 4 : ℝ) : ℝ) : ℂ) •
          unweightedSourceF2Bulk parameters lower graphs.2 mode radius

end Grad.AnnularCurrentSource
