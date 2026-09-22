import AEI18ActualCircularLowRowAlgebra

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentLow
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.GaugeCoefficients.Physical.Allocation
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelContinuity Grad.AnnularKernelL2 Grad.ActualBoundaryPrimitives Grad.BoundaryKernelAction Grad.GaugeCoefficients.Physical.Ledger

open Grad.PhaseAlgebra

/-- The exact common balancing derivative and the physical -x/r term.
The reference diagonal provides its already checked continuous realization. -/
def lowCommonDiagonalCurve (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (index : LowAnnularIndex) : C(ℝ, ℝ) :=
  lowNormalizedReferenceCurve parameters length lower positive index.2 index.1 index.1 +
    (if index.1 = 0 then (2 : ℝ) else -2) • lowRadiusMuRatio lower length positive index.2.val.2

theorem lowCommonDiagonalCurve_actual (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (index : LowAnnularIndex) (radius : ℝ) (inside : lower ≤ radius) :
    lowCommonDiagonalCurve parameters length lower positive index radius =
      (annularPhaseSlope parameters index.2.val.2 radius +
        if index.1 = 0 then lowMuLogSlope length radius index.2.val.2 else -1 / radius) / lowMu length radius index.2.val.2 := by
  change lowNormalizedReferenceCurve parameters length lower positive index.2 index.1 index.1 radius +
    (if index.1 = 0 then (2 : ℝ) else -2) * lowRadiusMuRatio lower length positive index.2.val.2 radius = _
  rw [lowNormalizedReferenceCurve_actual parameters length lower positive index.2 index.1 index.1 radius inside,
    lowRadiusMuRatio_actual lower length positive index.2.val.2 radius inside]
  rcases index with ⟨row, mode⟩
  fin_cases row <;> simp [lowReferenceMatrix] <;> ring

theorem lowCommonDiagonalCurve_bound (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (index : LowAnnularIndex)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    |lowCommonDiagonalCurve parameters length lower positive index radius| ≤ lowReferenceCoefficientConstant parameters length + 2 := by
  have refBound := lowNormalizedReferenceCurve_bound parameters length lower lengthPositive positive index.2 index.1 index.1 radius inside
  have radial := lowRadiusMuRatio_bound lower length positive index.2.val.2 radius
  have coefficient : |if index.1 = 0 then (2 : ℝ) else -2| = 2 := by split_ifs <;> norm_num
  change |lowNormalizedReferenceCurve parameters length lower positive index.2 index.1 index.1 radius +
    (if index.1 = 0 then (2 : ℝ) else -2) * lowRadiusMuRatio lower length positive index.2.val.2 radius| ≤ _
  exact (abs_add_le _ _).trans (by rw [abs_mul, coefficient]; linarith)

def lowCommonDiagonal (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) : LowEnergyBulk lower →L[ℂ] LowEnergyBulk lower :=
  complexLpTwoMap (fun index => scalarRadialMap lower (lowCommonDiagonalCurve parameters length lower positive index)
    (lowReferenceCoefficientConstant parameters length + 2)
    (lowCommonDiagonalCurve_bound parameters length lower lengthPositive positive index))
    (lowReferenceCoefficientConstant parameters length + 2)
    (by have := lowReferenceCoefficientConstant_pos parameters length lengthPositive; positivity)
    (fun _ field => scalarRadialMap_bound _ _ _ _ field)

theorem lowCommonDiagonal_ae (parameters : PhaseParameters) (length lower : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (field : LowEnergyBulk lower) (index : LowAnnularIndex) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      lowCommonDiagonal parameters length lower lengthPositive positive field index radius =
        ((annularPhaseSlope parameters index.2.val.2 radius +
          if index.1 = 0 then lowMuLogSlope length radius index.2.val.2 else -1 / radius) / lowMu length radius index.2.val.2) • field index radius := by
  have actual := scalarRadialMap_ae lower (lowCommonDiagonalCurve parameters length lower positive index)
    (lowReferenceCoefficientConstant parameters length + 2)
    (lowCommonDiagonalCurve_bound parameters length lower lengthPositive positive index) (field index)
  filter_upwards [actual, ae_restrict_mem measurableSet_Icc] with radius actual inside
  rw [lowCommonDiagonalCurve_actual parameters length lower positive index radius inside.1] at actual
  exact actual

end Grad.AnnularCurrentLow
