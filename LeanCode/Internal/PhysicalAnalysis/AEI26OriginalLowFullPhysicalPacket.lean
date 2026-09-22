import AEI25OriginalCurrentWeakRows

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

open Grad.SourceBoundaryTrace Grad.AnnularSourceGraph Grad.AnnularFluxTrace Grad.CircularHighRegularity Grad.PhaseAlgebra

theorem lowBulkSlot_outside {dimension : ℕ} (lower : ℝ) (slot : Fin dimension) (field : LowModeBulk lower)
    (mode : ℤ × ℤ) (outside : ¬ (|mode.1| = 1 ∨ |mode.1| = 2)) : lowBulkSlot lower slot field mode = 0 := by
  change radialMatrixUnit lower slot 0 (lowBulkIntoFull lower field mode) = 0
  rw [lowBulkIntoFull_outside lower field mode outside, map_zero]

theorem lowNormalizedSevenInput_outside (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (field : LowEnergyBulk lower)
    (mode : ℤ × ℤ) (outside : ¬ (|mode.1| = 1 ∨ |mode.1| = 2)) :
    lowNormalizedSevenInput parameters lower length lengthPositive positive field mode = 0 := by
  change lowBulkSlot lower 0 (lowComponent lower 1 field) mode +
    lowBulkSlot lower 1 (lowNormalizedAngular parameters lower length positive field) mode +
    lowBulkSlot lower 2 (lowNormalizedCell parameters lower length lengthPositive positive field) mode +
    lowBulkSlot lower 3 (lowNormalizedRadius parameters lower length positive field) mode = 0
  rw [lowBulkSlot_outside lower 0 _ mode outside, lowBulkSlot_outside lower 1 _ mode outside,
    lowBulkSlot_outside lower 2 _ mode outside, lowBulkSlot_outside lower 3 _ mode outside]
  simp

def lowRhoPhysicalWeight (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (radius : ℝ) (mode : ℤ × ℤ) : ℝ :=
  lowStorageWeight lower positive radius * Real.exp (radialPhase parameters radius mode.2)

theorem lowRhoPhysicalWeight_pos (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (radius : ℝ) (mode : ℤ × ℤ) : 0 < lowRhoPhysicalWeight parameters lower positive radius mode :=
  mul_pos (lowPowerCurve_pos lower (-(7 / 4 : ℝ)) positive radius) (Real.exp_pos _)

/-- Actual original low physical seven-tuple, with zero complement in the
full angular/cell index set. Every retained entry uses the genuine ADY section. -/
def lowOriginalSevenCoefficient (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (field : lowEnergyGraph lower length positive)
    (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean 7 :=
  if low : (|mode.1| = 1 ∨ |mode.1| = 2) then
    lowPhysicalSevenSymbol radius ⟨mode, low⟩
      (radialSectionExtension 1 lower bounded.le (lowPhysicalSection parameters lower length positive bounded field (0, ⟨mode, low⟩)) radius 0)
      (radialSectionExtension 1 lower bounded.le (lowPhysicalSection parameters lower length positive bounded field (1, ⟨mode, low⟩)) radius 0)
  else 0

theorem lowNormalizedSevenInput_original (parameters : PhaseParameters) (lower length : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (field : lowEnergyGraph lower length positive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      lowNormalizedSevenInput parameters lower length lengthPositive positive (field.val 0) mode radius =
        (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ) •
          lowOriginalSevenCoefficient parameters lower length positive bounded field radius mode := by
  rw [ae_all_iff]
  intro mode
  by_cases low : (|mode.1| = 1 ∨ |mode.1| = 2)
  · simpa only [lowOriginalSevenCoefficient, dif_pos low, lowRhoPhysicalWeight, lowPhysicalStoredWeight] using
      lowNormalizedSevenInput_physical parameters lower length lengthPositive positive bounded field ⟨mode, low⟩
  · simp only [lowOriginalSevenCoefficient, dif_neg low, smul_zero,
      lowNormalizedSevenInput_outside parameters lower length lengthPositive positive (field.val 0) mode low]
    exact Lp.coeFn_zero (ComplexEuclidean 7) 2 (volume.restrict (Icc lower 1))

end Grad.AnnularCurrentLow
