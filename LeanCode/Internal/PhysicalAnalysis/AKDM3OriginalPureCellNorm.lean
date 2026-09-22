import AKDM2ActualWeakEquationAbsorption
import AKCD7SameActualPureCellEndpoint

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 3000
open Set MeasureTheory
open scoped BigOperators

namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.NonlinearProduct Grad.GenericCarriers
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Algebra
open Grad.CartesianStartup

/-- The zero-order original mass row is exactly the disk L2 value norm. -/
theorem apMassRow_zero_norm {dimension : ℕ} (mass : ℝ) (field : ClosedJet dimension) :
    ‖apMassRow mass 0 field‖ = ‖closedDerivativeL2 (0, 0) field‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [PiLp.norm_sq_eq_of_L2, derivativeIndex_zero_univ, Finset.sum_singleton]
  change ‖(mass : ℂ)^0 • closedDerivativeL2 (0, 0) field‖^2 = _
  rw [pow_zero,one_smul]

/-- Pure-cell norm fidelity for the SAME original weighted field. The
moments are the genuine unbounded natural-frequency moments. -/
theorem originalCellNorm_eq_actualMoment {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (moments : StartupAllMoments dimension)
    (same : ∀ cell : ℤ, fieldCellProjection dimension openUnitDisk cell moments.field =
      closedDerivativeL2 (0, 0) (phaseWeightedJet parameters cell (core.val cell)))
    (grade : ℕ) :
    originalCellNorm parameters grade core = ‖moments.moment grade‖ := by
  have coordinate (cell : ℤ) :
      fieldCellProjection dimension openUnitDisk cell (moments.moment grade) =
        (cellFrequency cell)^grade • closedDerivativeL2 (0, 0)
          (phaseWeightedJet parameters cell (core.val cell)) := by
    rw [← same cell]
    apply Lp.ext
    filter_upwards [moments.same,fieldCellProjection_ae dimension openUnitDisk (moments.moment grade),
      fieldCellProjection_ae dimension openUnitDisk moments.field,
      Lp.coeFn_smul ((cellFrequency cell)^grade)
        (fieldCellProjection dimension openUnitDisk cell moments.field)] with point weighted one two scaled
    rw [one cell,scaled,Pi.smul_apply,two cell]
    exact weighted grade cell
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mp
  change originalCellNorm parameters grade core ^ 2 = ‖moments.moment grade‖ ^ 2
  rw [originalCellNorm_sq,Grad.CellEnergy.field_norm_sq_eq_tsum]
  apply tsum_congr
  intro cell
  rw [coordinate,norm_smul,Real.norm_of_nonneg (pow_nonneg (cellFrequency_pos cell).le _),apMassRow_zero_norm]

/-- Matching closed representatives determine the exact original moment norm. -/
theorem originalCellNorm_eq_actualMoment_of_ae {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (moments : StartupAllMoments dimension)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      moments.field point cell = closedDiskLift
        (closedMultiDerivative (phaseWeightedJet parameters cell (core.val cell)) (0, 0)) point)
    (grade : ℕ) :
    originalCellNorm parameters grade core = ‖moments.moment grade‖ := by
  apply originalCellNorm_eq_actualMoment parameters core moments
  intro cell
  apply Lp.ext
  filter_upwards [same,fieldCellProjection_ae dimension openUnitDisk moments.field,
    closedDerivativeL2_ae (phaseWeightedJet parameters cell (core.val cell)) (0, 0)] with point field projected represented
  exact (projected cell).trans ((field cell).trans represented.symm)

end Grad.OriginalCartesianTameEstimate
