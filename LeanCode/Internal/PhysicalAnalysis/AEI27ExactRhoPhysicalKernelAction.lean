import AEI26OriginalLowFullPhysicalPacket

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

open Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients Grad.PhaseAlgebra

/-- Explicit cancellation of the common rho^(1/2) radial factor in the
completed operator. This is independent of AHT's sqrt(r) interpretation. -/
theorem lowRhoPhysicalWeight_decode (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (radius : ℝ) (shift mode : ℤ × ℤ) :
    (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ *
      (bulkWeightRatio parameters 0 radius shift mode : ℂ) =
      (lowRhoPhysicalWeight parameters lower positive radius (twoFrequencyTranslation shift mode) : ℂ)⁻¹ := by
  have storage : lowStorageWeight lower positive radius ≠ 0 :=
    (lowPowerCurve_pos lower (-(7 / 4 : ℝ)) positive radius).ne'
  have realEquality : (lowRhoPhysicalWeight parameters lower positive radius mode)⁻¹ *
      bulkWeightRatio parameters 0 radius shift mode =
      (lowRhoPhysicalWeight parameters lower positive radius (twoFrequencyTranslation shift mode))⁻¹ := by
    simp only [lowRhoPhysicalWeight, bulkWeightRatio, pow_zero, mul_one, div_one, Real.exp_sub]
    field_simp [storage, Real.exp_ne_zero]
  exact_mod_cast realEquality

def lowRhoPhysicalCoefficient {dimension : ℕ} (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (field : DivisionRow dimension lower) (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean dimension :=
  (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ • field mode radius

/-- Exact original physical Fourier action with low rho-storage, proved from
the SAME completed bulk action and the explicit input/output cancellation. -/
theorem lowRegularAction_physical {src tgt : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius src tgt)
    (regular : RegularKernelFamily kernel) (field : DivisionRow src lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (kernel (collarRadius lower positive bounded radius)).entry shift (twoFrequencyTranslation shift mode)
        (lowRhoPhysicalCoefficient parameters lower positive field radius (twoFrequencyTranslation shift mode)))
        (lowRhoPhysicalCoefficient parameters lower positive
          (regularRadialBulkAction parameters 0 lower positive bounded kernel regular field) radius mode) := by
  filter_upwards [completedBulkKernel_ae parameters 0 lower (collarRadius lower positive bounded)
    (collarRadius_continuous lower positive bounded) (fun radius => kernel (collarRadius lower positive bounded radius))
    (regularRadialBulk_measurable parameters lower positive bounded kernel regular)
    (regularRadialBulkBound parameters 0 kernel regular)
    (regularRadialBulk_moment parameters 0 lower positive bounded kernel regular) field,
    ae_restrict_mem measurableSet_Icc] with radius actual inside
  intro mode
  have sum := actual mode
  rw [collarRadius_literal lower positive bounded radius inside] at sum
  have scaled := ((lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ •
    ContinuousLinearMap.id ℂ (ComplexEuclidean tgt)).hasSum sum
  change HasSum (fun shift => (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ •
    ((bulkWeightRatio parameters 0 radius shift mode : ℂ) •
      (kernel (collarRadius lower positive bounded radius)).entry shift (twoFrequencyTranslation shift mode)
        (field (twoFrequencyTranslation shift mode) radius)))
    (lowRhoPhysicalCoefficient parameters lower positive
      (regularRadialBulkAction parameters 0 lower positive bounded kernel regular field) radius mode) at scaled
  apply scaled.congr_fun
  intro shift
  rw [lowRhoPhysicalCoefficient, map_smul, smul_smul, lowRhoPhysicalWeight_decode parameters lower positive radius]

end Grad.AnnularCurrentLow
