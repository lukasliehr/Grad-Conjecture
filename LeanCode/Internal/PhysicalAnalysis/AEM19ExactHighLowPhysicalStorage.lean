import AEM18UniformOriginalHighToLowCross
import AEG7ActualReconstructionEnergyInput

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCrossMaps
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.AnnularVariational
open Grad.AnnularLowEnergy Grad.AnnularLowReference Grad.AnnularLowCompletion Grad.AnnularCurrentLow
open Grad.BoundaryKernelAction Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularKernelL2
open Grad.AnnularOmegaGraph Grad.AnnularTiltedReference Grad.SourceCollarCoefficients Grad.PhaseAlgebra

/-- Exact BF coincidence of the high sqrt(r)*r^(-9/4) storage with the
original low rho^(1/2)=r^(-7/4). No additional tilt is put into Y. -/
theorem crossPhysicalStorageWeight (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    lowRhoPhysicalWeight parameters lower positive radius mode =
      radius ^ (-annularTiltExponent) * originalRowWeight parameters 0 radius mode := by
  have radiusPositive := positive.trans_le inside.1
  change (max lower radius) ^ (-(7 / 4 : ℝ)) * Real.exp (radialPhase parameters radius mode.2) = _
  rw [max_eq_right inside.1]
  unfold originalRowWeight
  simp only [pow_zero, mul_one]
  rw [← mul_assoc, Real.sqrt_eq_rpow, ← Real.rpow_add radiusPositive]
  norm_num [annularTiltExponent]

/-- The same completed coefficients decode to the same physical Fourier
coefficient in both sectors, for arbitrary input/output vector dimensions. -/
theorem crossPhysicalCoefficient_same {dimension : ℕ} (parameters : PhaseParameters) (lower : ℝ)
    (positive : 0 < lower) (field : DivisionRow dimension lower) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    lowRhoPhysicalCoefficient parameters lower positive field radius mode =
      highTiltedRowCoefficient parameters 0 lower field radius mode := by
  unfold lowRhoPhysicalCoefficient highTiltedRowCoefficient originalRowCoefficient
  rw [smul_smul, crossPhysicalStorageWeight parameters lower positive radius inside mode]
  congr 1
  rw [Real.rpow_neg (positive.trans_le inside.1).le]
  push_cast
  field_simp [(Real.rpow_pos_of_pos (positive.trans_le inside.1) annularTiltExponent).ne',
    (originalRowWeight_pos parameters 0 radius (positive.trans_le inside.1) mode).ne']

/-- Every original high output of the low cross map is the SAME physical
pre-Q j,c,rV convolution already established on the complete low graph. -/
theorem lowToHighBulkCross_hasSum (parameters : PhaseParameters) (lower length compact : ℝ)
    (lengthPositive : 0 < length) (positive : 0 < lower) (bounded : lower < 1)
    (state : RetainedInverseState parameters length compact) (row : Fin 3)
    (field : lowEnergyGraph lower length positive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : HighAnnularMode,
      HasSum (fun shift => (lowPhysicalRowKernel parameters length compact state row (collarRadius lower positive bounded.le radius)).entry
        shift (twoFrequencyTranslation shift mode.val)
        (lowOriginalSevenCoefficient parameters lower length positive bounded field radius (twoFrequencyTranslation shift mode.val)))
        (highTiltedRowCoefficient parameters 0 lower
          (lowPhysicalRowAction parameters length compact lower positive bounded.le state row
            (lowNormalizedSevenInput parameters lower length lengthPositive positive (field.val 0))) radius mode.val) := by
  filter_upwards [lowOriginalCurrentRow_hasSum parameters length compact lower lengthPositive positive bounded state field row,
    ae_restrict_mem measurableSet_Icc] with radius actual inside
  intro mode
  have same := crossPhysicalCoefficient_same parameters lower positive
    (lowPhysicalRowAction parameters length compact lower positive bounded.le state row
      (lowNormalizedSevenInput parameters lower length lengthPositive positive (field.val 0))) radius inside mode.val
  exact same ▸ actual mode.val

end Grad.AnnularCrossMaps
