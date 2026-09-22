import AEG5LiteralPhysicalCoordinateLaws

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.BoundaryKernelAction
open Grad.AnnularReconstruction Grad.AnnularTiltedReference Grad.SourceCollarCoefficients Grad.AnnularKernelL2

/-- The actual physical coefficient in the BF r^(-9/4) weighted bulk carrier.
Only the common radius power is changed; all mode-dependent phases stay original. -/
def highTiltedRowCoefficient {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ) (lower : ℝ)
    (field : DivisionRow dimension lower) (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean dimension :=
  ((radius ^ annularTiltExponent : ℝ) : ℂ) • originalRowCoefficient parameters power lower field radius mode

theorem highTiltedRowCoefficient_energy {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (lower : ℝ) (field : DivisionRow dimension lower) (radius : ℝ) (positive : 0 < radius) (mode : ℤ × ℤ) :
    ‖field mode radius‖ ^ 2 = radius *
      (radius ^ (-annularTiltExponent) * Real.exp (Grad.PhaseAlgebra.radialPhase parameters radius mode.2) *
        Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ power) ^ 2 *
      ‖highTiltedRowCoefficient parameters power lower field radius mode‖ ^ 2 := by
  rw [originalRowCoefficient_energy parameters power lower field radius positive mode,
    highTiltedRowCoefficient, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (Real.rpow_pos_of_pos positive _).le, mul_pow,
    Real.rpow_neg positive.le]
  field_simp [(Real.rpow_pos_of_pos positive annularTiltExponent).ne']

/-- Literal original r dr, full nu and unchanged analytic-width norm, including
exactly the r^(-9/4) tilt used in the actual high proof. -/
theorem highTiltedRow_norm_sq {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (lower : ℝ) (positive : 0 < lower) (field : DivisionRow dimension lower) :
    ‖field‖ ^ 2 = ∑' mode : ℤ × ℤ,
      ∫ radius, radius *
        (radius ^ (-annularTiltExponent) * Real.exp (Grad.PhaseAlgebra.radialPhase parameters radius mode.2) *
          Grad.SourceCollarDivision.annularFrequency mode.1 mode.2 ^ power) ^ 2 *
        ‖highTiltedRowCoefficient parameters power lower field radius mode‖ ^ 2
        ∂volume.restrict (Icc lower 1) := by
  rw [radialRow_norm_sq]
  apply tsum_congr
  intro mode
  rw [radialLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
  exact highTiltedRowCoefficient_energy parameters power lower field radius (positive.trans_le inside.1) mode

/-- Actual normalized reconstruction errors retain their physical Fourier
formula after the common tilt, including each original input-mode phase. -/
theorem normalizedCovariantErrorAction_tiltedPhysical (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : AnnularReconstructionState parameters L compact)
    (power : ℕ) (field : DivisionRow 7 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (normalizedCovariantErrorFamily parameters L compact lower positive bounded state radius).entry
        shift (twoFrequencyTranslation shift mode)
        (highTiltedRowCoefficient parameters power lower field radius (twoFrequencyTranslation shift mode)))
      (highTiltedRowCoefficient parameters power lower
        (normalizedCovariantErrorAction parameters L compact lower positive bounded state power field) radius mode) := by
  filter_upwards [normalizedCovariantErrorAction_physical parameters L compact lower positive bounded state power field]
    with radius actual
  intro mode
  simpa only [highTiltedRowCoefficient, map_smul] using
    (actual mode).const_smul ((radius ^ annularTiltExponent : ℝ) : ℂ)

theorem normalizedRotatedErrorAction_tiltedPhysical (parameters : PhaseParameters) (L compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower ≤ 1) (state : AnnularReconstructionState parameters L compact)
    (power : ℕ) (field : DivisionRow 7 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      HasSum (fun shift => (normalizedRotatedErrorFamily parameters L compact lower positive bounded state radius).entry
        shift (twoFrequencyTranslation shift mode)
        (highTiltedRowCoefficient parameters power lower field radius (twoFrequencyTranslation shift mode)))
      (highTiltedRowCoefficient parameters power lower
        (normalizedRotatedErrorAction parameters L compact lower positive bounded state power field) radius mode) := by
  filter_upwards [normalizedRotatedErrorAction_physical parameters L compact lower positive bounded state power field]
    with radius actual
  intro mode
  simpa only [highTiltedRowCoefficient, map_smul] using
    (actual mode).const_smul ((radius ^ annularTiltExponent : ℝ) : ℂ)

end Grad.AnnularCurrentEnergy
