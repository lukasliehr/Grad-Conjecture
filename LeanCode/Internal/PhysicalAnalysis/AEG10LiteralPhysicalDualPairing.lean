import AEG9ActualEightInputCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularCurrentEnergy
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.AnnularVariational
open Grad.AnnularReconstruction Grad.AnnularTiltedReference Grad.SourceCollarCoefficients

/-- The dual test has the opposite phase and radius power from the physical
field. The common square-root radial storage is divided out exactly once. -/
def highDualTestCoefficient {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ) (lower : ℝ)
    (test : DivisionRow dimension lower) (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean dimension :=
  ((radius ^ (-annularTiltExponent) * originalRowWeight parameters power radius mode / radius : ℝ) : ℂ) •
    test mode radius

theorem highDualTestCoefficient_pairing {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (lower : ℝ) (test field : DivisionRow dimension lower) (radius : ℝ) (positive : 0 < radius)
    (mode : ℤ × ℤ) :
    inner ℂ (test mode radius) (field mode radius) =
      (radius : ℂ) * inner ℂ (highDualTestCoefficient parameters power lower test radius mode)
        (highTiltedRowCoefficient parameters power lower field radius mode) := by
  rw [highDualTestCoefficient, highTiltedRowCoefficient, originalRowCoefficient,
    inner_smul_left, inner_smul_right, inner_smul_right, Complex.conj_ofReal,
    Real.rpow_neg positive.le]
  have radiusNonzero : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr positive.ne'
  have powerNonzero : ((radius ^ annularTiltExponent : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.rpow_pos_of_pos positive annularTiltExponent).ne'
  have weightNonzero : (originalRowWeight parameters power radius mode : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (originalRowWeight_pos parameters power radius positive mode).ne'
  push_cast
  field_simp

/-- The actual normalized bulk pairing is exactly the original physical
r dr dual pairing. It is linear in the field and conjugate-linear in the test. -/
theorem highBulk_originalPhysicalPairing {dimension : ℕ} (parameters : PhaseParameters) (power : ℕ)
    (lower : ℝ) (positive : 0 < lower) (test field : DivisionRow dimension lower) :
    inner ℂ test field = ∑' mode : ℤ × ℤ,
      ∫ radius, (radius : ℂ) * inner ℂ (highDualTestCoefficient parameters power lower test radius mode)
        (highTiltedRowCoefficient parameters power lower field radius mode) ∂volume.restrict (Icc lower 1) := by
  rw [physicalBulk_inner]
  apply tsum_congr
  intro mode
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with radius inside
  exact highDualTestCoefficient_pairing parameters power lower test field radius (positive.trans_le inside.1) mode

end Grad.AnnularCurrentEnergy
