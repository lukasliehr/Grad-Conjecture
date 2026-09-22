import AJL5ActualRawSourceCurves

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
namespace Grad.AnnularSmoothSources
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.SourceCollarCoefficients Grad.AnnularCurrentLow
open Grad.AnnularLowEnergy Grad.PhaseAlgebra Grad.BoundaryKernelAction

/-- The exact physical rho storage inverse after cancellation of the
original forward phase against its inverse in rawPhysicalFactor. -/
def conjugatedPhysicalFactor (radius : ℝ) : ℂ :=
  ((radius ^ (-(7 / 4 : ℝ)) : ℝ) : ℂ)⁻¹

theorem rawPhysicalFactor_phase_cancel (parameters : PhaseParameters) (radius : ℝ) (mode : ℤ × ℤ) :
    (Real.exp (radialPhase parameters radius mode.2) : ℂ) * rawPhysicalFactor parameters radius mode =
      conjugatedPhysicalFactor radius := by
  have nonzero : (Real.exp (radialPhase parameters radius mode.2) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.exp_ne_zero (radialPhase parameters radius mode.2))
  unfold rawPhysicalFactor conjugatedPhysicalFactor
  rw [Complex.ofReal_mul, mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ nonzero, one_mul]

theorem conjugatedPhysicalFactor_smooth (lower : ℝ) (positive : 0 < lower) :
    ContDiffOn ℝ ∞ conjugatedPhysicalFactor (Icc lower 1) := by
  apply (Complex.ofRealCLM.contDiff.comp_contDiffOn
    (positivePower_smooth lower positive (-(7 / 4 : ℝ)))).inv
  intro radius inside
  change ((radius ^ (-(7 / 4 : ℝ)) : ℝ) : ℂ) ≠ 0
  exact_mod_cast (Real.rpow_pos_of_pos (positive.trans_le inside.1) (-(7 / 4 : ℝ))).ne'

variable {dimension : ℕ} {lower : ℝ} {field : DivisionRow dimension lower}

/-- A phase-conjugated radial Hilbert curve built from the actual finite
stored row; its coefficients carry the original inserted grade once. -/
def FiniteSmoothStoredRow.conjugatedPolynomial (source : FiniteSmoothStoredRow lower field)
    (power : ℕ) (radius : ℝ) : CellL2 dimension :=
  ∑ mode ∈ source.support, lp.single 2 mode
    ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
      (conjugatedPhysicalFactor radius • source.coefficient mode radius))

theorem FiniteSmoothStoredRow.conjugatedPolynomial_smooth (source : FiniteSmoothStoredRow lower field)
    (positive : 0 < lower) (power : ℕ) :
    ContDiffOn ℝ ∞ (source.conjugatedPolynomial power) (Icc lower 1) := by
  apply ContDiffOn.sum
  intro mode _
  exact ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).restrictScalars ℝ).contDiff.comp_contDiffOn
    (((conjugatedPhysicalFactor_smooth lower positive).smul (source.smooth mode)).const_smul _)

theorem FiniteSmoothStoredRow.conjugatedPolynomial_mode (source : FiniteSmoothStoredRow lower field)
    (power : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    source.conjugatedPolynomial power radius mode =
      (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
        (conjugatedPhysicalFactor radius • source.coefficient mode radius) := by
  classical
  rw [FiniteSmoothStoredRow.conjugatedPolynomial, lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.single_apply, Pi.single_apply]
  rw [Finset.sum_eq_single mode]
  · simp only [ite_true]
  · intro other _ different
    exact if_neg (Ne.symm different)
  · intro outside
    rw [source.outside mode outside radius, smul_zero, smul_zero]
    simp

theorem FiniteSmoothStoredRow.conjugatedPolynomial_physical (source : FiniteSmoothStoredRow lower field)
    (parameters : PhaseParameters) (power : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    source.conjugatedPolynomial power radius mode =
      (Real.exp (radialPhase parameters radius mode.2) : ℂ) •
        source.physicalPolynomial parameters power radius mode := by
  rw [source.conjugatedPolynomial_mode, source.physicalPolynomial_mode]
  rw [← rawPhysicalFactor_phase_cancel parameters radius mode, mul_smul]
  exact smul_comm _ _ _

theorem FiniteSmoothStoredRow.conjugatedPolynomial_actual (source : FiniteSmoothStoredRow lower field)
    (parameters : PhaseParameters) (positive : 0 < lower) (power : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      source.conjugatedPolynomial power radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            lowRhoPhysicalCoefficient parameters lower positive field radius mode) := by
  filter_upwards [source.physicalPolynomial_actual parameters positive power] with radius actual
  intro mode
  rw [source.conjugatedPolynomial_physical, actual mode, smul_comm]

theorem FiniteSmoothStoredRow.conjugatedPolynomial_grade (source : FiniteSmoothStoredRow lower field)
    (power : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    source.conjugatedPolynomial power radius mode =
      (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
        source.conjugatedPolynomial 0 radius mode := by
  rw [source.conjugatedPolynomial_mode, source.conjugatedPolynomial_mode, pow_zero, one_smul]

theorem FiniteSmoothStoredRow.radius_conjugatedPolynomial_actual {lower : ℝ} {row : DivisionRow 1 lower}
    (source : FiniteSmoothStoredRow lower row) (parameters : PhaseParameters)
    (positive : 0 < lower) (power : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ × ℤ,
      (source.radius positive).conjugatedPolynomial power radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
          ((Real.exp (radialPhase parameters radius mode.2) : ℂ) •
            (radius • lowRhoPhysicalCoefficient parameters lower positive row radius mode)) := by
  filter_upwards [source.radius_physicalPolynomial_actual parameters positive power] with radius actual
  intro mode
  rw [(source.radius positive).conjugatedPolynomial_physical parameters power radius mode, actual mode]
  exact smul_comm _ _ _

end Grad.AnnularSmoothSources
