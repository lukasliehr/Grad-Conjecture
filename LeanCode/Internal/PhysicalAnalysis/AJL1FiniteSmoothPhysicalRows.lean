import AJE60OriginalSharedSourceConsumer
import AJH16OriginalSevenSlotSmoothness

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators ENNReal
namespace Grad.AnnularSmoothSources
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularStrongOrbit
open Grad.SourceCollarCoefficients
open Grad.AnnularCurrentLow Grad.AnnularLowEnergy Grad.PhaseAlgebra Grad.BoundaryKernelAction

/-- A literal finite radial representative of an existing stored bulk row. -/
structure FiniteSmoothStoredRow {dimension : ℕ} (lower : ℝ) (field : DivisionRow dimension lower) where
  support : Finset (ℤ × ℤ)
  coefficient : (ℤ × ℤ) → ℝ → ComplexEuclidean dimension
  smooth : ∀ mode, ContDiffOn ℝ ∞ (coefficient mode) (Icc lower 1)
  outside : ∀ mode, mode ∉ support → ∀ radius, coefficient mode radius = 0
  actual : ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode, field mode radius = coefficient mode radius

theorem positivePower_smooth (lower : ℝ) (positive : 0 < lower) (power : ℝ) :
    ContDiffOn ℝ ∞ (fun radius : ℝ => radius ^ power) (Icc lower 1) := by
  intro radius inside
  exact (Real.contDiffAt_rpow_const_of_ne (positive.trans_le inside.1).ne').contDiffWithinAt

/-- The exact original physical storage inverse, on the positive collar. -/
def rawPhysicalFactor (parameters : PhaseParameters) (radius : ℝ) (mode : ℤ × ℤ) : ℂ :=
  ((radius ^ (-(7 / 4 : ℝ)) * Real.exp (radialPhase parameters radius mode.2) : ℝ) : ℂ)⁻¹

theorem rawPhysicalFactor_smooth (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (mode : ℤ × ℤ) : ContDiffOn ℝ ∞ (fun radius => rawPhysicalFactor parameters radius mode) (Icc lower 1) := by
  have realSmooth := (positivePower_smooth lower positive (-(7 / 4 : ℝ))).mul
    (radialPhase_smooth parameters mode.2).exp.contDiffOn
  have complexSmooth := Complex.ofRealCLM.contDiff.comp_contDiffOn realSmooth
  apply complexSmooth.inv
  intro radius inside
  change ((radius ^ (-(7 / 4 : ℝ)) * Real.exp (radialPhase parameters radius mode.2) : ℝ) : ℂ) ≠ 0
  exact_mod_cast (mul_pos (Real.rpow_pos_of_pos (positive.trans_le inside.1) (-(7 / 4 : ℝ)))
    (Real.exp_pos (radialPhase parameters radius mode.2))).ne'

theorem rawPhysicalFactor_actual (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    rawPhysicalFactor parameters radius mode = (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ := by
  simp only [rawPhysicalFactor,lowRhoPhysicalWeight,lowStorageWeight,lowPowerCurve,ContinuousMap.coe_mk,max_eq_right inside.1]

variable {dimension : ℕ} {lower : ℝ} {field : DivisionRow dimension lower}

def FiniteSmoothStoredRow.physicalPolynomial (source : FiniteSmoothStoredRow lower field)
    (parameters : PhaseParameters) (power : ℕ) (radius : ℝ) : CellL2 dimension :=
  ∑ mode ∈ source.support, lp.single 2 mode
    ((Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
      (rawPhysicalFactor parameters radius mode • source.coefficient mode radius))

theorem FiniteSmoothStoredRow.physicalPolynomial_smooth (source : FiniteSmoothStoredRow lower field)
    (parameters : PhaseParameters) (positive : 0 < lower) (power : ℕ) :
    ContDiffOn ℝ ∞ (source.physicalPolynomial parameters power) (Icc lower 1) := by
  apply ContDiffOn.sum
  intro mode _
  exact ((lp.singleContinuousLinearMap ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).restrictScalars ℝ).contDiff.comp_contDiffOn
    (((rawPhysicalFactor_smooth parameters lower positive mode).smul (source.smooth mode)).const_smul _)

theorem FiniteSmoothStoredRow.physicalPolynomial_mode (source : FiniteSmoothStoredRow lower field)
    (parameters : PhaseParameters) (power : ℕ) (radius : ℝ) (mode : ℤ × ℤ) :
    source.physicalPolynomial parameters power radius mode =
      (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
        (rawPhysicalFactor parameters radius mode • source.coefficient mode radius) := by
  classical
  rw [FiniteSmoothStoredRow.physicalPolynomial,lp.coeFn_sum,Finset.sum_apply]
  simp only [lp.single_apply,Pi.single_apply]
  rw [Finset.sum_eq_single mode]
  · simp only [ite_true]
  · intro other _ different
    exact if_neg (Ne.symm different)
  · intro outside
    rw [source.outside mode outside radius,smul_zero,smul_zero]
    simp

theorem FiniteSmoothStoredRow.physicalPolynomial_actual (source : FiniteSmoothStoredRow lower field)
    (parameters : PhaseParameters) (positive : 0 < lower) (power : ℕ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      source.physicalPolynomial parameters power radius mode =
        (Grad.AnnularVariational.annularFrequency mode.1 mode.2 ^ power : ℂ) •
          lowRhoPhysicalCoefficient parameters lower positive field radius mode := by
  filter_upwards [source.actual,ae_restrict_mem measurableSet_Icc] with radius actual inside
  intro mode
  rw [source.physicalPolynomial_mode,rawPhysicalFactor_actual parameters lower positive radius inside mode,
    lowRhoPhysicalCoefficient,actual mode]

end Grad.AnnularSmoothSources
