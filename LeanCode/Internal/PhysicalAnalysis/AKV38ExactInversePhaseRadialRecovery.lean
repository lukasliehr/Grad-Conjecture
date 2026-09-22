import AKV37ReservedInversePhaseDiagonal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Set
open scoped ContDiff BigOperators Topology
namespace Grad.AnnularGeneralSourceRegularity
open Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.AnnularVariational Grad.SourceCollarCoefficients
open Grad.AnnularSmoothCore

theorem inversePhaseDiagonal_real_coefficient (parameters : PhaseParameters) (dimension reserve : ℕ)
    (enough : 4 ≤ reserve) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) (field : CellL2 dimension) (mode : ℤ × ℤ) :
    inversePhaseDiagonal parameters dimension reserve radius field mode =
      (inversePhaseCurve parameters mode.2 radius * (annularFrequency mode.1 mode.2 ^ reserve)⁻¹) • field mode := by
  have sum := (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).hasSum
    ((ContinuousLinearMap.apply ℂ (CellL2 dimension) field).hasSum
      (inversePhaseDiagonalTerm_summable parameters dimension reserve 0 (by simpa using enough) radius nonnegative bounded).hasSum)
  change HasSum (fun other => inversePhaseDiagonalTerm parameters dimension reserve 0 other radius field mode)
    (inversePhaseDiagonal parameters dimension reserve radius field mode) at sum
  rw [← sum.tsum_eq, tsum_eq_single mode]
  · simp [inversePhaseDiagonalTerm, fourierMatrixPoint_coordinate]
  · intro other different
    simp [inversePhaseDiagonalTerm, fourierMatrixPoint_coordinate, Ne.symm different]

theorem inversePhaseDiagonal_coefficient (parameters : PhaseParameters) (dimension reserve : ℕ)
    (enough : 4 ≤ reserve) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (field : CellL2 dimension) (mode : ℤ × ℤ) :
    inversePhaseDiagonal parameters dimension reserve radius field mode =
      ((inversePhaseCurve parameters mode.2 radius : ℂ) *
        ((annularFrequency mode.1 mode.2 : ℂ)^reserve)⁻¹) • field mode := by
  rw [inversePhaseDiagonal_real_coefficient parameters dimension reserve enough radius nonnegative bounded]
  have scalarSame :
      (inversePhaseCurve parameters mode.2 radius * (annularFrequency mode.1 mode.2 ^ reserve)⁻¹) • field mode =
      (((inversePhaseCurve parameters mode.2 radius * (annularFrequency mode.1 mode.2 ^ reserve)⁻¹ : ℝ) : ℂ)) • field mode :=
    RCLike.real_smul_eq_coe_smul _ _
  simpa only [Complex.ofReal_mul,Complex.ofReal_inv,Complex.ofReal_pow] using scalarSame

theorem inversePhaseDiagonal_cancel (parameters : PhaseParameters) (dimension reserve : ℕ)
    (enough : 4 ≤ reserve) (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1)
    (higher physical : CellL2 dimension)
    (same : ∀ mode, higher mode = (annularFrequency mode.1 mode.2 : ℂ)^reserve •
      ((Real.exp (Grad.PhaseAlgebra.radialPhase parameters radius mode.2) : ℂ) • physical mode)) :
    inversePhaseDiagonal parameters dimension reserve radius higher = physical := by
  apply lp.ext
  funext mode
  rw [inversePhaseDiagonal_coefficient parameters dimension reserve enough radius nonnegative bounded,same mode]
  rw [mul_smul,inv_smul_smul₀ (pow_ne_zero reserve (by exact_mod_cast (Grad.SourceBoundaryTrace.annularFrequency_pos mode).ne'))]
  rw [inversePhaseCurve,Real.exp_neg,Complex.ofReal_inv]
  exact inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne') _

/-- The original phase is removed at exactly the same radius, using finitely
many extra polynomial grades at each derivative order. -/
theorem inversePhaseCurve_smooth_of_weighted {dimension : ℕ}
    (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (weighted physical : ℕ → ℝ → CellL2 dimension)
    (smooth : ∀ grade, ContDiffOn ℝ ∞ (weighted grade) (Icc lower 1))
    (same : ∀ grade reserve radius, radius ∈ Icc lower 1 → ∀ mode,
      weighted (grade+reserve) radius mode = (annularFrequency mode.1 mode.2 : ℂ)^reserve •
        ((Real.exp (Grad.PhaseAlgebra.radialPhase parameters radius mode.2) : ℂ) • physical grade radius mode)) :
    ∀ grade, ContDiffOn ℝ ∞ (physical grade) (Icc lower 1) := by
  intro grade
  apply contDiffOn_infty.mpr
  intro order
  have operatorSmooth := inversePhaseDiagonal_contDiffOn parameters dimension (order+4) order (by omega) lower positive bounded
  have realSmooth := ((ContinuousLinearMap.restrictScalarsIsometry ℂ (CellL2 dimension) (CellL2 dimension) ℝ ℝ).toContinuousLinearMap.contDiff).comp_contDiffOn operatorSmooth
  have mapped := realSmooth.clm_apply (contDiffOn_infty.mp (smooth (grade+(order+4))) order)
  apply mapped.congr
  intro radius inside
  exact (inversePhaseDiagonal_cancel parameters dimension (order+4) (by omega) radius (positive.le.trans inside.1) inside.2
    _ _ (same grade (order+4) radius inside)).symm

end Grad.AnnularGeneralSourceRegularity
