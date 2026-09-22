import AKH2ReservedPhaseSlopeDiagonal

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
open Set
open scoped BigOperators Topology
namespace Grad.AnnularWeightedSmoothness
open Grad.ClosedJets Grad.CartesianState Grad.AnnularVariational Grad.SourceCollarCoefficients
open Grad.AnnularSmoothCore

theorem phaseSlopeDiagonal_real_coefficient (parameters : PhaseParameters) (dimension reserve : ℕ)
    (enough : 5 ≤ reserve) (radius : ℝ) (field : CellL2 dimension) (mode : ℤ × ℤ) :
    phaseSlopeDiagonal parameters dimension reserve radius field mode =
      (annularPhaseSlope parameters mode.2 radius * (annularFrequency mode.1 mode.2 ^ reserve)⁻¹) • field mode := by
  have sum := (lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean dimension) 2 mode).hasSum
    ((ContinuousLinearMap.apply ℂ (CellL2 dimension) field).hasSum
      (phaseSlopeDiagonalTerm_summable parameters dimension reserve 0 (by simpa using enough) radius).hasSum)
  change HasSum (fun other => phaseSlopeDiagonalTerm parameters dimension reserve 0 other radius field mode)
    (phaseSlopeDiagonal parameters dimension reserve radius field mode) at sum
  rw [← sum.tsum_eq, tsum_eq_single mode]
  · simp [phaseSlopeDiagonalTerm, fourierMatrixPoint_coordinate]
  · intro other different
    simp [phaseSlopeDiagonalTerm, fourierMatrixPoint_coordinate, Ne.symm different]

def reservedPhaseSlopeSymbol (parameters : PhaseParameters) (reserve : ℕ) (radius : ℝ)
    (mode : ℤ × ℤ) : ℂ :=
  (annularPhaseSlope parameters mode.2 radius : ℂ) * frequencyReserveSymbol reserve mode

theorem reservedPhaseSlopeSymbol_real (parameters : PhaseParameters) (reserve : ℕ) (radius : ℝ)
    (mode : ℤ × ℤ) : reservedPhaseSlopeSymbol parameters reserve radius mode =
      ((annularPhaseSlope parameters mode.2 radius * (annularFrequency mode.1 mode.2 ^ reserve)⁻¹ : ℝ) : ℂ) := by
  simp only [reservedPhaseSlopeSymbol, frequencyReserveSymbol, Complex.ofReal_mul,
    Complex.ofReal_inv, Complex.ofReal_pow]
  rfl

theorem phaseSlopeDiagonal_coefficient (parameters : PhaseParameters) (dimension reserve : ℕ)
    (enough : 5 ≤ reserve) (radius : ℝ) (field : CellL2 dimension) (mode : ℤ × ℤ) :
    phaseSlopeDiagonal parameters dimension reserve radius field mode =
      reservedPhaseSlopeSymbol parameters reserve radius mode • field mode := by
  rw [phaseSlopeDiagonal_real_coefficient parameters dimension reserve enough, reservedPhaseSlopeSymbol_real]
  exact RCLike.real_smul_eq_coe_smul _ _

theorem reservedPhaseSlopeSymbol_bound (parameters : PhaseParameters) (reserve : ℕ)
    (enough : 1 ≤ reserve) (radius : ℝ) (mode : ℤ × ℤ) :
    ‖reservedPhaseSlopeSymbol parameters reserve radius mode‖ ≤ phaseSlopeJetConstant parameters 0 := by
  have frequencyPositive : 0 < annularFrequency mode.1 mode.2 :=
    Grad.SourceBoundaryTrace.annularFrequency_pos mode
  have frequencyOne : 1 ≤ annularFrequency mode.1 mode.2 := by
    unfold annularFrequency
    linarith [abs_nonneg (mode.1 : ℝ), abs_nonneg (mode.2 : ℝ)]
  have frequencyBound : annularFrequency mode.1 mode.2 ≤ annularFrequency mode.1 mode.2 ^ reserve := by
    simpa using pow_le_pow_right₀ frequencyOne enough
  rw [reservedPhaseSlopeSymbol_real, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg frequencyPositive.le _))]
  have bound := annularPhaseSlope_iterated_bound parameters mode 0 radius
  simp only [iteratedDeriv_zero, zero_add, pow_one, Real.norm_eq_abs] at bound
  calc
    _ ≤ (phaseSlopeJetConstant parameters 0 * annularFrequency mode.1 mode.2) *
        (annularFrequency mode.1 mode.2 ^ reserve)⁻¹ :=
      mul_le_mul_of_nonneg_right bound (inv_nonneg.mpr (pow_nonneg frequencyPositive.le _))
    _ ≤ phaseSlopeJetConstant parameters 0 := by
      rw [mul_assoc]
      apply mul_le_of_le_one_right (phaseSlopeJetConstant_nonnegative parameters 0)
      rw [← div_eq_mul_inv]
      exact (div_le_one (pow_pos frequencyPositive reserve)).2 frequencyBound

theorem phaseSlopeDiagonal_boundedMultiplier (parameters : PhaseParameters) (dimension reserve : ℕ)
    (enough : 5 ≤ reserve) (radius : ℝ) :
    phaseSlopeDiagonal parameters dimension reserve radius =
      boundedHilbertMultiplier parameters dimension (reservedPhaseSlopeSymbol parameters reserve radius)
        (phaseSlopeJetConstant parameters 0) (phaseSlopeJetConstant_nonnegative parameters 0)
        (reservedPhaseSlopeSymbol_bound parameters reserve (by omega) radius) := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  exact phaseSlopeDiagonal_coefficient parameters dimension reserve enough radius field mode

theorem phaseSlopeDiagonal_norm_le (parameters : PhaseParameters) (dimension reserve : ℕ)
    (enough : 5 ≤ reserve) (radius : ℝ) :
    ‖phaseSlopeDiagonal parameters dimension reserve radius‖ ≤ phaseSlopeJetConstant parameters 0 := by
  rw [phaseSlopeDiagonal_boundedMultiplier parameters dimension reserve enough radius]
  exact Grad.BoundaryLift.coefficientOperator_norm_le parameters 0 (Equiv.refl _) _
    (phaseSlopeJetConstant_nonnegative parameters 0) _

theorem phaseSlopeDiagonal_same (parameters : PhaseParameters) (dimension reserve : ℕ)
    (enough : 5 ≤ reserve) (radius : ℝ) (higher lower : CellL2 dimension)
    (same : ∀ mode, higher mode = (annularFrequency mode.1 mode.2 : ℂ) ^ reserve • lower mode)
    (mode : ℤ × ℤ) :
    phaseSlopeDiagonal parameters dimension reserve radius higher mode =
      (annularPhaseSlope parameters mode.2 radius : ℂ) • lower mode := by
  have reserveSymbol : frequencyReserveSymbol reserve mode =
      ((annularFrequency mode.1 mode.2 : ℂ) ^ reserve)⁻¹ := rfl
  rw [phaseSlopeDiagonal_coefficient parameters dimension reserve enough, same,
    reservedPhaseSlopeSymbol, reserveSymbol, mul_smul, inv_smul_smul₀]
  exact pow_ne_zero reserve (by exact_mod_cast (Grad.SourceBoundaryTrace.annularFrequency_pos mode).ne')

theorem phaseSlopeDiagonal_comp_reserve (parameters : PhaseParameters) (dimension reserve extra : ℕ)
    (enough : 5 ≤ reserve) (radius : ℝ) :
    (phaseSlopeDiagonal parameters dimension reserve radius).comp (hilbertReserve parameters dimension extra) =
      phaseSlopeDiagonal parameters dimension (reserve + extra) radius := by
  apply ContinuousLinearMap.ext
  intro field
  apply lp.ext
  funext mode
  simp only [ContinuousLinearMap.comp_apply,
    phaseSlopeDiagonal_coefficient parameters dimension reserve enough,
    phaseSlopeDiagonal_coefficient parameters dimension (reserve + extra) (by omega),
    hilbertReserve_apply, reservedPhaseSlopeSymbol, frequencyReserveSymbol,
    smul_smul, pow_add, mul_inv_rev]
  congr 1
  ring

end Grad.AnnularWeightedSmoothness
