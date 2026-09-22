import AHJ1OrdinaryDiskInterpolation

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra

theorem apMassRow_coordinate_norm {dimension grade : ℕ} (mass : ℝ) (nonnegative : 0 ≤ mass)
    (field : ClosedJet dimension) (index : DerivativeIndex grade) :
    ‖apMassRow mass grade field index‖ = mass ^ (grade - derivativeOrder index) *
      ‖closedDerivativeL2 (derivativeMultiIndex index) field‖ := by
  change ‖(mass : ℂ) ^ (grade - derivativeOrder index) • _‖ = _
  rw [norm_smul, Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg nonnegative]

/-- Multiplying the actual lower row by the missing mass power is bounded
by the original higher row, uniformly for every mass at least one. -/
theorem apMassRow_lower_power {dimension low high : ℕ} (mass : ℝ) (oneLe : 1 ≤ mass)
    (ordered : low ≤ high) (field : ClosedJet dimension) :
    mass ^ (high - low) * ‖apMassRow mass low field‖ ≤
      apLoweringConstant low * ‖apMassRow mass high field‖ := by
  have nonnegative : 0 ≤ mass := zero_le_one.trans oneLe
  have bounded (index : DerivativeIndex low) :
      ‖((mass : ℂ) ^ (high - low) • apMassRow mass low field) index‖ ≤ ‖apMassRow mass high field‖ := by
    let target := apDerivativeAtGrade index high (index.property.trans ordered)
    have coordinate : ((mass : ℂ) ^ (high - low) • apMassRow mass low field) index =
        apMassRow mass high field target := by
      change (mass : ℂ) ^ (high - low) • ((mass : ℂ) ^ (low - derivativeOrder index) • closedDerivativeL2 (derivativeMultiIndex index) field) =
        (mass : ℂ) ^ (high - derivativeOrder index) • closedDerivativeL2 (derivativeMultiIndex index) field
      rw [smul_smul, ← pow_add]
      congr 2
      have indexBound := index.property
      change derivativeOrder index ≤ low at indexBound
      omega
    rw [coordinate]
    exact PiLp.norm_apply_le (apMassRow mass high field) target
  have result := apRow_norm_bound_of_coordinates
    ((mass : ℂ) ^ (high - low) • apMassRow mass low field) _ (norm_nonneg _) bounded
  rw [norm_smul, Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg nonnegative] at result
  exact result

/-- The same higher row also controls the ordinary lower disk Sobolev row
with the missing mass power. -/
theorem apMassRow_ordinary_power {dimension low high : ℕ} (mass : ℝ) (oneLe : 1 ≤ mass)
    (ordered : low ≤ high) (field : ClosedJet dimension) :
    mass ^ (high - low) * ‖apMassRow 1 low field‖ ≤
      apLoweringConstant low * ‖apMassRow mass high field‖ := by
  have nonnegative : 0 ≤ mass := zero_le_one.trans oneLe
  have bounded (index : DerivativeIndex low) :
      ‖((mass : ℂ) ^ (high - low) • apMassRow 1 low field) index‖ ≤ ‖apMassRow mass high field‖ := by
    let target := apDerivativeAtGrade index high (index.property.trans ordered)
    change ‖(mass : ℂ) ^ (high - low) • ((1 : ℂ) ^ (low - derivativeOrder index) • closedDerivativeL2 (derivativeMultiIndex index) field)‖ ≤ _
    rw [one_pow, one_smul, norm_smul, Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg nonnegative]
    have powers : mass ^ (high - low) ≤ mass ^ (high - derivativeOrder index) :=
      pow_le_pow_right₀ oneLe (Nat.sub_le_sub_left index.property high)
    calc
      _ ≤ mass ^ (high - derivativeOrder index) * ‖closedDerivativeL2 (derivativeMultiIndex index) field‖ :=
        mul_le_mul_of_nonneg_right powers (norm_nonneg _)
      _ = ‖apMassRow mass high field target‖ := (apMassRow_coordinate_norm mass nonnegative field target).symm
      _ ≤ _ := PiLp.norm_apply_le (apMassRow mass high field) target
  have result := apRow_norm_bound_of_coordinates
    ((mass : ℂ) ^ (high - low) • apMassRow 1 low field) _ (norm_nonneg _) bounded
  rw [norm_smul, Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg nonnegative] at result
  exact result

theorem apMassRow_ordinary_le {dimension grade : ℕ} (mass : ℝ) (oneLe : 1 ≤ mass)
    (field : ClosedJet dimension) :
    ‖apMassRow 1 grade field‖ ≤ apLoweringConstant grade * ‖apMassRow mass grade field‖ := by
  simpa only [Nat.sub_self, pow_zero, one_mul] using apMassRow_ordinary_power mass oneLe (le_refl grade) field

theorem apMassRow_coordinate_low {dimension low high : ℕ} (mass : ℝ) (oneLe : 1 ≤ mass)
    (ordered : low ≤ high) (field : ClosedJet dimension) (index : DerivativeIndex high)
    (indexBound : derivativeOrder index ≤ low) :
    ‖apMassRow mass high field index‖ ≤ mass ^ (high - low) * ‖apMassRow mass low field‖ := by
  let target := apDerivativeAtGrade index low indexBound
  have coordinate : apMassRow mass high field index =
      (mass : ℂ) ^ (high - low) • apMassRow mass low field target := by
    change (mass : ℂ) ^ (high - derivativeOrder index) • closedDerivativeL2 (derivativeMultiIndex index) field =
      (mass : ℂ) ^ (high - low) • ((mass : ℂ) ^ (low - derivativeOrder index) • closedDerivativeL2 (derivativeMultiIndex index) field)
    rw [smul_smul, ← pow_add]
    congr 2
    omega
  rw [coordinate, norm_smul, Complex.norm_pow, Complex.norm_real,
    Real.norm_of_nonneg (zero_le_one.trans oneLe)]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le (apMassRow mass low field) target)
    (pow_nonneg (zero_le_one.trans oneLe) _)

end Grad.GaugeCoefficients.Physical.RadialLedger
