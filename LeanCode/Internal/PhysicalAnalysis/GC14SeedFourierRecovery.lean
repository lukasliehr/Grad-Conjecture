import GC14SeedRealization
import Mathlib.Analysis.Fourier.AddCircle

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

open Set MeasureTheory
open scoped BigOperators Topology Interval

namespace Grad.GaugeCoefficients.Physical.Frame

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

local instance seedPeriodPositive : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem seedCharacter_coefficient {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] [CompleteSpace Value] (source target : ℤ) (value : Value) :
    fourierCoeff (T := 2 * Real.pi)
        (fun circle : CellCircle => cellCharacter source circle • value) target =
      if source = target then value else 0 := by
  have scalarCoefficient : fourierCoeff (T := 2 * Real.pi) (fourier source) target =
      if target = source then 1 else 0 := by
    have raw := congrFun (fourierCoeff_fourier (T := 2 * Real.pi) source) target
    by_cases equality : target = source <;> simpa [Pi.single, equality] using raw
  rw [fourierCoeff]
  calc
    _ = (∫ circle : CellCircle, fourier (-target) circle * cellCharacter source circle
        ∂AddCircle.haarAddCircle) • value := by
      convert (integral_smul_const (μ := AddCircle.haarAddCircle)
        (fun circle : CellCircle => fourier (-target) circle * cellCharacter source circle) value) using 1
      simp only [mul_smul]
    _ = fourierCoeff (T := 2 * Real.pi) (fourier source) target • value := rfl
    _ = (if target = source then 1 else 0) • value :=
      congrArg (fun scalar : ℂ => scalar • value) scalarCoefficient
    _ = _ := by
      by_cases equality : source = target
      · rw [if_pos equality, if_pos equality.symm, one_smul]
      · rw [if_neg equality, if_neg (fun reverse => equality reverse.symm), zero_smul]

theorem seedCircleSeries_coefficient {Value : Type*} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] [CompleteSpace Value] (values : ℤ → Value)
    (norms : Summable (fun source => ‖values source‖)) (target : ℤ) :
    fourierCoeff (T := 2 * Real.pi)
      (fun circle : CellCircle => ∑' source : ℤ, cellCharacter source circle • values source) target =
      values target := by
  let term : ℤ → CellCircle → Value := fun source circle =>
    fourier (-target) circle • (cellCharacter source circle • values source)
  have termIntegrable : ∀ source : ℤ, Integrable (term source) AddCircle.haarAddCircle := by
    intro source
    have continuousTerm : Continuous (term source) :=
      (fourier (-target)).continuous.smul ((cellCharacter source).continuous.smul continuous_const)
    simpa only [integrableOn_univ] using
      ContinuousOn.integrableOn_compact isCompact_univ continuousTerm.continuousOn
  have seriesSummable (circle : CellCircle) :
      Summable (fun source : ℤ => cellCharacter source circle • values source) :=
    Summable.of_norm_bounded norms (fun source => by rw [norm_smul, cellCharacter_apply_norm, one_mul])
  have distribute (circle : CellCircle) :
      fourier (-target) circle • (∑' source : ℤ, cellCharacter source circle • values source) =
        ∑' source : ℤ, term source circle :=
    ((seriesSummable circle).tsum_const_smul (fourier (-target) circle)).symm
  have integralNorms : Summable (fun source : ℤ =>
      ∫ circle : CellCircle, ‖term source circle‖ ∂AddCircle.haarAddCircle) := by
    apply norms.congr
    intro source
    have integrandIdentity : (fun circle : CellCircle => ‖term source circle‖) =
        fun _ => ‖values source‖ := by
      funext circle
      simp only [term, norm_smul, cellCharacter_apply_norm, one_mul]
      rw [show ‖fourier (-target) circle‖ = 1 by exact Circle.norm_coe _, one_mul]
    rw [integrandIdentity, integral_const]
    simp
  rw [fourierCoeff]
  simp_rw [distribute]
  rw [← integral_tsum_of_summable_integral_norm termIntegrable integralNorms]
  have termIntegral (source : ℤ) :
      (∫ circle : CellCircle, term source circle ∂AddCircle.haarAddCircle) =
        if source = target then values source else 0 :=
    seedCharacter_coefficient source target (values source)
  simp_rw [termIntegral]
  rw [tsum_ite_eq target]

theorem seedCoefficient_integral {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 inputDimension outputDimension)
    (point : ClosedDisk) (target : ℤ) :
    ((2 * Real.pi : ℝ)⁻¹ : ℂ) •
      (∫ angle in (0 : ℝ)..2 * Real.pi,
        Complex.exp (-Complex.I * (target : ℂ) * angle) •
          fourierEvaluation coefficient angle point) = coefficientValue coefficient target point := by
  have recovered := seedCircleSeries_coefficient (fun source => coefficientValue coefficient source point)
    (coefficientValue_point_norm_summable admissible coefficient point) target
  rw [fourierCoeff_eq_intervalIntegral _ _ 0] at recovered
  simp only [zero_add] at recovered
  have character (angle : ℝ) :
      fourier (-target) (angle : CellCircle) = Complex.exp (-Complex.I * (target : ℂ) * angle) := by
    change cellCharacter (-target) (angle : CellCircle) = _
    rw [cellCharacter_coe]
    unfold cellExponential
    congr 1
    push_cast
    ring
  have series (angle : ℝ) :
      (∑' source : ℤ, cellCharacter source (angle : CellCircle) •
        coefficientValue coefficient source point) = fourierEvaluation coefficient angle point := by
    apply tsum_congr
    intro source
    rw [cellCharacter_coe]
    rfl
  simp_rw [character, series] at recovered
  convert recovered using 1
  simp only [one_div]
  exact_mod_cast rfl

end Grad.GaugeCoefficients.Physical.Frame
