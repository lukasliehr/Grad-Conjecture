import ACE10VolterraDerivativeBounds

noncomputable section
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct

theorem kernelMass_le_inverse_factorial (count : ℕ) : kernelMass count ≤ 1 / (count.factorial : ℝ) := by
  unfold kernelMass
  apply one_div_le_one_div_of_le (by positivity)
  have power : (1 : ℝ) ≤ 4 ^ count := one_le_pow₀ (by norm_num)
  have factorial : (1 : ℝ) ≤ ((count + 1).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (count + 1)
  calc
    _ ≤ 4 ^ count * (count.factorial : ℝ) := le_mul_of_one_le_left (by positivity) power
    _ ≤ _ := le_mul_of_one_le_right (by positivity) factorial

theorem kernelMass_succ_le (count : ℕ) : kernelMass (count + 1) ≤ kernelMass count := by
  rw [kernelMass_succ]
  apply div_le_self (kernelMass_positive count).le
  have nonnegative : (0 : ℝ) ≤ count := Nat.cast_nonneg count
  nlinarith

def volterraSeriesMajorant {dimension : ℕ} (parameter : ℝ) (field : ClosedJet dimension)
    (grade count : ℕ) : ℝ :=
  |parameter| ^ count * volterraPowerMajorant grade (count + 1) field

theorem volterraSeriesMajorant_nonnegative {dimension : ℕ} (parameter : ℝ)
    (field : ClosedJet dimension) (grade count : ℕ) :
    0 ≤ volterraSeriesMajorant parameter field grade count := by
  have first := leibnizEnvelope_one_le grade
  have second := sourceDerivativeEnvelope_one_le grade field
  have third := radiusIterationConstant_one_le grade
  have fourth := kernelMass_positive (count + 1)
  unfold volterraSeriesMajorant volterraPowerMajorant
  positivity

theorem volterraSeriesMajorant_summable {dimension : ℕ} (parameter : ℝ)
    (field : ClosedJet dimension) (grade : ℕ) :
    Summable (volterraSeriesMajorant parameter field grade) := by
  have first := leibnizEnvelope_one_le grade
  have second := sourceDerivativeEnvelope_one_le grade field
  have third := radiusIterationConstant_one_le grade
  let constant := leibnizEnvelope grade * sourceDerivativeEnvelope grade field * radiusIterationConstant grade
  have comparison := (Real.summable_pow_div_factorial (|parameter| * radiusIterationConstant grade)).mul_left constant
  apply Summable.of_nonneg_of_le (volterraSeriesMajorant_nonnegative parameter field grade) _ comparison
  intro count
  have massBound := (kernelMass_succ_le count).trans (kernelMass_le_inverse_factorial count)
  calc
    _ = (|parameter| ^ count * (leibnizEnvelope grade * sourceDerivativeEnvelope grade field *
        radiusIterationConstant grade ^ (count + 1))) * kernelMass (count + 1) := by
      unfold volterraSeriesMajorant volterraPowerMajorant
      ring
    _ ≤ (|parameter| ^ count * (leibnizEnvelope grade * sourceDerivativeEnvelope grade field *
        radiusIterationConstant grade ^ (count + 1))) * (1 / (count.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left massBound (by positivity)
    _ = constant * ((|parameter| * radiusIterationConstant grade) ^ count / (count.factorial : ℝ)) := by
      dsimp only [constant]
      rw [mul_pow, pow_succ]
      ring

/-- The literal resolvent summand. The parameter is arbitrary real, so the
construction includes zero without a division by the parameter. -/
def volterraSeriesTerm {dimension : ℕ} (parameter : ℝ) (field : ClosedJet dimension)
    (count : ℕ) : SpatialPlane → ComplexEuclidean dimension :=
  parameter ^ count • volterraPowerValue (count + 1) field

theorem volterraSeriesTerm_smooth {dimension : ℕ} (parameter : ℝ)
    (field : ClosedJet dimension) (count : ℕ) :
    ContDiff ℝ ∞ (volterraSeriesTerm parameter field count) :=
  (volterraPowerValue_smooth (count + 1) field).const_smul (parameter ^ count)

theorem volterraSeriesTerm_operator_bound {dimension : ℕ} (parameter : ℝ)
    (field : ClosedJet dimension) (grade count : ℕ) (point : SpatialPlane)
    (inside : point ∈ closedUnitDisk) :
    ‖iteratedFDeriv ℝ grade (volterraSeriesTerm parameter field count) point‖ ≤
      volterraSeriesMajorant parameter field grade count := by
  unfold volterraSeriesTerm
  rw [iteratedFDeriv_const_smul_apply
    ((volterraPowerValue_smooth (count + 1) field).of_le (by exact_mod_cast le_top)).contDiffAt,
    norm_smul, Real.norm_eq_abs, abs_pow]
  exact mul_le_mul_of_nonneg_left
    (volterraPower_operator_bound grade (count + 1) grade le_rfl field ⟨point, inside⟩)
    (pow_nonneg (abs_nonneg _) _)

end Grad.ActualCenterVolterra
