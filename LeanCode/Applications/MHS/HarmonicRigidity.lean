import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

noncomputable section

open Set

namespace Grad.MainAssembly.HarmonicRigidity

/-- The literal two-harmonic seed angle used by G20--G23. -/
def alphaAngle (alpha delta parameter time : ℝ) : ℝ :=
  alpha + delta * (Real.cos time + parameter * Real.sin (2 * time))

/-- Exact `NG_R09`: a continuous real function taking values in `pi * Z`
has one global integer value. -/
theorem continuous_piLattice_constant (function : ℝ → ℝ)
    (continuousFunction : Continuous function)
    (latticeValued : ∀ time, ∃ integer : ℤ,
      function time = (integer : ℝ) * Real.pi) :
    ∃ integer : ℤ, ∀ time, function time = (integer : ℝ) * Real.pi := by
  let divided := fun time : ℝ => function time / Real.pi
  have dividedContinuous : Continuous divided :=
    continuousFunction.div_const Real.pi
  have dividedMaps : MapsTo divided univ (Set.range ((↑) : ℤ → ℝ)) := by
    intro time membership
    rcases latticeValued time with ⟨integer, equality⟩
    refine ⟨integer, ?_⟩
    dsimp [divided]
    rw [equality]
    field_simp [Real.pi_ne_zero]
  have integerRangeDiscrete : IsDiscrete (Set.range ((↑) : ℤ → ℝ)) :=
    Real.isClosedEmbedding_intCast.isEmbedding.isDiscrete_range
  rcases latticeValued 0 with ⟨integer, atZero⟩
  refine ⟨integer, fun time => ?_⟩
  have dividedConstant : divided time = divided 0 :=
    isPreconnected_univ.constant_of_mapsTo integerRangeDiscrete
      dividedContinuous.continuousOn dividedMaps trivial trivial
  dsimp [divided] at dividedConstant
  rw [atZero] at dividedConstant
  field_simp [Real.pi_ne_zero] at dividedConstant
  simpa [mul_comm] using dividedConstant

private theorem alphaAngle_four_sum (alpha delta parameter shift tangentSign : ℝ)
    (tangentSignValue : tangentSign = 1 ∨ tangentSign = -1) :
    alphaAngle alpha delta parameter (tangentSign * 0 + shift) +
      alphaAngle alpha delta parameter (tangentSign * (Real.pi / 2) + shift) +
      alphaAngle alpha delta parameter (tangentSign * Real.pi + shift) +
      alphaAngle alpha delta parameter
        (tangentSign * (3 * Real.pi / 2) + shift) =
      4 * alpha := by
  rcases tangentSignValue with rfl | rfl
  · simp [alphaAngle, Real.cos_add]
    ring_nf
    have cosThreeHalf : Real.cos (Real.pi * (3 / 2)) = 0 := by
      rw [show Real.pi * (3 / 2) = Real.pi + Real.pi / 2 by ring]
      rw [Real.cos_add]
      simp
    have sinThreeHalf : Real.sin (Real.pi * (3 / 2)) = -1 := by
      rw [show Real.pi * (3 / 2) = Real.pi + Real.pi / 2 by ring]
      simp [Real.sin_add]
    rw [cosThreeHalf, sinThreeHalf, Real.sin_add_pi]
    rw [show shift * 2 + Real.pi * 2 =
      shift * 2 + 2 * Real.pi by ring, Real.sin_add_two_pi]
    rw [show shift * 2 + Real.pi * 3 =
      (shift * 2 + 2 * Real.pi) + Real.pi by ring,
      Real.sin_add_pi, Real.sin_add_two_pi]
    ring
  · simp [alphaAngle, Real.cos_add]
    ring_nf
    have cosThreeHalf : Real.cos (Real.pi * (3 / 2)) = 0 := by
      rw [show Real.pi * (3 / 2) = Real.pi + Real.pi / 2 by ring]
      rw [Real.cos_add]
      simp
    have sinThreeHalf : Real.sin (Real.pi * (3 / 2)) = -1 := by
      rw [show Real.pi * (3 / 2) = Real.pi + Real.pi / 2 by ring]
      simp [Real.sin_add]
    rw [cosThreeHalf, sinThreeHalf, Real.sin_sub_pi]
    rw [show shift * 2 - Real.pi * 2 =
      shift * 2 - 2 * Real.pi by ring, Real.sin_sub_two_pi]
    rw [show shift * 2 - Real.pi * 3 =
      (shift * 2 - 2 * Real.pi) - Real.pi by ring,
      Real.sin_sub_pi, Real.sin_sub_two_pi]
    ring

/-- Exact `NG_R10`: the four quarter-period values exclude the normal sign
and force the continuous lattice lift from `NG_R09` to be zero. -/
theorem harmonic_normal_sign_and_lattice_zero
    (alpha delta firstParameter secondParameter tangentSign normalSign shift : ℝ)
    (_deltaNonzero : delta ≠ 0)
    (alphaNotLattice : ∀ integer : ℤ,
      2 * alpha ≠ (integer : ℝ) * Real.pi)
    (tangentSignValue : tangentSign = 1 ∨ tangentSign = -1)
    (normalSignValue : normalSign = 1 ∨ normalSign = -1)
    (angleCongruence : ∀ time, ∃ integer : ℤ,
      alphaAngle alpha delta secondParameter (tangentSign * time + shift) -
          normalSign * alphaAngle alpha delta firstParameter time =
        (integer : ℝ) * Real.pi) :
    normalSign = 1 ∧
      ∀ time,
        alphaAngle alpha delta secondParameter (tangentSign * time + shift) -
          normalSign * alphaAngle alpha delta firstParameter time = 0 := by
  let difference := fun time : ℝ =>
    alphaAngle alpha delta secondParameter (tangentSign * time + shift) -
      normalSign * alphaAngle alpha delta firstParameter time
  have differenceContinuous : Continuous difference := by
    dsimp [difference, alphaAngle]
    fun_prop
  have differenceLattice : ∀ time, ∃ integer : ℤ,
      difference time = (integer : ℝ) * Real.pi := by
    exact angleCongruence
  rcases continuous_piLattice_constant difference differenceContinuous
      differenceLattice with ⟨integer, constantDifference⟩
  have shiftedSum := alphaAngle_four_sum alpha delta secondParameter shift
    tangentSign tangentSignValue
  have sourceSum := alphaAngle_four_sum alpha delta firstParameter 0 1
    (Or.inl rfl)
  have atZero := constantDifference 0
  have atQuarter := constantDifference (Real.pi / 2)
  have atHalf := constantDifference Real.pi
  have atThreeQuarters := constantDifference (3 * Real.pi / 2)
  dsimp [difference] at atZero atQuarter atHalf atThreeQuarters
  simp only [one_mul, add_zero, mul_zero] at sourceSum
  have summedIdentity :
      4 * alpha - normalSign * (4 * alpha) =
        4 * ((integer : ℝ) * Real.pi) := by
    calc
      4 * alpha - normalSign * (4 * alpha) =
          (alphaAngle alpha delta secondParameter
              (tangentSign * 0 + shift) +
            alphaAngle alpha delta secondParameter
              (tangentSign * (Real.pi / 2) + shift) +
            alphaAngle alpha delta secondParameter
              (tangentSign * Real.pi + shift) +
            alphaAngle alpha delta secondParameter
              (tangentSign * (3 * Real.pi / 2) + shift)) -
            normalSign *
              (alphaAngle alpha delta firstParameter 0 +
                alphaAngle alpha delta firstParameter (Real.pi / 2) +
                alphaAngle alpha delta firstParameter Real.pi +
                alphaAngle alpha delta firstParameter (3 * Real.pi / 2)) := by
          rw [shiftedSum, sourceSum]
      _ =
          (alphaAngle alpha delta secondParameter
              (tangentSign * 0 + shift) -
            normalSign * alphaAngle alpha delta firstParameter 0) +
          (alphaAngle alpha delta secondParameter
              (tangentSign * (Real.pi / 2) + shift) -
            normalSign * alphaAngle alpha delta firstParameter (Real.pi / 2)) +
          (alphaAngle alpha delta secondParameter
              (tangentSign * Real.pi + shift) -
            normalSign * alphaAngle alpha delta firstParameter Real.pi) +
          (alphaAngle alpha delta secondParameter
              (tangentSign * (3 * Real.pi / 2) + shift) -
            normalSign * alphaAngle alpha delta firstParameter
              (3 * Real.pi / 2)) := by ring
      _ = 4 * ((integer : ℝ) * Real.pi) := by
          rw [atZero, atQuarter, atHalf, atThreeQuarters]
          ring
  rcases normalSignValue with rfl | rfl
  · refine ⟨rfl, fun time => ?_⟩
    have integerCastZero : (integer : ℝ) = 0 := by
      have productZero : (integer : ℝ) * Real.pi = 0 := by
        nlinarith
      exact (mul_eq_zero.mp productZero).resolve_right Real.pi_ne_zero
    have equality := constantDifference time
    dsimp [difference] at equality ⊢
    rw [integerCastZero, zero_mul] at equality
    exact equality
  · exfalso
    apply alphaNotLattice integer
    nlinarith

/-- Exact `NG_R11`: after `NG_R10` has made the angle difference identically
zero, the isolated first harmonic forces the shift to be an integral `2*pi`
period. -/
theorem first_harmonic_forces_integral_period
    (alpha delta firstParameter secondParameter tangentSign shift : ℝ)
    (deltaNonzero : delta ≠ 0)
    (tangentSignValue : tangentSign = 1 ∨ tangentSign = -1)
    (angleIdentity : ∀ time,
      alphaAngle alpha delta secondParameter (tangentSign * time + shift) -
        alphaAngle alpha delta firstParameter time = 0) :
    ∃ integer : ℤ, shift = (integer : ℝ) * (2 * Real.pi) := by
  have atZero := angleIdentity 0
  have atHalf := angleIdentity Real.pi
  have cosineOne : Real.cos shift = 1 := by
    rcases tangentSignValue with rfl | rfl
    · simp [alphaAngle, Real.cos_add] at atZero atHalf
      rw [show 2 * (Real.pi + shift) = 2 * shift + 2 * Real.pi by ring,
        Real.sin_add_two_pi] at atHalf
      have factor : delta * (Real.cos shift - 1) = 0 := by
        linear_combination (atZero - atHalf) / 2
      exact sub_eq_zero.mp
        ((mul_eq_zero.mp factor).resolve_left deltaNonzero)
    · simp [alphaAngle, Real.cos_add] at atZero atHalf
      rw [show 2 * (-Real.pi + shift) = 2 * shift - 2 * Real.pi by ring,
        Real.sin_sub_two_pi] at atHalf
      have factor : delta * (Real.cos shift - 1) = 0 := by
        linear_combination (atZero - atHalf) / 2
      exact sub_eq_zero.mp
        ((mul_eq_zero.mp factor).resolve_left deltaNonzero)
  rcases (Real.cos_eq_one_iff shift).mp cosineOne with ⟨integer, equality⟩
  exact ⟨integer, equality.symm⟩

private theorem alphaAngle_add_int_two_pi
    (alpha delta parameter time : ℝ) (integer : ℤ) :
    alphaAngle alpha delta parameter
        (time + (integer : ℝ) * (2 * Real.pi)) =
      alphaAngle alpha delta parameter time := by
  have doubled :
      2 * (time + (integer : ℝ) * (2 * Real.pi)) =
        2 * time + ((2 * integer : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  simp only [alphaAngle]
  rw [Real.cos_add_int_mul_two_pi, doubled,
    Real.sin_add_int_mul_two_pi]

/-- Exact forward direction of `NG_R12`: the second harmonic, positivity and
the remaining tangent sign force equality of the two positive parameters. -/
theorem second_harmonic_forces_parameter_and_tangent_sign
    (alpha delta firstParameter secondParameter tangentSign shift : ℝ)
    (firstPositive : 0 < firstParameter)
    (secondPositive : 0 < secondParameter)
    (deltaNonzero : delta ≠ 0)
    (tangentSignValue : tangentSign = 1 ∨ tangentSign = -1)
    (shiftPeriod : ∃ integer : ℤ,
      shift = (integer : ℝ) * (2 * Real.pi))
    (angleIdentity : ∀ time,
      alphaAngle alpha delta secondParameter (tangentSign * time + shift) -
        alphaAngle alpha delta firstParameter time = 0) :
    tangentSign = 1 ∧ secondParameter = firstParameter := by
  rcases shiftPeriod with ⟨integer, rfl⟩
  have atQuarter := angleIdentity (Real.pi / 4)
  rcases tangentSignValue with rfl | rfl
  · rw [show 1 * (Real.pi / 4) + (integer : ℝ) * (2 * Real.pi) =
      Real.pi / 4 + (integer : ℝ) * (2 * Real.pi) by ring,
      alphaAngle_add_int_two_pi] at atQuarter
    refine ⟨rfl, ?_⟩
    simp [alphaAngle] at atQuarter
    rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
      Real.sin_pi_div_two] at atQuarter
    have factor : delta * (secondParameter - firstParameter) = 0 := by
      linear_combination atQuarter
    exact sub_eq_zero.mp
      ((mul_eq_zero.mp factor).resolve_left deltaNonzero)
  · rw [show (-1 : ℝ) * (Real.pi / 4) +
        (integer : ℝ) * (2 * Real.pi) =
      -(Real.pi / 4) + (integer : ℝ) * (2 * Real.pi) by ring,
      alphaAngle_add_int_two_pi] at atQuarter
    simp [alphaAngle] at atQuarter
    rw [show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
      Real.sin_pi_div_two] at atQuarter
    have factor : delta * (secondParameter + firstParameter) = 0 := by
      linear_combination -atQuarter
    have impossible : secondParameter + firstParameter = 0 :=
      (mul_eq_zero.mp factor).resolve_left deltaNonzero
    nlinarith

/-- Exact converse clause of `NG_R12`. -/
theorem harmonic_congruence_of_fixed_data
    (alpha delta parameter shift : ℝ)
    (shiftPeriod : ∃ integer : ℤ,
      shift = (integer : ℝ) * (2 * Real.pi)) :
    ∀ time, ∃ integer : ℤ,
      alphaAngle alpha delta parameter (1 * time + shift) -
          1 * alphaAngle alpha delta parameter time =
        (integer : ℝ) * Real.pi := by
  rcases shiftPeriod with ⟨integer, rfl⟩
  intro time
  refine ⟨0, ?_⟩
  rw [show 1 * time + (integer : ℝ) * (2 * Real.pi) =
    time + (integer : ℝ) * (2 * Real.pi) by ring,
    alphaAngle_add_int_two_pi]
  simp

end Grad.MainAssembly.HarmonicRigidity
