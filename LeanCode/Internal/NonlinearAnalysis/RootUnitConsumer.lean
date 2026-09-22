import RootUnitGoal

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! Immediate exact consumers of the root unit, through the goal statement
alone (no access to the construction): pointwise reality, positivity and
uniform separation from zero of the chart root on the literal Q13 ball; the
genuine first directional derivative with its Q15 estimate; the order-zero
estimate `|a(τ)|_s ≤ C_s (1 + |τ|_s)`; and its Q12 conversion to the
tangential `T^{s+1}` norm. -/

/-- On the literal Q13 ball the chart root of a real planar family is real,
positive and uniformly separated from zero at every axial point. -/
theorem rootChart_pointwise_positive (parameters : PhaseParameters)
    (family : TangentCoefficient parameters) (real : RealTangent family)
    (axis : RootAxisCondition family) (zeta : ℝ) :
    (coefficientValue (rootChart family) zeta).im = 0 ∧
      Real.sqrt (7 / 8) < (coefficientValue (rootChart family) zeta).re ∧
      0 < (coefficientValue (rootChart family) zeta).re := by
  obtain ⟨_, pointwise, _⟩ := actualRootUnit parameters
  obtain ⟨small, value⟩ := pointwise family real axis zeta
  rw [value, Complex.ofReal_im, Complex.ofReal_re]
  have separated : Real.sqrt (7 / 8) <
      Real.sqrt (1 - ‖planarValue family zeta‖ ^ 2 / 2) :=
    Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  have sqrt_nonneg := Real.sqrt_nonneg (7 / 8 : ℝ)
  exact ⟨rfl, separated, lt_of_le_of_lt sqrt_nonneg separated⟩

/-- The first derivative: the chart root has a genuine directional
derivative in every graded envelope along every tangential direction at
every Q13 base, obeying the order-one Q15 estimate
`|Da(τ)[h]|_s ≤ C_s [(1 + |τ|_s)|h|_0 + |h|_s]`. -/
theorem rootChart_first_derivative (parameters : PhaseParameters) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (base direction : TangentCoefficient parameters), RootAxisCondition base →
        ∃ value : TameCoefficient parameters,
          HasEnvDerivAt (fun t : ℝ => rootChart (base + (t : ℂ) • direction)) value ∧
          coefficientEnvelope grade value ≤
            constant * ((1 + tangentPlanarEnvelope grade base) *
                tangentPlanarEnvelope 0 direction +
              tangentPlanarEnvelope grade direction) := by
  obtain ⟨_, _, derivative, zeroth, genuine, bound⟩ := actualRootUnit parameters
  obtain ⟨constant, constant_nonneg, estimate⟩ := bound grade 1
  refine ⟨constant, constant_nonneg, ?_⟩
  intro base direction axis
  refine ⟨derivative 1 base (fun _ => direction), ?_, ?_⟩
  · have step := genuine 0 base (fun _ => direction) axis
    apply step.congr_curve
    intro t
    have tuple_eq : (fun position : Fin 0 => direction) =
        (fun position : Fin 0 => position.elim0) :=
      funext fun position => position.elim0
    calc rootChart (base + (t : ℂ) • direction)
        = derivative 0 (base + (t : ℂ) • direction)
            (fun position : Fin 0 => position.elim0) := (zeroth _).symm
      _ = derivative 0 (base + (t : ℂ) • direction) (fun position : Fin 0 => direction) := by
          rw [tuple_eq]
  · have applied := estimate base (fun _ => direction) axis
    have erase_empty : (Finset.univ : Finset (Fin 1)).erase 0 = ∅ := by decide
    rw [Fin.prod_univ_one, Fin.sum_univ_one, erase_empty, Finset.prod_empty, mul_one] at applied
    exact applied

/-- The order-zero Q15 form `|a(τ)|_s ≤ C_s (1 + |τ|_s)` on the Q13 ball. -/
theorem rootChart_grade_bound (parameters : PhaseParameters) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ base : TangentCoefficient parameters, RootAxisCondition base →
        coefficientEnvelope grade (rootChart base) ≤
          constant * (1 + tangentPlanarEnvelope grade base) := by
  obtain ⟨_, _, derivative, zeroth, _, bound⟩ := actualRootUnit parameters
  obtain ⟨constant, constant_nonneg, estimate⟩ := bound grade 0
  refine ⟨constant, constant_nonneg, ?_⟩
  intro base axis
  have applied := estimate base (fun position => position.elim0) axis
  rw [zeroth base, Fin.prod_univ_zero, Fin.sum_univ_zero, mul_one, add_zero] at applied
  exact applied

/-- The Q12 conversion of the order-zero estimate to the tangential norm:
`|a(τ)|_s ≤ C_s (1 + √2^s C_ax ‖τ‖_{T^{s+1}})`. -/
theorem rootChart_tangent_bound (parameters : PhaseParameters) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ base : TangentCoefficient parameters, RootAxisCondition base →
        coefficientEnvelope grade (rootChart base) ≤
          constant * (1 + Real.sqrt 2 ^ grade * (axisConstant * tangentNorm (grade + 1) base)) := by
  obtain ⟨constant, constant_nonneg, estimate⟩ := rootChart_grade_bound parameters grade
  refine ⟨constant, constant_nonneg, ?_⟩
  intro base axis
  have bridge := tangentPlanarEnvelope_le grade base
  apply (estimate base axis).trans
  apply mul_le_mul_of_nonneg_left _ constant_nonneg
  linarith

end Grad.NonlinearQuotientBounds
