import RootUnitValue
import TameTangentDot

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The tangential side of the pointwise identification: the literal Q13
axis ball on tangential families, real planar families (conjugation
symmetric cell coefficients), the pointwise planar value
`τ(ζ) = Σ_n e^{inζ} τ_n` with its envelope bound `|τ(ζ)| ≤ |τ|_0`, reality
of its components, and the pointwise value `x(τ)(ζ) = |τ(ζ)|²/2` of the
quadratic. -/

variable {parameters : PhaseParameters}

/-- The literal Q13 axis ball `‖τ‖_{T¹} < (2 C_ax)⁻¹` on tangential families. -/
def RootAxisCondition (family : TangentCoefficient parameters) : Prop :=
  tangentNorm 1 family < (2 * axisConstant)⁻¹

theorem rootAxisConstant_pos : 0 < axisConstant := by
  rw [axisConstant]
  apply Real.sqrt_pos.mpr
  have pi_large := tame_three_lt_pi
  linarith

/-- Q13 places the grade-zero planar envelope strictly below one half. -/
theorem rootAxis_planar_lt_half {family : TangentCoefficient parameters}
    (axis : RootAxisCondition family) : tangentPlanarEnvelope 0 family < 1 / 2 := by
  have bridge := tangentPlanarEnvelope_le 0 family
  rw [pow_zero, one_mul] at bridge
  have bridge_one : tangentPlanarEnvelope 0 family ≤
      axisConstant * tangentNorm 1 family := bridge
  have constant_pos := rootAxisConstant_pos
  have norm_lt : axisConstant * tangentNorm 1 family <
      axisConstant * (2 * axisConstant)⁻¹ :=
    mul_lt_mul_of_pos_left axis constant_pos
  have collapse : axisConstant * (2 * axisConstant)⁻¹ = 1 / 2 := by
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt constant_pos), one_mul, one_div]
  linarith

theorem rootAxis_planar_small {family : TangentCoefficient parameters}
    (axis : RootAxisCondition family) : tangentPlanarEnvelope 0 family < 1 :=
  lt_trans (rootAxis_planar_lt_half axis) (by norm_num)

theorem rootAxis_quadratic_small {family : TangentCoefficient parameters}
    (axis : RootAxisCondition family) :
    coefficientEnvelope 0 (tangentQuadratic family) < 1 :=
  tangentQuadratic_small (rootAxis_planar_small axis)

/-! ### Real planar families and the pointwise planar value -/

/-- Real planar families: every component is conjugation symmetric,
`τ_{-n} = conj τ_n`, so that the axial function `Σ_n τ_n e^{inζ}` is real. -/
def RealTangent (family : TangentCoefficient parameters) : Prop :=
  ∀ (cell : ℤ) (index : Fin 2),
    family.val (-cell) index = (starRingEnd ℂ) (family.val cell index)

/-- The pointwise planar value `τ(ζ) = Σ_n e^{inζ} τ_n`. -/
def planarValue (family : TangentCoefficient parameters) (zeta : ℝ) : ComplexEuclidean 2 :=
  ∑' cell, axialPhase cell zeta • family.val cell

theorem planarTerm_norm (family : TangentCoefficient parameters) (zeta : ℝ) (cell : ℤ) :
    ‖axialPhase cell zeta • family.val cell‖ = ‖family.val cell‖ := by
  rw [norm_smul, norm_axialPhase, one_mul]

theorem norm_le_tangentPlanarTerm (grade : ℕ) (family : ℤ → ComplexEuclidean 2) (cell : ℤ) :
    ‖family cell‖ ≤ tangentPlanarTerm parameters grade family cell := by
  rw [tangentPlanarTerm]
  calc ‖family cell‖ = 1 * ‖family cell‖ := (one_mul _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_right (tameWeight_one_le parameters grade cell)
      (norm_nonneg _)

theorem planar_norm_summable (family : TangentCoefficient parameters) :
    Summable (fun cell => ‖family.val cell‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun cell => norm_le_tangentPlanarTerm 0 family.val cell) (tangentPlanar_summable 0 family)

theorem planarValue_term_norm_summable (family : TangentCoefficient parameters) (zeta : ℝ) :
    Summable (fun cell => ‖axialPhase cell zeta • family.val cell‖) :=
  (planar_norm_summable family).congr (fun cell => (planarTerm_norm family zeta cell).symm)

theorem planarValue_term_summable (family : TangentCoefficient parameters) (zeta : ℝ) :
    Summable (fun cell => axialPhase cell zeta • family.val cell) :=
  Summable.of_norm (planarValue_term_norm_summable family zeta)

theorem planarValue_hasSum (family : TangentCoefficient parameters) (zeta : ℝ) :
    HasSum (fun cell => axialPhase cell zeta • family.val cell) (planarValue family zeta) :=
  (planarValue_term_summable family zeta).hasSum

/-- The pointwise bound `|τ(ζ)| ≤ |τ|_0`. -/
theorem norm_planarValue_le (family : TangentCoefficient parameters) (zeta : ℝ) :
    ‖planarValue family zeta‖ ≤ tangentPlanarEnvelope 0 family := by
  rw [planarValue]
  apply (norm_tsum_le_tsum_norm (planarValue_term_norm_summable family zeta)).trans
  rw [tangentPlanarEnvelope]
  apply (planarValue_term_norm_summable family zeta).tsum_le_tsum _
    (tangentPlanar_summable 0 family)
  intro cell
  rw [planarTerm_norm]
  exact norm_le_tangentPlanarTerm 0 family.val cell

/-- The components of the planar value are the component values. -/
theorem planarValue_apply (family : TangentCoefficient parameters) (zeta : ℝ) (index : Fin 2) :
    planarValue family zeta index = coefficientValue (tangentComponent family index) zeta := by
  have mapped := (EuclideanSpace.proj (𝕜 := ℂ) (ι := Fin 2) index).map_tsum
    (planarValue_term_summable family zeta)
  rw [planarValue]
  change EuclideanSpace.proj index (∑' cell, axialPhase cell zeta • family.val cell) = _
  rw [mapped, coefficientValue, axialValue]
  apply tsum_congr
  intro cell
  change (axialPhase cell zeta • family.val cell) index = _
  rw [PiLp.smul_apply, smul_eq_mul, tangentComponent_val, mul_comm]

/-! ### Reality of the values -/

theorem axialPhase_conj (cell : ℤ) (zeta : ℝ) :
    (starRingEnd ℂ) (axialPhase cell zeta) = axialPhase (-cell) zeta := by
  unfold axialPhase
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- A conjugation-symmetric family has real axial values. -/
theorem coefficientValue_conj {c : TameCoefficient parameters}
    (real : ∀ cell, c.val (-cell) = (starRingEnd ℂ) (c.val cell)) (zeta : ℝ) :
    (starRingEnd ℂ) (coefficientValue c zeta) = coefficientValue c zeta := by
  have sum := coefficientValue_hasSum c zeta
  have conjugated := sum.map (starRingEnd ℂ) Complex.continuous_conj
  have reflected : HasSum (fun cell => c.val (-cell) * axialPhase (-cell) zeta)
      (coefficientValue c zeta) :=
    (Equiv.neg ℤ).hasSum_iff.mpr sum
  have agree : ((starRingEnd ℂ) ∘ fun cell => c.val cell * axialPhase cell zeta) =
      fun cell => c.val (-cell) * axialPhase (-cell) zeta := by
    funext cell
    rw [Function.comp_apply, map_mul, axialPhase_conj, real cell]
  rw [agree] at conjugated
  exact conjugated.unique reflected

theorem planarValue_conj {family : TangentCoefficient parameters} (real : RealTangent family)
    (zeta : ℝ) (index : Fin 2) :
    (starRingEnd ℂ) (planarValue family zeta index) = planarValue family zeta index := by
  rw [planarValue_apply]
  exact coefficientValue_conj (fun cell => real cell index) zeta

theorem planarValue_real {family : TangentCoefficient parameters} (real : RealTangent family)
    (zeta : ℝ) (index : Fin 2) :
    planarValue family zeta index = ((planarValue family zeta index).re : ℂ) :=
  (Complex.conj_eq_iff_re.mp (planarValue_conj real zeta index)).symm

/-! ### The pointwise value of the quadratic -/

theorem coefficientValue_tangentDot (first second : TangentCoefficient parameters) (zeta : ℝ) :
    coefficientValue (tangentDot first second) zeta =
      planarValue first zeta 0 * planarValue second zeta 0 +
        planarValue first zeta 1 * planarValue second zeta 1 := by
  rw [tangentDot, coefficientValue_add, coefficientValue_mul, coefficientValue_mul,
    planarValue_apply, planarValue_apply, planarValue_apply, planarValue_apply]

theorem coefficientValue_tangentQuadratic (family : TangentCoefficient parameters) (zeta : ℝ) :
    coefficientValue (tangentQuadratic family) zeta =
      (2 : ℂ)⁻¹ * (planarValue family zeta 0 ^ 2 + planarValue family zeta 1 ^ 2) := by
  rw [tangentQuadratic, coefficientValue_smul, coefficientValue_tangentDot, sq, sq]

/-- For real planar families the quadratic evaluates to `|τ(ζ)|²/2`. -/
theorem coefficientValue_tangentQuadratic_real {family : TangentCoefficient parameters}
    (real : RealTangent family) (zeta : ℝ) :
    coefficientValue (tangentQuadratic family) zeta =
      ((‖planarValue family zeta‖ ^ 2 / 2 : ℝ) : ℂ) := by
  rw [coefficientValue_tangentQuadratic, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_two,
    planarValue_real real zeta 0, planarValue_real real zeta 1, Complex.norm_real,
    Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  push_cast
  ring

/-- On the literal Q13 ball the pointwise quadratic is strictly below `1/8`. -/
theorem rootAxis_planarValue_lt {family : TangentCoefficient parameters}
    (axis : RootAxisCondition family) (zeta : ℝ) :
    ‖planarValue family zeta‖ ^ 2 / 2 < 1 / 8 := by
  have norm_lt : ‖planarValue family zeta‖ < 1 / 2 :=
    lt_of_le_of_lt (norm_planarValue_le family zeta) (rootAxis_planar_lt_half axis)
  have nonneg := norm_nonneg (planarValue family zeta)
  nlinarith

end Grad.NonlinearQuotientBounds
