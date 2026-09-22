import FG1Frequency

noncomputable section

open scoped BigOperators ENNReal

universe valueUniverse

namespace Grad.FourierGrade

/-- Internal weighted coordinates for the literal `J_q` sequence carrier.
The public `coefficient` removes the P14 weight. -/
abbrev JGrade (Value : Type valueUniverse) [NormedAddCommGroup Value] (_grade : ℕ) :=
  lp (fun _ : FourierMode => Value) 2

def coefficient {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (grade : ℕ) (field : JGrade Value grade) (mode : FourierMode) : Value :=
  (((frequencyWeight mode : ℂ) ^ grade)⁻¹) • field mode

def ofCoefficient {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (grade : ℕ) (values : FourierMode → Value)
    (membership : Memℓp (fun mode => (frequencyWeight mode : ℂ) ^ grade • values mode) 2) :
    JGrade Value grade :=
  ⟨fun mode => (frequencyWeight mode : ℂ) ^ grade • values mode, membership⟩

def weightedCoordinates {Value : Type valueUniverse} [NormedAddCommGroup Value] [NormedSpace ℂ Value]
    (grade : ℕ) : JGrade Value grade ≃ₗᵢ[ℂ] lp (fun _ : FourierMode => Value) 2 :=
  LinearIsometryEquiv.refl ℂ _

theorem coefficient_ofCoefficient {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (grade : ℕ) (values : FourierMode → Value)
    (membership : Memℓp (fun mode => (frequencyWeight mode : ℂ) ^ grade • values mode) 2)
    (mode : FourierMode) : coefficient grade (ofCoefficient grade values membership) mode = values mode := by
  simp only [coefficient, ofCoefficient]
  rw [inv_smul_smul₀]
  exact pow_ne_zero grade (Complex.ofReal_ne_zero.mpr (frequencyWeight_ne_zero mode))

theorem weighted_coefficient {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (grade : ℕ) (field : JGrade Value grade) (mode : FourierMode) :
    (frequencyWeight mode : ℂ) ^ grade • coefficient grade field mode = field mode := by
  simp only [coefficient]
  rw [smul_inv_smul₀]
  exact pow_ne_zero grade (Complex.ofReal_ne_zero.mpr (frequencyWeight_ne_zero mode))

theorem ext_coefficients {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] {grade : ℕ} {first second : JGrade Value grade}
    (equal : ∀ mode, coefficient grade first mode = coefficient grade second mode) : first = second := by
  apply Subtype.ext
  funext mode
  rw [← weighted_coefficient grade first mode, ← weighted_coefficient grade second mode, equal]

theorem norm_sq_eq_weighted_tsum {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (grade : ℕ) (field : JGrade Value grade) :
    ‖field‖ ^ 2 = ∑' mode : FourierMode,
      frequencyWeight mode ^ (2 * grade) * ‖coefficient grade field mode‖ ^ 2 := by
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at normFormula
  rw [normFormula]
  congr 1
  funext mode
  rw [← weighted_coefficient grade field mode, norm_smul, Complex.norm_pow,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (frequencyWeight_pos mode)]
  ring

end Grad.FourierGrade
