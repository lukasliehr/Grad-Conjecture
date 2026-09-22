import TameRootSeries

noncomputable section

set_option maxHeartbeats 800000

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The literal Fourier evaluation of a cell-coefficient family at an axial
point `ζ`: `c(ζ) = Σ_n c_n e^{inζ}`.  On the Q5 coefficient core the sum is
absolutely convergent because every envelope weight is at least one.
Evaluation is linear and unital, multiplicative for the cell convolution
(the Cauchy product of absolutely summable `ℤ`-indexed families), bounded
by the grade-zero envelope, and commutes with every majorized series. -/

variable {parameters : PhaseParameters}

/-- The axial phase `e^{inζ}`. -/
def axialPhase (cell : ℤ) (zeta : ℝ) : ℂ :=
  Complex.exp (((cell : ℝ) * zeta : ℝ) * Complex.I)

theorem norm_axialPhase (cell : ℤ) (zeta : ℝ) : ‖axialPhase cell zeta‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem axialPhase_add (first second : ℤ) (zeta : ℝ) :
    axialPhase (first + second) zeta = axialPhase first zeta * axialPhase second zeta := by
  unfold axialPhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem axialPhase_zero (zeta : ℝ) : axialPhase 0 zeta = 1 := by
  simp [axialPhase]

/-- The phase of a cell splits along any shift: `e^{imζ} e^{i(n-m)ζ} = e^{inζ}`. -/
theorem axialPhase_sub_mul (cell shift : ℤ) (zeta : ℝ) :
    axialPhase shift zeta * axialPhase (cell - shift) zeta = axialPhase cell zeta := by
  have recover : shift + (cell - shift) = cell := by ring
  rw [← axialPhase_add, recover]

/-- The raw axial value `Σ_n c_n e^{inζ}` of a coefficient family. -/
def axialValue (c : ℤ → ℂ) (zeta : ℝ) : ℂ :=
  ∑' cell, c cell * axialPhase cell zeta

theorem norm_axialTerm (c : ℤ → ℂ) (zeta : ℝ) (cell : ℤ) :
    ‖c cell * axialPhase cell zeta‖ = ‖c cell‖ := by
  rw [norm_mul, norm_axialPhase, mul_one]

theorem axialTerm_norm_summable {c : ℤ → ℂ} (summable : Summable (fun cell => ‖c cell‖))
    (zeta : ℝ) : Summable (fun cell => ‖c cell * axialPhase cell zeta‖) :=
  summable.congr (fun cell => (norm_axialTerm c zeta cell).symm)

theorem axialTerm_summable {c : ℤ → ℂ} (summable : Summable (fun cell => ‖c cell‖))
    (zeta : ℝ) : Summable (fun cell => c cell * axialPhase cell zeta) :=
  Summable.of_norm (axialTerm_norm_summable summable zeta)

theorem axialValue_hasSum {c : ℤ → ℂ} (summable : Summable (fun cell => ‖c cell‖))
    (zeta : ℝ) : HasSum (fun cell => c cell * axialPhase cell zeta) (axialValue c zeta) :=
  (axialTerm_summable summable zeta).hasSum

theorem norm_axialValue_le {c : ℤ → ℂ} (summable : Summable (fun cell => ‖c cell‖))
    (zeta : ℝ) : ‖axialValue c zeta‖ ≤ ∑' cell, ‖c cell‖ := by
  rw [axialValue]
  apply (norm_tsum_le_tsum_norm (axialTerm_norm_summable summable zeta)).trans_eq
  exact tsum_congr (fun cell => norm_axialTerm c zeta cell)

theorem axialValue_add {c d : ℤ → ℂ} (cSummable : Summable (fun cell => ‖c cell‖))
    (dSummable : Summable (fun cell => ‖d cell‖)) (zeta : ℝ) :
    axialValue (c + d) zeta = axialValue c zeta + axialValue d zeta := by
  rw [axialValue, axialValue, axialValue,
    ← (axialTerm_summable cSummable zeta).tsum_add (axialTerm_summable dSummable zeta)]
  apply tsum_congr
  intro cell
  rw [Pi.add_apply, add_mul]

theorem axialValue_smul (scalar : ℂ) (c : ℤ → ℂ) (zeta : ℝ) :
    axialValue (scalar • c) zeta = scalar * axialValue c zeta := by
  rw [axialValue, axialValue, ← tsum_mul_left]
  apply tsum_congr
  intro cell
  rw [Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem axialValue_delta (zeta : ℝ) : axialValue tameDelta zeta = 1 := by
  rw [axialValue, tsum_eq_single (0 : ℤ) (by
    intro cell nonzero
    rw [tameDelta, if_neg nonzero, zero_mul])]
  rw [tameDelta, if_pos rfl, one_mul, axialPhase_zero]

/-- The product term of two evaluated families on cell pairs. -/
def axialProductTerm (c d : ℤ → ℂ) (zeta : ℝ) (pair : ℤ × ℤ) : ℂ :=
  (c pair.1 * axialPhase pair.1 zeta) * (d pair.2 * axialPhase pair.2 zeta)

/-- The same product in sheared coordinates `(n, m) ↦ (m, n - m)`. -/
def axialShearTerm (c d : ℤ → ℂ) (zeta : ℝ) (pair : ℤ × ℤ) : ℂ :=
  (c pair.2 * axialPhase pair.2 zeta) *
    (d (pair.1 - pair.2) * axialPhase (pair.1 - pair.2) zeta)

theorem axialShearTerm_comp (c d : ℤ → ℂ) (zeta : ℝ) (pair : ℤ × ℤ) :
    axialShearTerm c d zeta (tamePairShearEquiv pair) = axialProductTerm c d zeta pair := by
  simp only [axialShearTerm, axialProductTerm, tamePairShearEquiv, Equiv.coe_fn_mk,
    add_sub_cancel_left]

theorem axialProductTerm_summable {c d : ℤ → ℂ}
    (cSummable : TameSummableFamily parameters c)
    (dSummable : TameSummableFamily parameters d) (zeta : ℝ) :
    Summable (axialProductTerm c d zeta) := by
  have product := summable_mul_of_summable_norm
    (f := fun cell => c cell * axialPhase cell zeta)
    (g := fun cell => d cell * axialPhase cell zeta)
    (axialTerm_norm_summable cSummable.norm_summable zeta)
    (axialTerm_norm_summable dSummable.norm_summable zeta)
  exact product

theorem axialShearTerm_summable {c d : ℤ → ℂ}
    (cSummable : TameSummableFamily parameters c)
    (dSummable : TameSummableFamily parameters d) (zeta : ℝ) :
    Summable (axialShearTerm c d zeta) := by
  apply (tamePairShearEquiv.summable_iff (f := axialShearTerm c d zeta)).mp
  apply (axialProductTerm_summable cSummable dSummable zeta).congr
  intro pair
  rw [Function.comp_apply, axialShearTerm_comp]

/-- The sheared fiber sums collapse to the convolution times the phase. -/
theorem axialShearTerm_fiber (c d : ℤ → ℂ) (zeta : ℝ) (cell : ℤ) :
    (∑' shift, axialShearTerm c d zeta (cell, shift)) =
      rawConvolution c d cell * axialPhase cell zeta := by
  rw [rawConvolution, ← tsum_mul_right]
  apply tsum_congr
  intro shift
  rw [axialShearTerm, ← axialPhase_sub_mul cell shift zeta]
  ring

/-- Evaluation is multiplicative for the cell convolution: the Cauchy product
of two absolutely summable `ℤ`-indexed families, rearranged through the shear
`(n, m) ↦ (m, n - m)`. -/
theorem axialValue_rawConvolution {c d : ℤ → ℂ}
    (cSummable : TameSummableFamily parameters c)
    (dSummable : TameSummableFamily parameters d) (zeta : ℝ) :
    axialValue (rawConvolution c d) zeta = axialValue c zeta * axialValue d zeta := by
  have fNorm : Summable (fun cell => ‖c cell * axialPhase cell zeta‖) :=
    axialTerm_norm_summable cSummable.norm_summable zeta
  have gNorm : Summable (fun cell => ‖d cell * axialPhase cell zeta‖) :=
    axialTerm_norm_summable dSummable.norm_summable zeta
  have sheared := axialShearTerm_summable cSummable dSummable zeta
  calc axialValue (rawConvolution c d) zeta
      = ∑' cell, ∑' shift, axialShearTerm c d zeta (cell, shift) := by
        rw [axialValue]
        exact tsum_congr (fun cell => (axialShearTerm_fiber c d zeta cell).symm)
    _ = ∑' pair : ℤ × ℤ, axialShearTerm c d zeta pair := sheared.tsum_prod.symm
    _ = ∑' pair : ℤ × ℤ, axialShearTerm c d zeta (tamePairShearEquiv pair) :=
        (tamePairShearEquiv.tsum_eq (axialShearTerm c d zeta)).symm
    _ = ∑' pair : ℤ × ℤ, axialProductTerm c d zeta pair :=
        tsum_congr (axialShearTerm_comp c d zeta)
    _ = ∑' pair : ℤ × ℤ, (c pair.1 * axialPhase pair.1 zeta) *
          (d pair.2 * axialPhase pair.2 zeta) := rfl
    _ = axialValue c zeta * axialValue d zeta :=
        (tsum_mul_tsum_of_summable_norm
          (f := fun cell => c cell * axialPhase cell zeta)
          (g := fun cell => d cell * axialPhase cell zeta) fNorm gNorm).symm

/-! ### Evaluation of coefficient-core elements -/

/-- The axial value of a coefficient-core element at the axial point `ζ`. -/
def coefficientValue (c : TameCoefficient parameters) (zeta : ℝ) : ℂ :=
  axialValue c.val zeta

theorem coefficientValue_hasSum (c : TameCoefficient parameters) (zeta : ℝ) :
    HasSum (fun cell => c.val cell * axialPhase cell zeta) (coefficientValue c zeta) :=
  axialValue_hasSum c.property.norm_summable zeta

/-- The value is bounded by the grade-zero Q5 envelope. -/
theorem norm_coefficientValue_le (c : TameCoefficient parameters) (zeta : ℝ) :
    ‖coefficientValue c zeta‖ ≤ coefficientEnvelope 0 c := by
  apply (norm_axialValue_le c.property.norm_summable zeta).trans
  rw [coefficientEnvelope, tameEnvelope]
  exact c.property.norm_summable.tsum_le_tsum
    (fun cell => norm_le_tameEnvelopeTerm parameters 0 c.val cell) (c.property 0)

theorem coefficientValue_add (c d : TameCoefficient parameters) (zeta : ℝ) :
    coefficientValue (c + d) zeta = coefficientValue c zeta + coefficientValue d zeta := by
  rw [coefficientValue, coefficientValue, coefficientValue, tameAdd_val]
  exact axialValue_add c.property.norm_summable d.property.norm_summable zeta

theorem coefficientValue_smul (scalar : ℂ) (c : TameCoefficient parameters) (zeta : ℝ) :
    coefficientValue (scalar • c) zeta = scalar * coefficientValue c zeta := by
  rw [coefficientValue, coefficientValue, tameSmul_val]
  exact axialValue_smul scalar c.val zeta

theorem coefficientValue_one (zeta : ℝ) :
    coefficientValue (1 : TameCoefficient parameters) zeta = 1 := by
  rw [coefficientValue, tameOne_val]
  exact axialValue_delta zeta

theorem coefficientValue_mul (c d : TameCoefficient parameters) (zeta : ℝ) :
    coefficientValue (c * d) zeta = coefficientValue c zeta * coefficientValue d zeta := by
  rw [coefficientValue, coefficientValue, coefficientValue, tameMul_val]
  exact axialValue_rawConvolution c.property d.property zeta

theorem coefficientValue_pow (c : TameCoefficient parameters) (zeta : ℝ) :
    ∀ exponent : ℕ,
      coefficientValue (c ^ exponent) zeta = coefficientValue c zeta ^ exponent
  | 0 => by rw [pow_zero, pow_zero, coefficientValue_one]
  | exponent + 1 => by
      rw [pow_succ, pow_succ, coefficientValue_mul, coefficientValue_pow c zeta exponent]

theorem coefficientValue_zero (zeta : ℝ) :
    coefficientValue (0 : TameCoefficient parameters) zeta = 0 := by
  rw [coefficientValue, tameZero_val, axialValue]
  simp

/-- Evaluation at the axial point `ζ` as a ring homomorphism from the
convolution ring to `ℂ`. -/
def coefficientValueHom (zeta : ℝ) : TameCoefficient parameters →+* ℂ where
  toFun c := coefficientValue c zeta
  map_one' := coefficientValue_one zeta
  map_mul' c d := coefficientValue_mul c d zeta
  map_zero' := coefficientValue_zero zeta
  map_add' c d := coefficientValue_add c d zeta

theorem coefficientValueHom_apply (zeta : ℝ) (c : TameCoefficient parameters) :
    coefficientValueHom zeta c = coefficientValue c zeta := rfl

/-- Evaluation commutes with every majorized series: the value of the sum is
the absolutely convergent sum of the values. -/
theorem coefficientValue_tameSeries {Index : Type}
    (terms : Index → TameCoefficient parameters) {majorant : ℕ → Index → ℝ}
    (major : SeriesMajorant terms majorant) (zeta : ℝ) :
    HasSum (fun index => coefficientValue (terms index) zeta)
      (coefficientValue (tameSeries terms major) zeta) := by
  have uncurried : Summable (Function.uncurry (fun (index : Index) (cell : ℤ) =>
      (terms index).val cell * axialPhase cell zeta)) := by
    apply Summable.of_norm
    apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
    constructor
    · intro index
      exact axialTerm_norm_summable (terms index).property.norm_summable zeta
    · apply Summable.of_nonneg_of_le (fun _ => tsum_nonneg (fun _ => norm_nonneg _))
        (fun index => ?_) ((major 0).2)
      show (∑' cell, ‖(terms index).val cell * axialPhase cell zeta‖) ≤ majorant 0 index
      calc (∑' cell, ‖(terms index).val cell * axialPhase cell zeta‖)
          = ∑' cell, ‖(terms index).val cell‖ :=
            tsum_congr (fun cell => norm_axialTerm _ zeta cell)
        _ ≤ coefficientEnvelope 0 (terms index) := by
            rw [coefficientEnvelope, tameEnvelope]
            exact (terms index).property.norm_summable.tsum_le_tsum
              (fun cell => norm_le_tameEnvelopeTerm parameters 0 _ cell)
              ((terms index).property 0)
        _ ≤ majorant 0 index := (major 0).1 index
  have interchange : (∑' cell, ∑' index, (terms index).val cell * axialPhase cell zeta) =
      ∑' index, ∑' cell, (terms index).val cell * axialPhase cell zeta :=
    uncurried.tsum_comm
  have value_eq : coefficientValue (tameSeries terms major) zeta =
      ∑' index, coefficientValue (terms index) zeta := by
    calc coefficientValue (tameSeries terms major) zeta
        = ∑' cell, (∑' index, (terms index).val cell) * axialPhase cell zeta := rfl
      _ = ∑' cell, ∑' index, (terms index).val cell * axialPhase cell zeta := by
          apply tsum_congr
          intro cell
          exact tsum_mul_right.symm
      _ = ∑' index, ∑' cell, (terms index).val cell * axialPhase cell zeta := interchange
      _ = ∑' index, coefficientValue (terms index) zeta := rfl
  have valueSummable : Summable (fun index => coefficientValue (terms index) zeta) := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun index => ?_) ((major 0).2)
    exact (norm_coefficientValue_le (terms index) zeta).trans ((major 0).1 index)
  rw [value_eq]
  exact valueSummable.hasSum

theorem coefficientValue_tameSeries_eq {Index : Type}
    (terms : Index → TameCoefficient parameters) {majorant : ℕ → Index → ℝ}
    (major : SeriesMajorant terms majorant) (zeta : ℝ) :
    coefficientValue (tameSeries terms major) zeta =
      ∑' index, coefficientValue (terms index) zeta :=
  (coefficientValue_tameSeries terms major zeta).tsum_eq.symm

end Grad.NonlinearQuotientBounds
