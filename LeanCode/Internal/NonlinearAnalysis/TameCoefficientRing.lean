import TameCoefficientBridge

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState

/-! The coefficient core as a commutative convolution algebra: the submodule
of all-grade Q5-summable families, the actual cell convolution product with
its unit, and the commutative ring structure carried by exact tsum
rearrangements.  All rearrangements are justified by the envelope
summability; no completed or weakened norm is substituted. -/

variable {parameters : PhaseParameters}

/-- The all-grade Q5 coefficient core as a complex submodule. -/
def tameCoefficientSubmodule (parameters : PhaseParameters) : Submodule ℂ (ℤ → ℂ) where
  carrier := {c | TameSummableFamily parameters c}
  zero_mem' := by
    intro grade
    apply summable_zero.congr
    intro cell
    simp [tameEnvelopeTerm]
  add_mem' := by
    intro c d cSummable dSummable grade
    apply Summable.of_nonneg_of_le (tameEnvelopeTerm_nonneg parameters grade _)
      (fun cell => ?_) ((cSummable grade).add (dSummable grade))
    calc tameEnvelopeTerm parameters grade (c + d) cell
        = tameWeight parameters grade cell * ‖c cell + d cell‖ := rfl
      _ ≤ tameWeight parameters grade cell * (‖c cell‖ + ‖d cell‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (tameWeight_pos _ _ _).le
      _ = tameEnvelopeTerm parameters grade c cell +
          tameEnvelopeTerm parameters grade d cell := by
          rw [tameEnvelopeTerm, tameEnvelopeTerm]
          ring
  smul_mem' := by
    intro scalar c cSummable grade
    apply ((cSummable grade).mul_left ‖scalar‖).congr
    intro cell
    calc ‖scalar‖ * tameEnvelopeTerm parameters grade c cell
        = tameWeight parameters grade cell * (‖scalar‖ * ‖c cell‖) := by
          rw [tameEnvelopeTerm]
          ring
      _ = tameEnvelopeTerm parameters grade (scalar • c) cell := by
          rw [tameEnvelopeTerm]
          congr 1
          rw [Pi.smul_apply, norm_smul]

/-- The Q5 coefficient core carrier type. -/
abbrev TameCoefficient (parameters : PhaseParameters) : Type :=
  tameCoefficientSubmodule parameters

theorem tameCoefficient_summable (c : TameCoefficient parameters) :
    TameSummableFamily parameters c.val := c.property

/-- The convolution unit: one at the zero cell. -/
def tameDelta : ℤ → ℂ := fun cell => if cell = 0 then 1 else 0

theorem tameDelta_summable_family (parameters : PhaseParameters) :
    TameSummableFamily parameters tameDelta := by
  intro grade
  apply (hasSum_ite_eq (0 : ℤ) (tameWeight parameters grade 0 * 1)).summable.congr
  intro cell
  by_cases zeroCell : cell = 0
  · subst zeroCell
    simp [tameEnvelopeTerm, tameDelta]
  · simp [tameEnvelopeTerm, tameDelta, zeroCell]

instance : One (TameCoefficient parameters) :=
  ⟨⟨tameDelta, tameDelta_summable_family parameters⟩⟩

theorem tameOne_val : (1 : TameCoefficient parameters).val = tameDelta := rfl

instance : Mul (TameCoefficient parameters) :=
  ⟨fun c d => ⟨rawConvolution c.val d.val,
    rawConvolution_summable_family c.property d.property⟩⟩

theorem tameMul_val (c d : TameCoefficient parameters) :
    (c * d).val = rawConvolution c.val d.val := rfl

theorem tameAdd_val (c d : TameCoefficient parameters) :
    (c + d).val = c.val + d.val := rfl

theorem tameSmul_val (scalar : ℂ) (c : TameCoefficient parameters) :
    (scalar • c).val = scalar • c.val := rfl

theorem tameZero_val : (0 : TameCoefficient parameters).val = 0 := rfl

/-! ### Raw convolution identities -/

theorem rawConvolution_comm (c d : ℤ → ℂ) : rawConvolution c d = rawConvolution d c := by
  funext cell
  have reindex := (Equiv.subLeft cell).tsum_eq
    (fun shift => d shift * c (cell - shift))
  calc rawConvolution c d cell
      = ∑' shift, d (cell - shift) * c (cell - (cell - shift)) := by
        apply tsum_congr
        intro shift
        rw [sub_sub_cancel, mul_comm]
    _ = ∑' shift, d shift * c (cell - shift) := reindex
    _ = rawConvolution d c cell := rfl

theorem rawConvolution_one (c : ℤ → ℂ) : rawConvolution c tameDelta = c := by
  funext cell
  rw [rawConvolution, tsum_eq_single cell (by
    intro shift distinct
    have nonzero : cell - shift ≠ 0 := fun zero => distinct (by omega)
    rw [tameDelta]
    rw [if_neg nonzero, mul_zero])]
  rw [tameDelta, sub_self, if_pos rfl, mul_one]

theorem one_rawConvolution (c : ℤ → ℂ) : rawConvolution tameDelta c = c := by
  rw [rawConvolution_comm, rawConvolution_one]

theorem rawConvolution_zero (c : ℤ → ℂ) : rawConvolution c 0 = 0 := by
  funext cell
  rw [rawConvolution]
  simp

theorem zero_rawConvolution (c : ℤ → ℂ) : rawConvolution 0 c = 0 := by
  rw [rawConvolution_comm, rawConvolution_zero]

theorem rawConvolution_smul_left (scalar : ℂ) (c d : ℤ → ℂ) :
    rawConvolution (scalar • c) d = scalar • rawConvolution c d := by
  funext cell
  calc rawConvolution (scalar • c) d cell
      = ∑' shift, scalar * (c shift * d (cell - shift)) := by
        apply tsum_congr
        intro shift
        rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
    _ = scalar * ∑' shift, c shift * d (cell - shift) := tsum_mul_left
    _ = (scalar • rawConvolution c d) cell := rfl

theorem rawConvolution_smul_right (scalar : ℂ) (c d : ℤ → ℂ) :
    rawConvolution c (scalar • d) = scalar • rawConvolution c d := by
  rw [rawConvolution_comm, rawConvolution_smul_left, rawConvolution_comm]

theorem rawConvolution_add_left {parameters : PhaseParameters} {first second : ℤ → ℂ}
    (firstSummable : TameSummableFamily parameters first)
    (secondSummable : TameSummableFamily parameters second) (d : ℤ → ℂ)
    (dSummable : TameSummableFamily parameters d) :
    rawConvolution (first + second) d = rawConvolution first d + rawConvolution second d := by
  funext cell
  calc rawConvolution (first + second) d cell
      = ∑' shift, (first shift * d (cell - shift) + second shift * d (cell - shift)) := by
        apply tsum_congr
        intro shift
        rw [Pi.add_apply, add_mul]
    _ = (∑' shift, first shift * d (cell - shift)) +
        ∑' shift, second shift * d (cell - shift) :=
        (rawConvolution_term_summable firstSummable dSummable cell).tsum_add
          (rawConvolution_term_summable secondSummable dSummable cell)
    _ = _ := rfl

/-- The paired norm family used to justify the associativity rearrangement. -/
def tamePairShearEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun pair := (pair.1 + pair.2, pair.1)
  invFun pair := (pair.2, pair.1 - pair.2)
  left_inv pair := by
    ext
    · simp
    · simp
  right_inv pair := by
    ext
    · simp
    · simp

theorem assoc_uncurry_summable {parameters : PhaseParameters} {a b c : ℤ → ℂ}
    (aSummable : TameSummableFamily parameters a)
    (bSummable : TameSummableFamily parameters b)
    (cSummable : TameSummableFamily parameters c) (n : ℤ) :
    Summable (Function.uncurry
      (fun outer inner => (a inner * b (outer - inner)) * c (n - outer))) := by
  apply Summable.of_norm
  have pairSummable : Summable (fun pair : ℤ × ℤ => ‖a pair.1‖ * ‖b pair.2‖) :=
    aSummable.norm_summable.mul_of_nonneg bSummable.norm_summable
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have shearSummable : Summable (fun pair : ℤ × ℤ => ‖a pair.2‖ * ‖b (pair.1 - pair.2)‖) := by
    apply (tamePairShearEquiv.summable_iff
      (f := fun pair : ℤ × ℤ => ‖a pair.2‖ * ‖b (pair.1 - pair.2)‖)).mp
    apply pairSummable.congr
    intro pair
    simp [tamePairShearEquiv]
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun pair => ?_)
    (shearSummable.mul_right (tameEnvelope parameters 0 c))
  calc ‖Function.uncurry
        (fun outer inner => (a inner * b (outer - inner)) * c (n - outer)) pair‖
      = ‖a pair.2‖ * ‖b (pair.1 - pair.2)‖ * ‖c (n - pair.1)‖ := by
        rw [Function.uncurry]
        rw [norm_mul, norm_mul]
    _ ≤ ‖a pair.2‖ * ‖b (pair.1 - pair.2)‖ * tameEnvelope parameters 0 c :=
        mul_le_mul_of_nonneg_left (norm_le_tameEnvelope cSummable 0 _)
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem rawConvolution_assoc {parameters : PhaseParameters} {a b c : ℤ → ℂ}
    (aSummable : TameSummableFamily parameters a)
    (bSummable : TameSummableFamily parameters b)
    (cSummable : TameSummableFamily parameters c) :
    rawConvolution (rawConvolution a b) c = rawConvolution a (rawConvolution b c) := by
  funext n
  calc rawConvolution (rawConvolution a b) c n
      = ∑' outer, ∑' inner, (a inner * b (outer - inner)) * c (n - outer) := by
        apply tsum_congr
        intro outer
        exact tsum_mul_right.symm
    _ = ∑' inner, ∑' outer, (a inner * b (outer - inner)) * c (n - outer) :=
        ((assoc_uncurry_summable aSummable bSummable cSummable n).tsum_comm).symm
    _ = ∑' inner, ∑' shift, (a inner * b shift) * c (n - inner - shift) := by
        apply tsum_congr
        intro inner
        have reindex := (Equiv.subRight inner).tsum_eq
          (fun shift => (a inner * b shift) * c (n - inner - shift))
        calc ∑' outer, (a inner * b (outer - inner)) * c (n - outer)
            = ∑' outer, (a inner * b (outer - inner)) * c (n - inner - (outer - inner)) := by
              apply tsum_congr
              intro outer
              have cancel : n - inner - (outer - inner) = n - outer := by ring
              rw [cancel]
          _ = ∑' shift, (a inner * b shift) * c (n - inner - shift) := reindex
    _ = ∑' inner, a inner * ∑' shift, b shift * c (n - inner - shift) := by
        apply tsum_congr
        intro inner
        calc ∑' shift, (a inner * b shift) * c (n - inner - shift)
            = ∑' shift, a inner * (b shift * c (n - inner - shift)) := by
              apply tsum_congr
              intro shift
              rw [mul_assoc]
          _ = _ := tsum_mul_left
    _ = rawConvolution a (rawConvolution b c) n := rfl

/-! ### The commutative ring structure -/

/-- The additive group of the coefficient core, named for reuse. -/
abbrev tameCoefficientAddCommGroup (parameters : PhaseParameters) :
    AddCommGroup (TameCoefficient parameters) := inferInstance

instance instTameCoefficientCommRing (parameters : PhaseParameters) :
    CommRing (TameCoefficient parameters) :=
  { tameCoefficientAddCommGroup parameters with
    mul := (· * ·)
    one := 1
    mul_assoc := fun a b c => Subtype.ext
      (rawConvolution_assoc a.property b.property c.property)
    mul_comm := fun a b => Subtype.ext (rawConvolution_comm a.val b.val)
    one_mul := fun a => Subtype.ext (one_rawConvolution a.val)
    mul_one := fun a => Subtype.ext (rawConvolution_one a.val)
    left_distrib := fun a b c => Subtype.ext (by
      calc (a * (b + c)).val = rawConvolution (b.val + c.val) a.val := by
            rw [tameMul_val, rawConvolution_comm]
            rfl
        _ = rawConvolution b.val a.val + rawConvolution c.val a.val :=
            rawConvolution_add_left b.property c.property a.val a.property
        _ = (a * b + a * c).val := by
            rw [tameAdd_val, tameMul_val, tameMul_val,
              rawConvolution_comm b.val a.val, rawConvolution_comm c.val a.val])
    right_distrib := fun a b c => Subtype.ext (by
      calc ((a + b) * c).val = rawConvolution (a.val + b.val) c.val := rfl
        _ = rawConvolution a.val c.val + rawConvolution b.val c.val :=
            rawConvolution_add_left a.property b.property c.val c.property
        _ = (a * c + b * c).val := rfl)
    zero_mul := fun a => Subtype.ext (zero_rawConvolution a.val)
    mul_zero := fun a => Subtype.ext (rawConvolution_zero a.val) }

theorem tameSmul_mul (scalar : ℂ) (c d : TameCoefficient parameters) :
    (scalar • c) * d = scalar • (c * d) :=
  Subtype.ext (rawConvolution_smul_left scalar c.val d.val)

theorem tameMul_smul (scalar : ℂ) (c d : TameCoefficient parameters) :
    c * (scalar • d) = scalar • (c * d) :=
  Subtype.ext (rawConvolution_smul_right scalar c.val d.val)

theorem tamePow_val_succ (c : TameCoefficient parameters) (exponent : ℕ) :
    (c ^ (exponent + 1)).val = rawConvolution c.val ((c ^ exponent).val) := by
  rw [pow_succ, mul_comm]
  rfl

end Grad.NonlinearQuotientBounds
