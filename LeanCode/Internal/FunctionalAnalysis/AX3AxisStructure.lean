import AX2AxisCore
import FC7Conjugation

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators ComplexConjugate

namespace Grad.AxisCore

open Grad.ClosedJets Grad.CartesianState

variable (parameters : PhaseParameters) (valueDimension : ℕ)

/-- Conjugation is conjugate-linear for complex scalars. -/
theorem axisConjugation_smul (dimension : ℕ) (scalar : ℂ)
    (value : ComplexEuclidean dimension) :
    cartesianPhysicalConjugation dimension (scalar • value) =
      conj scalar • cartesianPhysicalConjugation dimension value := by
  apply PiLp.ext
  intro coordinate
  simp only [cartesianPhysicalConjugation_apply, PiLp.smul_apply, smul_eq_mul, map_mul]

theorem axisConjugation_real_smul (dimension : ℕ) (scalar : ℝ)
    (value : ComplexEuclidean dimension) :
    cartesianPhysicalConjugation dimension ((scalar : ℂ) • value) =
      (scalar : ℂ) • cartesianPhysicalConjugation dimension value := by
  rw [axisConjugation_smul, Complex.conj_ofReal]

theorem axisConjugation_real_inv_smul (dimension : ℕ) (scalar : ℝ)
    (value : ComplexEuclidean dimension) :
    cartesianPhysicalConjugation dimension (((scalar : ℂ))⁻¹ • value) =
      ((scalar : ℂ))⁻¹ • cartesianPhysicalConjugation dimension value := by
  rw [axisConjugation_smul, map_inv₀, Complex.conj_ofReal]

/-- The literal real involution of each M16 axis carrier: coordinatewise
conjugation composed with cell reversal. -/
def axisInvolution (grade : ℕ) (field : AxisGrade parameters valueDimension grade) :
    AxisGrade parameters valueDimension grade :=
  ⟨fun cell => cartesianPhysicalConjugation valueDimension (field (-cell)), by
    show Memℓp _ 2
    rw [memlp_iff_summable_sq]
    have base : Summable (fun cell : ℤ => ‖field cell‖ ^ 2) :=
      (memlp_iff_summable_sq _).mp (lp.memℓp field)
    have reindexed : Summable (fun cell : ℤ => ‖field (-cell)‖ ^ 2) :=
      ((Equiv.neg ℤ).summable_iff (f := fun cell : ℤ => ‖field cell‖ ^ 2)).mpr base
    apply reindexed.congr
    intro cell
    show ‖field (-cell)‖ ^ 2 =
      ‖cartesianPhysicalConjugation valueDimension (field (-cell))‖ ^ 2
    rw [(cartesianPhysicalConjugation valueDimension).norm_map]⟩

theorem axisInvolution_apply (grade : ℕ)
    (field : AxisGrade parameters valueDimension grade) (cell : ℤ) :
    axisInvolution parameters valueDimension grade field cell =
      cartesianPhysicalConjugation valueDimension (field (-cell)) := rfl

theorem axisInvolution_involutive (grade : ℕ)
    (field : AxisGrade parameters valueDimension grade) :
    axisInvolution parameters valueDimension grade
      (axisInvolution parameters valueDimension grade field) = field := by
  apply lp.ext
  funext cell
  rw [axisInvolution_apply, axisInvolution_apply, neg_neg]
  exact cartesianPhysicalConjugation_involutive valueDimension (field cell)

theorem axisInvolution_add (grade : ℕ)
    (first second : AxisGrade parameters valueDimension grade) :
    axisInvolution parameters valueDimension grade (first + second) =
      axisInvolution parameters valueDimension grade first +
        axisInvolution parameters valueDimension grade second := by
  apply lp.ext
  funext cell
  rw [lp.coeFn_add, Pi.add_apply, axisInvolution_apply, axisInvolution_apply,
    axisInvolution_apply, lp.coeFn_add, Pi.add_apply]
  exact (cartesianPhysicalConjugation valueDimension).map_add (first (-cell)) (second (-cell))

theorem axisInvolution_smul (grade : ℕ) (scalar : ℂ)
    (field : AxisGrade parameters valueDimension grade) :
    axisInvolution parameters valueDimension grade (scalar • field) =
      conj scalar • axisInvolution parameters valueDimension grade field := by
  apply lp.ext
  funext cell
  rw [axisInvolution_apply, lp.coeFn_smul, Pi.smul_apply, lp.coeFn_smul, Pi.smul_apply,
    axisInvolution_apply, axisConjugation_smul]

/-- The involution acts on axis coefficients by conjugation and cell
reversal: coefficient extensionality form. -/
theorem axisInvolution_coefficient (grade : ℕ)
    (field : AxisGrade parameters valueDimension grade) (cell : ℤ) :
    axisCoefficient parameters grade
        (axisInvolution parameters valueDimension grade field) cell =
      cartesianPhysicalConjugation valueDimension
        (axisCoefficient parameters grade field (-cell)) := by
  unfold axisCoefficient
  rw [axisInvolution_apply, axisConjugation_real_inv_smul, axisWeight_even]

/-- The involution is an exact isometry of each M16 carrier. -/
theorem axisInvolution_norm (grade : ℕ)
    (field : AxisGrade parameters valueDimension grade) :
    ‖axisInvolution parameters valueDimension grade field‖ = ‖field‖ := by
  have involutionFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num)
    (axisInvolution parameters valueDimension grade field)
  have fieldFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field
  norm_num at involutionFormula fieldFormula
  have squares : ‖axisInvolution parameters valueDimension grade field‖ ^ 2 =
      ‖field‖ ^ 2 := by
    rw [involutionFormula, fieldFormula]
    calc (∑' cell : ℤ, ‖axisInvolution parameters valueDimension grade field cell‖ ^ 2)
        = ∑' cell : ℤ, ‖field (-cell)‖ ^ 2 := by
          congr 1
          funext cell
          rw [axisInvolution_apply,
            (cartesianPhysicalConjugation valueDimension).norm_map]
      _ = ∑' cell : ℤ, ‖field cell‖ ^ 2 :=
          tsum_comp_neg (fun cell : ℤ => ‖field cell‖ ^ 2)
  calc ‖axisInvolution parameters valueDimension grade field‖
      = Real.sqrt (‖axisInvolution parameters valueDimension grade field‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖field‖ ^ 2) := by rw [squares]
    _ = ‖field‖ := Real.sqrt_sq (norm_nonneg _)

/-- The real involution of the all-grade axis core: the same conjugation and
cell reversal on the single coefficient family. -/
def axisCoreInvolution (family : AxisSmoothCore parameters valueDimension) :
    AxisSmoothCore parameters valueDimension :=
  ⟨fun cell => cartesianPhysicalConjugation valueDimension (family.1 (-cell)), by
    show ∀ grade : ℕ, Summable (fun cell : ℤ =>
      axisWeight parameters grade cell ^ 2 *
        ‖cartesianPhysicalConjugation valueDimension (family.1 (-cell))‖ ^ 2)
    intro grade
    have reindexed : Summable (fun cell : ℤ =>
        axisWeight parameters grade (-cell) ^ 2 * ‖family.1 (-cell)‖ ^ 2) :=
      ((Equiv.neg ℤ).summable_iff (f := fun cell : ℤ =>
        axisWeight parameters grade cell ^ 2 * ‖family.1 cell‖ ^ 2)).mpr (family.2 grade)
    apply reindexed.congr
    intro cell
    show axisWeight parameters grade (-cell) ^ 2 * ‖family.1 (-cell)‖ ^ 2 =
      axisWeight parameters grade cell ^ 2 *
        ‖cartesianPhysicalConjugation valueDimension (family.1 (-cell))‖ ^ 2
    rw [axisWeight_even, (cartesianPhysicalConjugation valueDimension).norm_map]⟩

theorem axisCoreInvolution_involutive (family : AxisSmoothCore parameters valueDimension) :
    axisCoreInvolution parameters valueDimension
      (axisCoreInvolution parameters valueDimension family) = family := by
  apply Subtype.ext
  funext cell
  show cartesianPhysicalConjugation valueDimension
      (cartesianPhysicalConjugation valueDimension (family.1 (-(-cell)))) = family.1 cell
  rw [neg_neg]
  exact cartesianPhysicalConjugation_involutive valueDimension (family.1 cell)

/-- The same-coefficient embeddings intertwine the core involution with the
carrier involutions: conjugation compatibility of the axis smooth core. -/
theorem axisEta_involution (grade : ℕ) (family : AxisSmoothCore parameters valueDimension) :
    axisEta parameters valueDimension grade
        (axisCoreInvolution parameters valueDimension family) =
      axisInvolution parameters valueDimension grade
        (axisEta parameters valueDimension grade family) := by
  apply lp.ext
  funext cell
  show (axisWeight parameters grade cell : ℂ) •
      cartesianPhysicalConjugation valueDimension (family.1 (-cell)) =
    cartesianPhysicalConjugation valueDimension
      ((axisWeight parameters grade (-cell) : ℂ) • family.1 (-cell))
  rw [axisConjugation_real_smul, axisWeight_even]

/-- The carrier involutions commute with the same-coefficient inclusions. -/
theorem axisInvolution_inclusion (grade : ℕ)
    (field : AxisGrade parameters valueDimension (grade + 1)) :
    axisInvolution parameters valueDimension grade
        (axisInclusion parameters valueDimension grade field) =
      axisInclusion parameters valueDimension grade
        (axisInvolution parameters valueDimension (grade + 1) field) := by
  apply lp.ext
  funext cell
  show cartesianPhysicalConjugation valueDimension
      ((axisWeight parameters grade (-cell) : ℂ) •
        ((axisWeight parameters (grade + 1) (-cell) : ℂ))⁻¹ • field (-cell)) =
    (axisWeight parameters grade cell : ℂ) •
      ((axisWeight parameters (grade + 1) cell : ℂ))⁻¹ •
        cartesianPhysicalConjugation valueDimension (field (-cell))
  rw [axisConjugation_real_smul, axisConjugation_real_inv_smul, axisWeight_even,
    axisWeight_even]

/-- The literal finite-support density of the all-grade axis core in each
M16 grade: every carrier element is within `epsilon` of the embedding of a
finitely supported coefficient family. -/
theorem axis_finite_support_dense (grade : ℕ)
    (field : AxisGrade parameters valueDimension grade)
    (epsilon : ℝ) (positive : 0 < epsilon) :
    ∃ core : AxisSmoothCore parameters valueDimension,
      (∃ support : Finset ℤ, ∀ cell ∉ support, core.1 cell = 0) ∧
      ‖field - axisEta parameters valueDimension grade core‖ < epsilon := by
  have expansion := lp.hasSum_single (by norm_num) field
  obtain ⟨support, closeProperty⟩ := Metric.tendsto_atTop.mp expansion epsilon positive
  have closeEnough := closeProperty support le_rfl
  have coreMembership : (fun cell : ℤ => if cell ∈ support then
      axisCoefficient parameters grade field cell else 0) ∈
      axisCoreSubmodule parameters valueDimension := by
    show ∀ innerGrade : ℕ, Summable (fun cell : ℤ =>
      axisWeight parameters innerGrade cell ^ 2 *
        ‖if cell ∈ support then axisCoefficient parameters grade field cell else 0‖ ^ 2)
    intro innerGrade
    refine (hasSum_sum_of_ne_finset_zero (s := support) ?_).summable
    intro cell outside
    show axisWeight parameters innerGrade cell ^ 2 *
      ‖if cell ∈ support then axisCoefficient parameters grade field cell else 0‖ ^ 2 = 0
    rw [if_neg outside, norm_zero]
    ring
  refine ⟨⟨_, coreMembership⟩, ⟨support, fun cell outside => ?_⟩, ?_⟩
  · show (if cell ∈ support then axisCoefficient parameters grade field cell else 0) = 0
    rw [if_neg outside]
  · have truncationIdentity : axisEta parameters valueDimension grade ⟨_, coreMembership⟩ =
        ∑ cell ∈ support, lp.single 2 cell (field cell) := by
      apply lp.ext
      funext target
      calc axisEta parameters valueDimension grade ⟨_, coreMembership⟩ target
          = (axisWeight parameters grade target : ℂ) •
              (if target ∈ support then axisCoefficient parameters grade field target
                else 0) :=
            axisEta_apply parameters valueDimension grade ⟨_, coreMembership⟩ target
        _ = (if target ∈ support then field target else 0) := by
            by_cases inside : target ∈ support
            · rw [if_pos inside, if_pos inside, axis_weighted_coefficient]
            · rw [if_neg inside, if_neg inside, smul_zero]
        _ = ∑ cell ∈ support, (if target = cell then field cell else 0) :=
            (Finset.sum_ite_eq support target fun cell => field cell).symm
        _ = ∑ cell ∈ support, lp.single 2 cell (field cell) target := by
            apply Finset.sum_congr rfl
            intro cell _
            by_cases equal : target = cell
            · subst equal
              rw [if_pos rfl, lp.single_apply_self]
            · rw [if_neg equal, lp.single_apply_ne
                (E := fun _ : ℤ => ComplexEuclidean valueDimension) 2 cell (field cell)
                equal]
        _ = (∑ cell ∈ support, lp.single 2 cell (field cell)) target := by
            rw [lp.coeFn_sum, Finset.sum_apply]
    rw [truncationIdentity, ← dist_eq_norm, dist_comm]
    exact closeEnough

end Grad.AxisCore
