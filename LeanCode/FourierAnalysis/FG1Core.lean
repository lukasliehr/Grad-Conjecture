import FG1Inclusion

noncomputable section

open TopologicalSpace
open scoped BigOperators ENNReal Topology

universe valueUniverse

namespace Grad.FourierGrade

def coefficientSingle {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (grade : ℕ) (mode : FourierMode) (value : Value) :
    JGrade Value grade :=
  lp.single 2 mode ((frequencyWeight mode : ℂ) ^ grade • value)

theorem coefficientSingle_eq_weightedSingle {Value : Type valueUniverse}
    [NormedAddCommGroup Value] [NormedSpace ℂ Value] (grade : ℕ)
    (field : JGrade Value grade) (mode : FourierMode) :
    coefficientSingle grade mode (coefficient grade field mode) =
      (lp.single (E := fun _ : FourierMode => Value) 2 mode (field mode) : JGrade Value grade) := by
  apply Subtype.ext
  funext other
  change (lp.single (E := fun _ : FourierMode => Value) 2 mode
      ((frequencyWeight mode : ℂ) ^ grade • coefficient grade field mode) :
        JGrade Value grade) other =
    (lp.single (E := fun _ : FourierMode => Value) 2 mode (field mode) : JGrade Value grade) other
  rw [weighted_coefficient grade field mode]

def finiteCoefficientSpan (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (grade : ℕ) : Submodule ℂ (JGrade Value grade) :=
  Submodule.span ℂ (⋃ mode : FourierMode, Set.range (coefficientSingle (Value := Value) grade mode))

theorem coefficientSingle_mem_span {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (grade : ℕ) (mode : FourierMode) (value : Value) :
    coefficientSingle grade mode value ∈ finiteCoefficientSpan Value grade :=
  Submodule.subset_span (Set.mem_iUnion.mpr ⟨mode, ⟨value, rfl⟩⟩)

theorem finiteCoefficientSpan_closure {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (grade : ℕ) :
    (finiteCoefficientSpan Value grade).topologicalClosure = ⊤ := by
  apply top_unique
  intro field _
  have convergence : HasSum
      (fun mode : FourierMode => coefficientSingle grade mode (coefficient grade field mode)) field := by
    convert lp.hasSum_single (p := 2) (by norm_num) field using 1
    funext mode
    exact coefficientSingle_eq_weightedSingle grade field mode
  apply (finiteCoefficientSpan Value grade).isClosed_topologicalClosure.mem_of_tendsto convergence
  exact Filter.Eventually.of_forall (fun support =>
    (finiteCoefficientSpan Value grade).topologicalClosure.sum_mem (fun mode _ =>
      (finiteCoefficientSpan Value grade).le_topologicalClosure
        (coefficientSingle_mem_span grade mode (coefficient grade field mode))))

theorem finiteCoefficientSpan_dense {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (grade : ℕ) :
    Dense (finiteCoefficientSpan Value grade : Set (JGrade Value grade)) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr (finiteCoefficientSpan_closure grade)

/-- Coefficient families lying in every literal integer Fourier grade. -/
def coreSubmodule (Value : Type valueUniverse) [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] : Submodule ℂ (FourierMode → Value) where
  carrier values := ∀ grade : ℕ,
    Memℓp (fun mode => (frequencyWeight mode : ℂ) ^ grade • values mode) 2
  zero_mem' := by
    intro grade
    have zeroMember : Memℓp (0 : FourierMode → Value) 2 := zero_memℓp
    convert zeroMember using 1
    funext mode
    exact smul_zero _
  add_mem' := by
    intro first second firstMember secondMember grade
    have added := (firstMember grade).add (secondMember grade)
    convert added using 1
    funext mode
    exact smul_add _ _ _
  smul_mem' := by
    intro scalar values member grade
    have scaled := (member grade).const_smul scalar
    convert scaled using 1
    funext mode
    simp only [Pi.smul_apply, smul_smul]
    rw [mul_comm]

abbrev JCore (Value : Type valueUniverse) [NormedAddCommGroup Value] [NormedSpace ℂ Value] :=
  coreSubmodule Value

def coreToGrade {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (grade : ℕ) : JCore Value →ₗ[ℂ] JGrade Value grade where
  toFun values := ofCoefficient grade values (values.property grade)
  map_add' first second := by
    apply Subtype.ext
    funext mode
    change (frequencyWeight mode : ℂ) ^ grade • (first.1 mode + second.1 mode) =
      (frequencyWeight mode : ℂ) ^ grade • first.1 mode +
        (frequencyWeight mode : ℂ) ^ grade • second.1 mode
    exact smul_add _ _ _
  map_smul' scalar values := by
    apply Subtype.ext
    funext mode
    change (frequencyWeight mode : ℂ) ^ grade • (scalar • values.1 mode) =
      scalar • ((frequencyWeight mode : ℂ) ^ grade • values.1 mode)
    rw [smul_smul, smul_smul, mul_comm]

set_option maxHeartbeats 800000 in
theorem coreToGrade_coefficient {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (grade : ℕ) (values : JCore Value) (mode : FourierMode) :
    coefficient grade (coreToGrade grade values) mode = values.1 mode :=
  coefficient_ofCoefficient grade values.1 (values.property grade) mode

theorem coreToGrade_injective {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (grade : ℕ) : Function.Injective (coreToGrade (Value := Value) grade) := by
  intro first second equality
  apply Subtype.ext
  funext mode
  rw [← coreToGrade_coefficient grade first mode, ← coreToGrade_coefficient grade second mode,
    equality]

def coreOfFiniteSupport {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (values : FourierMode → Value)
    (finite : Set.Finite {mode | values mode ≠ 0}) : JCore Value := by
  refine ⟨values, fun grade => ?_⟩
  apply (memℓp_zero ?_).of_exponent_ge (by norm_num : (0 : ENNReal) ≤ 2)
  exact finite.subset (fun mode weightedNonzero => by
    intro valueZero
    apply weightedNonzero
    rw [valueZero, smul_zero])

def singleCore {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (mode : FourierMode) (value : Value) : JCore Value :=
  coreOfFiniteSupport (fun other => if other = mode then value else 0) (by
    apply (Set.finite_singleton mode).subset
    intro other nonzero
    by_contra distinct
    have different : other ≠ mode := by simpa using distinct
    exact nonzero (if_neg different))

theorem coreToGrade_single {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (grade : ℕ) (mode : FourierMode) (value : Value) :
    coreToGrade grade (singleCore mode value) = coefficientSingle grade mode value := by
  apply Subtype.ext
  funext other
  change (frequencyWeight other : ℂ) ^ grade • (if other = mode then value else 0) =
    (lp.single (E := fun _ : FourierMode => Value) 2 mode
      ((frequencyWeight mode : ℂ) ^ grade • value) : JGrade Value grade) other
  rw [lp.single_apply]
  by_cases same : other = mode
  · subst other
    simp only [if_pos, Pi.single_eq_same]
  · rw [if_neg same, Pi.single_eq_of_ne same, smul_zero]

set_option maxHeartbeats 800000 in
theorem coreToGrade_dense {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (grade : ℕ) :
    Dense (LinearMap.range (coreToGrade (Value := Value) grade) : Set (JGrade Value grade)) := by
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  apply top_unique
  intro field _
  have convergence : HasSum
      (fun mode : FourierMode => coefficientSingle grade mode (coefficient grade field mode)) field := by
    convert lp.hasSum_single (p := 2) (by norm_num) field using 1
    funext mode
    exact coefficientSingle_eq_weightedSingle grade field mode
  apply (LinearMap.range (coreToGrade (Value := Value) grade)).isClosed_topologicalClosure.mem_of_tendsto
    convergence
  exact Filter.Eventually.of_forall (fun support =>
    (LinearMap.range (coreToGrade (Value := Value) grade)).topologicalClosure.sum_mem
      (fun mode _ => (LinearMap.range (coreToGrade (Value := Value) grade)).le_topologicalClosure
        ⟨singleCore mode (coefficient grade field mode),
          coreToGrade_single grade mode (coefficient grade field mode)⟩))

theorem inclusion_coreToGrade {Value : Type valueUniverse} [NormedAddCommGroup Value]
    [NormedSpace ℂ Value] (source target : ℕ) (ordered : target ≤ source)
    (values : JCore Value) :
    inclusion source target ordered (coreToGrade source values) = coreToGrade target values := by
  apply ext_coefficients
  intro mode
  rw [inclusion_coefficient, coreToGrade_coefficient, coreToGrade_coefficient]

end Grad.FourierGrade
