import ANL6NormalBoundaryDerivative

noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal
namespace Grad.CircularNormalLift
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift
open Grad.Constraints Grad.CircularHighWeak Grad.GaugeCoefficients.Physical.WeightedTrace

abbrev NormalFiniteData := ℤ →₀ ComplexEuclidean 1

def normalBoundaryWeight (grade : ℕ) (mode : ℤ) : ℝ :=
  apBoundaryWeight 1 0 0 1 (grade - 1) (mode, 0)

theorem normalBoundaryWeight_pos (grade : ℕ) (mode : ℤ) : 0 < normalBoundaryWeight grade mode :=
  apBoundaryWeight_pos 1 0 0 1 (grade - 1) (mode, 0)

theorem normalBoundaryWeight_sq (grade : ℕ) (gradeBound : 2 ≤ grade) (mode : ℤ) :
    normalBoundaryWeight grade mode ^ 2 = boundaryFrequency (mode, 0) ^ (2 * grade - 3) := by
  have exponent : 2 * (grade - 1) - 1 = 2 * grade - 3 := by omega
  simp only [normalBoundaryWeight, apBoundaryWeight, apBoundaryPhase, Grad.AnalyticWeights.phase,
    zero_mul, sub_zero, Real.exp_zero, one_mul, Real.sq_sqrt (pow_nonneg (apBoundaryFrequency_pos 1 1 _).le _), exponent]
  congr 1
  simp [apBoundaryFrequency, boundaryFrequency]

def normalBoundaryAmbient (grade : ℕ) :
    NormalFiniteData →ₗ[ℂ] APBoundaryGrade 1 0 0 1 1 (grade - 1) where
  toFun values := ⟨fun output => if output.2 = 0 then
      (normalBoundaryWeight grade output.1 : ℂ) • values output.1 else 0, by
    classical
    change Memℓp (fun output : ℤ × ℤ => if output.2 = 0 then
      (normalBoundaryWeight grade output.1 : ℂ) • values output.1 else 0) 2
    rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)]
    apply summable_of_ne_finset_zero (s := values.support.image (fun mode => (mode, (0 : ℤ))))
    intro output missing
    by_cases cellZero : output.2 = 0
    · have modeZero : values output.1 = 0 := by
        apply Finsupp.notMem_support_iff.mp
        intro member
        apply missing
        exact Finset.mem_image.mpr ⟨output.1, member, Prod.ext rfl cellZero.symm⟩
      simp [cellZero, modeZero]
    · simp [cellZero]⟩
  map_add' first second := by
    apply lp.ext
    funext output
    change (if output.2 = 0 then (normalBoundaryWeight grade output.1 : ℂ) • (first + second) output.1 else 0) =
      (if output.2 = 0 then (normalBoundaryWeight grade output.1 : ℂ) • first output.1 else 0) +
      (if output.2 = 0 then (normalBoundaryWeight grade output.1 : ℂ) • second output.1 else 0)
    by_cases cellZero : output.2 = 0 <;> simp [cellZero, smul_add]
  map_smul' scalar values := by
    apply lp.ext
    funext output
    by_cases cellZero : output.2 = 0
    · simp only [if_pos cellZero, Finsupp.smul_apply, lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply]
      exact smul_comm _ _ _
    · simp [cellZero]

/-- The cell-zero closed subspace of the existing AP boundary grade q-1. -/
def normalBoundaryGrade (grade : ℕ) : Submodule ℂ (APBoundaryGrade 1 0 0 1 1 (grade - 1)) :=
  (normalBoundaryAmbient grade).range.topologicalClosure

def normalBoundaryInto (grade : ℕ) : NormalFiniteData →ₗ[ℂ] normalBoundaryGrade grade :=
  (normalBoundaryAmbient grade).codRestrict _ (fun values =>
    Submodule.le_topologicalClosure _ ⟨values, rfl⟩)

theorem normalBoundaryInto_denseRange (grade : ℕ) : DenseRange (normalBoundaryInto grade) := by
  have dense : DenseRange (Set.inclusion (Submodule.le_topologicalClosure (normalBoundaryAmbient grade).range)) := by
    apply (denseRange_inclusion_iff _).2
    intro point member
    exact member
  apply dense.mono
  rintro _ ⟨⟨point, values, equality⟩, rfl⟩
  exact ⟨values, Subtype.ext equality⟩

theorem normalBoundary_cell_zero (grade : ℕ) (field : normalBoundaryGrade grade)
    (mode cell : ℤ) (different : cell ≠ 0) : field.val (mode, cell) = 0 := by
  apply isClosed_property (normalBoundaryInto_denseRange grade)
    (isClosed_eq ((lp.evalCLM ℂ (fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 (mode, cell)).continuous.comp
      (normalBoundaryGrade grade).subtypeL.continuous) continuous_const) _ field
  intro values
  change (if cell = 0 then (normalBoundaryWeight grade mode : ℂ) • values mode else 0) = 0
  exact if_neg different

theorem normalBoundaryAmbient_single (grade : ℕ) (mode : ℤ) (value : ComplexEuclidean 1) :
    normalBoundaryAmbient grade (Finsupp.single mode ((normalBoundaryWeight grade mode : ℂ)⁻¹ • value)) =
      lp.single 2 (mode, 0) value := by
  classical
  apply lp.ext
  funext output
  change (if output.2 = 0 then (normalBoundaryWeight grade output.1 : ℂ) •
    (Finsupp.single mode ((normalBoundaryWeight grade mode : ℂ)⁻¹ • value)) output.1 else 0) = _
  by_cases equal : output = (mode, 0)
  · subst output
    simp only [Finsupp.single_eq_same, lp.single_apply_self]
    exact smul_inv_smul₀ (Complex.ofReal_ne_zero.mpr (normalBoundaryWeight_pos grade mode).ne') value
  · rw [lp.single_apply_ne (E := fun _ : ℤ × ℤ => ComplexEuclidean 1) 2 (mode, 0) value equal]
    by_cases cellZero : output.2 = 0
    · have modeNe : output.1 ≠ mode := fun same => equal (Prod.ext same cellZero)
      simp [cellZero, modeNe]
    · simp [cellZero]

/-- No extra regularity is hidden in the closed-subspace presentation. -/
theorem normalBoundary_mem_iff (grade : ℕ) (field : APBoundaryGrade 1 0 0 1 1 (grade - 1)) :
    field ∈ normalBoundaryGrade grade ↔ ∀ mode cell : ℤ, cell ≠ 0 → field (mode, cell) = 0 := by
  constructor
  · intro member
    exact normalBoundary_cell_zero grade ⟨field, member⟩
  · intro supported
    apply (normalBoundaryAmbient grade).range.isClosed_topologicalClosure.mem_of_tendsto
      (lp.hasSum_single (by norm_num) field)
    apply Filter.Eventually.of_forall
    intro modes
    apply Submodule.sum_mem
    intro output _
    by_cases cellZero : output.2 = 0
    · apply Submodule.le_topologicalClosure
      refine ⟨Finsupp.single output.1 ((normalBoundaryWeight grade output.1 : ℂ)⁻¹ • field output), ?_⟩
      have same : (output.1, (0 : ℤ)) = output := Prod.ext rfl cellZero.symm
      simpa only [same] using normalBoundaryAmbient_single grade output.1 (field output)
    · rw [supported output.1 output.2 cellZero, lp.single_zero]
      exact Submodule.zero_mem _

def normalBoundaryCoefficient (grade : ℕ) (field : normalBoundaryGrade grade) (mode : ℤ) : ComplexEuclidean 1 :=
  apBoundaryCoefficient 1 0 0 1 (grade - 1) field.val (mode, 0)

theorem normalBoundaryInto_coefficient (grade : ℕ) (values : NormalFiniteData) (mode : ℤ) :
    normalBoundaryCoefficient grade (normalBoundaryInto grade values) mode = values mode := by
  change (normalBoundaryWeight grade mode : ℂ)⁻¹ •
    (if (0 : ℤ) = 0 then (normalBoundaryWeight grade mode : ℂ) • values mode else 0) = _
  rw [if_pos rfl]
  exact inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (normalBoundaryWeight_pos grade mode).ne') _

theorem normalBoundary_norm_sq (grade : ℕ) (gradeBound : 2 ≤ grade) (field : normalBoundaryGrade grade) :
    ‖field‖ ^ 2 = ∑' mode : ℤ, boundaryFrequency (mode, 0) ^ (2 * grade - 3) *
      ‖normalBoundaryCoefficient grade field mode‖ ^ 2 := by
  have summable : Summable (fun output : ℤ × ℤ => ‖field.val output‖ ^ 2) := by
    have member := lp.memℓp field.val
    rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)] at member
    simpa using member
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) field.val
  norm_num at normFormula
  change ‖field.val‖ ^ 2 = _
  rw [normFormula, summable.tsum_prod]
  apply tsum_congr
  intro mode
  rw [tsum_eq_single 0]
  · have weighted := apBoundary_weighted_coefficient 1 0 0 1 (grade - 1) field.val (mode, 0)
    rw [← weighted, norm_smul, Complex.norm_real]
    change (‖normalBoundaryWeight grade mode‖ * ‖normalBoundaryCoefficient grade field mode‖) ^ 2 = _
    rw [Real.norm_of_nonneg (normalBoundaryWeight_pos grade mode).le,
      mul_pow, normalBoundaryWeight_sq grade gradeBound]
  · intro cell different
    rw [normalBoundary_cell_zero grade field mode cell different, norm_zero, zero_pow (by decide)]

theorem normalBoundaryInto_norm_sq (grade : ℕ) (gradeBound : 2 ≤ grade) (values : NormalFiniteData) :
    ‖normalBoundaryInto grade values‖ ^ 2 = normalFiniteBoundaryEnergy grade values.support values := by
  rw [normalBoundary_norm_sq grade gradeBound]
  simp_rw [normalBoundaryInto_coefficient]
  apply tsum_eq_sum
  intro mode missing
  rw [Finsupp.notMem_support_iff.mp missing, norm_zero, zero_pow (by decide), mul_zero]

end Grad.CircularNormalLift
