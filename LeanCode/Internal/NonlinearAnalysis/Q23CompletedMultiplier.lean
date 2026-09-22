import Q23SeedMultiplier
import GaugeModeAlgebra

noncomputable section

set_option maxHeartbeats 2400000

open Set Filter
open scoped BigOperators ContDiff ENNReal Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.Constraints.Gauges Grad.Constraints.Seed
open Grad.GaugeCoefficients.Algebra

theorem q23RealSmooth_linearFunction_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (linear : F → G) (additive : ∀ x y, linear (x + y) = linear x + linear y)
    (scalar : ∀ (r : ℝ) x, linear (r • x) = r • linear x)
    (continuous : Continuous linear)
    (mapping : E → F) (domain : Set E)
    (smooth : ContDiffOn ℝ ∞ mapping domain) :
    ContDiffOn ℝ ∞ (fun point => linear (mapping point)) domain := by
  let bundled : F →L[ℝ] G :=
    { toFun := linear, map_add' := additive, map_smul' := scalar, cont := continuous }
  exact bundled.contDiff.comp_contDiffOn smooth

theorem q23IteratedFDeriv_linearFunction_comp {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (linear : F → G) (additive : ∀ x y, linear (x + y) = linear x + linear y)
    (scalar : ∀ (r : ℝ) x, linear (r • x) = r • linear x)
    (continuous : Continuous linear) (mapping : E → F) (point : E)
    (smooth : ContDiffAt ℝ ∞ mapping point) (order : ℕ)
    (directions : Fin order → E) :
    (iteratedFDeriv ℝ order (fun x => linear (mapping x)) point) directions =
      linear ((iteratedFDeriv ℝ order mapping point) directions) := by
  let bundled : F →L[ℝ] G :=
    { toFun := linear, map_add' := additive, map_smul' := scalar, cont := continuous }
  have identity := bundled.iteratedFDeriv_comp_left smooth
    (i := order) (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))
  exact congrArg (fun derivative => derivative directions) identity

/-! The weighted `ℓ¹` seed carrier acts boundedly on each completed original
grade.  This realizes the accepted coefficient-space smoothness as genuine
operator-norm smoothness, rather than only pointwise differentiation on the
smooth core. -/

def weightedMultiplierCoefficients (phase : PhaseParameters) (grade : ℕ)
    (sequence : WeightedSequence) (cell : ℤ) : OperatorValue 2 2 :=
  ((sequenceWeight phase grade cell : ℂ)⁻¹) • sequence cell

theorem weightedMultiplier_envelopeTerm (phase : PhaseParameters) (grade : ℕ)
    (sequence : WeightedSequence) (cell : ℤ) :
    envelopeTerm phase grade (weightedMultiplierCoefficients phase grade sequence) cell =
      ‖sequence cell‖ := by
  unfold envelopeTerm weightedMultiplierCoefficients
  change sequenceWeight phase grade cell *
      ‖((sequenceWeight phase grade cell : ℂ)⁻¹) • sequence cell‖ = ‖sequence cell‖
  rw [← Seed.weighted_norm, smul_smul, mul_inv_cancel₀, one_smul]
  exact Complex.ofReal_ne_zero.mpr (sequenceWeight_pos phase grade cell).ne'

theorem weightedMultiplierCoefficients_summable (phase : PhaseParameters)
    (grade : ℕ) (sequence : WeightedSequence) :
    Summable (envelopeTerm phase grade
      (weightedMultiplierCoefficients phase grade sequence)) := by
  have normSummable : Summable (fun cell : ℤ => ‖sequence cell‖) := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      (lp.memℓp sequence).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
  apply normSummable.congr
  intro cell
  exact (weightedMultiplier_envelopeTerm phase grade sequence cell).symm

theorem weightedMultiplier_envelope (phase : PhaseParameters) (grade : ℕ)
    (sequence : WeightedSequence) :
    envelope phase grade (weightedMultiplierCoefficients phase grade sequence) =
      ‖sequence‖ := by
  rw [envelope, Seed.weightedSequence_norm]
  apply tsum_congr
  intro cell
  exact weightedMultiplier_envelopeTerm phase grade sequence cell

def weightedCompletedMultiplier (phase : PhaseParameters) (grade : ℕ)
    (sequence : WeightedSequence) :
    AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade :=
  completedMultiplier phase (weightedMultiplierCoefficients phase grade sequence)

theorem singleModeCompleted_add_map (phase : PhaseParameters) (grade : ℕ)
    (cell : ℤ) (first second : OperatorValue 2 2) :
    singleModeCompleted (grade := grade) phase cell (first + second) =
      singleModeCompleted phase cell first + singleModeCompleted phase cell second := by
  apply denseCoreContinuousLinearMap_ext phase
  intro field
  rw [singleModeCompleted_eta]
  change aGradeEta phase (singleModeGradeCore phase cell (first + second) field) =
    singleModeCompleted phase cell first (aGradeEta phase field) +
      singleModeCompleted phase cell second (aGradeEta phase field)
  rw [singleModeCompleted_eta, singleModeCompleted_eta,
    singleModeGradeCore_add_map, map_add]

theorem singleModeCompleted_smul_map (phase : PhaseParameters) (grade : ℕ)
    (cell : ℤ) (scalar : ℂ) (mapping : OperatorValue 2 2) :
    singleModeCompleted (grade := grade) phase cell (scalar • mapping) =
      scalar • singleModeCompleted phase cell mapping := by
  apply denseCoreContinuousLinearMap_ext phase
  intro field
  rw [singleModeCompleted_eta]
  change aGradeEta phase (singleModeGradeCore phase cell (scalar • mapping) field) =
    scalar • singleModeCompleted phase cell mapping (aGradeEta phase field)
  rw [singleModeCompleted_eta, singleModeGradeCore_smul_map, map_smul]

theorem weightedCompletedMultiplier_add (phase : PhaseParameters) (grade : ℕ)
    (first second : WeightedSequence) :
    weightedCompletedMultiplier phase grade (first + second) =
      weightedCompletedMultiplier phase grade first +
        weightedCompletedMultiplier phase grade second := by
  unfold weightedCompletedMultiplier completedMultiplier
  have firstSummable := completedModes_summable phase
    (weightedMultiplierCoefficients phase grade first)
    (weightedMultiplierCoefficients_summable phase grade first)
  have secondSummable := completedModes_summable phase
    (weightedMultiplierCoefficients phase grade second)
    (weightedMultiplierCoefficients_summable phase grade second)
  have term (cell : ℤ) :
      singleModeCompleted (grade := grade) phase cell
          (weightedMultiplierCoefficients phase grade (first + second) cell) =
        singleModeCompleted phase cell
            (weightedMultiplierCoefficients phase grade first cell) +
          singleModeCompleted phase cell
            (weightedMultiplierCoefficients phase grade second cell) := by
    rw [show weightedMultiplierCoefficients phase grade (first + second) cell =
        weightedMultiplierCoefficients phase grade first cell +
          weightedMultiplierCoefficients phase grade second cell by
      unfold weightedMultiplierCoefficients
      change ((sequenceWeight phase grade cell : ℂ)⁻¹) •
          (first cell + second cell) = _
      rw [smul_add],
      singleModeCompleted_add_map]
  simp_rw [term]
  exact firstSummable.tsum_add secondSummable

theorem weightedCompletedMultiplier_smul (phase : PhaseParameters) (grade : ℕ)
    (scalar : ℂ) (sequence : WeightedSequence) :
    weightedCompletedMultiplier phase grade (scalar • sequence) =
      scalar • weightedCompletedMultiplier phase grade sequence := by
  unfold weightedCompletedMultiplier completedMultiplier
  have summable := completedModes_summable phase
    (weightedMultiplierCoefficients phase grade sequence)
    (weightedMultiplierCoefficients_summable phase grade sequence)
  have term (cell : ℤ) :
      singleModeCompleted (grade := grade) phase cell
          (weightedMultiplierCoefficients phase grade (scalar • sequence) cell) =
        scalar • singleModeCompleted phase cell
          (weightedMultiplierCoefficients phase grade sequence cell) := by
    rw [show weightedMultiplierCoefficients phase grade (scalar • sequence) cell =
        scalar • weightedMultiplierCoefficients phase grade sequence cell by
      unfold weightedMultiplierCoefficients
      change ((sequenceWeight phase grade cell : ℂ)⁻¹) •
          (scalar • sequence cell) = _
      rw [smul_smul, smul_smul]
      congr 1
      exact mul_comm _ _,
      singleModeCompleted_smul_map]
  simp_rw [term]
  exact summable.tsum_const_smul scalar

theorem weightedCompletedMultiplier_norm_le (phase : PhaseParameters) (grade : ℕ)
    (sequence : WeightedSequence) :
    ‖weightedCompletedMultiplier phase grade sequence‖ ≤
      multiplierConstant grade phase.gamma * ‖sequence‖ := by
  exact (completedMultiplier_norm_le phase
    (weightedMultiplierCoefficients phase grade sequence)
    (weightedMultiplierCoefficients_summable phase grade sequence)).trans_eq
      (by rw [weightedMultiplier_envelope])

/-- The bounded coefficient-to-operator map at one fixed original grade. -/
def weightedCompletedMultiplierMap (phase : PhaseParameters) (grade : ℕ) :
    WeightedSequence →L[ℂ]
      (AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade) :=
  LinearMap.mkContinuous
    { toFun := weightedCompletedMultiplier phase grade
      map_add' := weightedCompletedMultiplier_add phase grade
      map_smul' := weightedCompletedMultiplier_smul phase grade }
    (multiplierConstant grade phase.gamma)
    (weightedCompletedMultiplier_norm_le phase grade)

@[simp]
theorem weightedCompletedMultiplierMap_apply (phase : PhaseParameters) (grade : ℕ)
    (sequence : WeightedSequence) :
    weightedCompletedMultiplierMap phase grade sequence =
      weightedCompletedMultiplier phase grade sequence := rfl

/-- The actual completed deviation/inverse-deviation/derivative multiplier as
an operator-valued function of all four seed parameters. -/
def completedSeedDeviationFamily (phase : PhaseParameters) (grade : ℕ)
    (kind : Fin 3) (parameter : Seed.Parameters) :
    AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade :=
  weightedCompletedMultiplierMap phase grade
    (Seed.weightedSeedFamilies phase grade kind parameter)

theorem completedSeedDeviationFamily_contDiffOn (phase : PhaseParameters)
    (grade : ℕ) (kind : Fin 3) :
    ContDiffOn ℝ ∞ (completedSeedDeviationFamily phase grade kind)
      Seed.parameterDomain := by
  exact q23RealSmooth_linearFunction_comp
    (fun sequence => weightedCompletedMultiplierMap phase grade sequence)
    (fun x y => (weightedCompletedMultiplierMap phase grade).map_add x y)
    (fun r x => by
      apply ContinuousLinearMap.ext
      intro field
      exact congrArg
        (fun operator : AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade => operator field)
        (((weightedCompletedMultiplierMap phase grade).restrictScalars ℝ).map_smul r x))
    (weightedCompletedMultiplierMap phase grade).continuous
    (Seed.weightedSeedFamilies phase grade kind) Seed.parameterDomain
    (Seed.weightedSeedFamilies_contDiffOn phase grade kind)

theorem weightedMultiplierCoefficients_weightedSeed (phase : PhaseParameters)
    (grade : ℕ) (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    weightedMultiplierCoefficients phase grade
        (Seed.weightedSeedFamilies phase grade kind parameter) =
      Seed.actualCells kind parameter := by
  funext cell
  unfold weightedMultiplierCoefficients
  rw [Seed.weightedSeedFamilies_cells phase grade kind parameter inside cell,
    smul_smul, inv_mul_cancel₀, one_smul]
  exact Complex.ofReal_ne_zero.mpr (sequenceWeight_pos phase grade cell).ne'

theorem completedSeedDeviationFamily_eq_actual (phase : PhaseParameters)
    (grade : ℕ) (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    completedSeedDeviationFamily phase grade kind parameter =
      completedMultiplier phase (Seed.actualCells kind parameter) := by
  unfold completedSeedDeviationFamily weightedCompletedMultiplierMap
  change completedMultiplier phase
    (weightedMultiplierCoefficients phase grade
      (Seed.weightedSeedFamilies phase grade kind parameter)) = _
  rw [weightedMultiplierCoefficients_weightedSeed phase grade kind parameter inside]

theorem completedSeedDeviationFamily_core (phase : PhaseParameters)
    (grade : ℕ) (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore phase 2) :
    completedSeedDeviationFamily phase grade kind parameter
        (aGradeEta phase (GradeCore.ofCoreLinear field)) =
      aGradeEta phase (GradeCore.ofCoreLinear
        (seedDeviationCore phase parameter inside kind field)) := by
  rw [completedSeedDeviationFamily_eq_actual phase grade kind parameter inside]
  exact (smoothMultiplier_eta phase (Seed.actualCells kind parameter)
    (seedCells_all_summable phase parameter inside kind) field grade).symm

/-- The literal order-`j` operator-norm seed derivative at one completed
original grade. -/
def completedSeedParameterDerivative (phase : PhaseParameters) (grade order : ℕ)
    (kind : Fin 3) (parameter : Seed.Parameters)
    (directions : Fin order → Seed.Parameters) :
    AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade :=
  weightedCompletedMultiplierMap phase grade
    (iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
      parameter directions)

/-- Identification of the literal operator family with its actual Mathlib
iterated Fréchet derivative on the admissible seed domain. -/
theorem iteratedFDeriv_completedSeedDeviationFamily (phase : PhaseParameters)
    (grade order : ℕ) (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    (iteratedFDeriv ℝ order (completedSeedDeviationFamily phase grade kind)
        parameter) directions =
      completedSeedParameterDerivative phase grade order kind parameter directions := by
  have weightedSmooth :=
    (Seed.weightedSeedFamilies_contDiffOn phase grade kind).contDiffAt
      (Seed.parameterDomain_isOpen.mem_nhds inside)
  exact q23IteratedFDeriv_linearFunction_comp
    (fun sequence => weightedCompletedMultiplierMap phase grade sequence)
    (fun x y => (weightedCompletedMultiplierMap phase grade).map_add x y)
    (fun r x => by
      apply ContinuousLinearMap.ext
      intro field
      exact congrArg
        (fun operator : AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade => operator field)
        (((weightedCompletedMultiplierMap phase grade).restrictScalars ℝ).map_smul r x))
    (weightedCompletedMultiplierMap phase grade).continuous
    (Seed.weightedSeedFamilies phase grade kind) parameter weightedSmooth order directions

theorem weightedMultiplierCoefficients_seedDerivative (phase : PhaseParameters)
    (grade order : ℕ) (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    weightedMultiplierCoefficients phase grade
        (iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
          parameter directions) =
      seedCellParameterDerivative order kind parameter directions := by
  funext cell
  unfold weightedMultiplierCoefficients
  rw [weightedSeedFamilies_iteratedFDeriv_cell phase grade order kind parameter inside
    directions cell, smul_smul, inv_mul_cancel₀, one_smul]
  exact Complex.ofReal_ne_zero.mpr (sequenceWeight_pos phase grade cell).ne'

theorem completedSeedParameterDerivative_core (phase : PhaseParameters)
    (grade order : ℕ) (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 2) :
    completedSeedParameterDerivative phase grade order kind parameter directions
        (aGradeEta phase (GradeCore.ofCoreLinear field)) =
      aGradeEta phase (GradeCore.ofCoreLinear
        (seedParameterMultiplier phase order kind parameter inside directions field)) := by
  unfold completedSeedParameterDerivative weightedCompletedMultiplierMap
  change completedMultiplier phase
      (weightedMultiplierCoefficients phase grade
        (iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
          parameter directions))
      (aGradeEta phase (GradeCore.ofCoreLinear field)) = _
  rw [weightedMultiplierCoefficients_seedDerivative phase grade order kind parameter inside
    directions]
  exact (smoothMultiplier_eta phase
    (seedCellParameterDerivative order kind parameter directions)
    (fun q => seedCellParameterDerivative_summable phase q order kind parameter inside
      directions) field grade).symm

theorem completedSeedParameterDerivative_zero (phase : PhaseParameters)
    (grade : ℕ) (kind : Fin 3) (parameter : Seed.Parameters) :
    completedSeedParameterDerivative phase grade 0 kind parameter
        (fun position => position.elim0) =
      completedSeedDeviationFamily phase grade kind parameter := by
  rfl

theorem completedSeedParameterDerivative_norm_le (phase : PhaseParameters)
    (grade order : ℕ) (kind : Fin 3) (parameter : Seed.Parameters)
    (directions : Fin order → Seed.Parameters) :
    ‖completedSeedParameterDerivative phase grade order kind parameter directions‖ ≤
      multiplierConstant grade phase.gamma *
        ‖iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
          parameter directions‖ := by
  exact weightedCompletedMultiplier_norm_le phase grade _

/-- Uniform finite-seed bounds on a compact admissible patch, with the exact
product of the finite-dimensional direction norms. -/
theorem completedSeedParameterDerivative_compact_bound (phase : PhaseParameters)
    (grade order : ℕ) (compact : Set Seed.Parameters) (compactness : IsCompact compact)
    (insideCompact : compact ⊆ Seed.parameterDomain) :
    ∃ constant : ℝ, 0 ≤ constant ∧
      ∀ (kind : Fin 3) (parameter : Seed.Parameters), parameter ∈ compact →
        ∀ directions : Fin order → Seed.Parameters,
          ‖completedSeedParameterDerivative phase grade order kind parameter directions‖ ≤
            constant * ∏ position, ‖directions position‖ := by
  have each (kind : Fin 3) : ∃ constant : ℝ, ∀ parameter ∈ compact,
      ‖iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind) parameter‖ ≤
        constant := by
    apply compactness.exists_bound_of_continuousOn
    exact (ContinuousOn.continuousOn_iteratedFDeriv (k := order)
      (Seed.weightedSeedFamilies_contDiffOn phase grade kind)
      Seed.parameterDomain_isOpen
      (by exact_mod_cast (le_top : (order : ℕ∞) ≤ ⊤))).mono insideCompact
  choose constants bounds using each
  let seedConstant := ∑ kind : Fin 3, max 0 (constants kind)
  have seedNonnegative : 0 ≤ seedConstant :=
    Finset.sum_nonneg (fun _ _ => le_max_left _ _)
  have seedBound (kind : Fin 3) (parameter : Seed.Parameters)
      (inCompact : parameter ∈ compact) :
      ‖iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind) parameter‖ ≤
        seedConstant :=
    (bounds kind parameter inCompact).trans
      ((le_max_right 0 (constants kind)).trans
        (Finset.single_le_sum (f := fun index : Fin 3 => max 0 (constants index))
          (s := Finset.univ) (fun _ _ => le_max_left _ _)
          (Finset.mem_univ kind)))
  refine ⟨multiplierConstant grade phase.gamma * seedConstant,
    mul_nonneg (multiplierConstant_nonnegative grade phase.gamma phase.gamma_pos.le)
      seedNonnegative, ?_⟩
  intro kind parameter inCompact directions
  have directionBound :=
    (iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind) parameter).le_opNorm
      directions
  calc
    ‖completedSeedParameterDerivative phase grade order kind parameter directions‖
        ≤ multiplierConstant grade phase.gamma *
            ‖iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
              parameter directions‖ :=
          completedSeedParameterDerivative_norm_le phase grade order kind parameter directions
    _ ≤ multiplierConstant grade phase.gamma *
          (‖iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind) parameter‖ *
            ∏ position, ‖directions position‖) :=
        mul_le_mul_of_nonneg_left directionBound
          (multiplierConstant_nonnegative grade phase.gamma phase.gamma_pos.le)
    _ ≤ (multiplierConstant grade phase.gamma * seedConstant) *
          ∏ position, ‖directions position‖ := by
        have bound := seedBound kind parameter inCompact
        have directionNonnegative : 0 ≤ ∏ position, ‖directions position‖ :=
          Finset.prod_nonneg fun _ _ => norm_nonneg _
        calc
          multiplierConstant grade phase.gamma *
                (‖iteratedFDeriv ℝ order
                    (Seed.weightedSeedFamilies phase grade kind) parameter‖ *
                  ∏ position, ‖directions position‖)
              ≤ multiplierConstant grade phase.gamma *
                (seedConstant * ∏ position, ‖directions position‖) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right bound directionNonnegative)
              (multiplierConstant_nonnegative grade phase.gamma phase.gamma_pos.le)
          _ = _ := by ring

/-- Every order in the completed operator family genuinely differentiates in
operator norm to the next literal weighted-seed derivative. -/
theorem completedSeedParameterDerivative_genuine (phase : PhaseParameters)
    (grade order : ℕ) (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (oldDirections : Fin order → Seed.Parameters)
    (newDirection : Seed.Parameters) :
    Tendsto (fun t : ℝ =>
      ‖(((t : ℂ))⁻¹ •
          (completedSeedParameterDerivative phase grade order kind
              (parameter + t • newDirection) oldDirections -
            completedSeedParameterDerivative phase grade order kind
              parameter oldDirections)) -
        completedSeedParameterDerivative phase grade (order + 1) kind parameter
          (Fin.cons newDirection oldDirections)‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  have weightedLimitReal := hasFDerivAt_real_quotient _ _
    (weightedSeed_line_hasFDerivAt phase grade order kind parameter inside oldDirections
      newDirection)
  have weightedLimit : Tendsto (fun t : ℝ =>
      ‖(((t : ℂ))⁻¹ •
          (iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
              (parameter + t • newDirection) oldDirections -
            iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
              parameter oldDirections)) -
        iteratedFDeriv ℝ (order + 1) (Seed.weightedSeedFamilies phase grade kind)
          parameter (Fin.cons newDirection oldDirections)‖)
      (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    refine weightedLimitReal.congr' (Eventually.of_forall (fun t => ?_))
    rw [zero_smul, add_zero]
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
    change ‖((t⁻¹ : ℝ) : ℂ) • _ - _‖ = ‖((t : ℂ)⁻¹) • _ - _‖
    rw [Complex.ofReal_inv]
  refine squeeze_zero' ?_
    (g := fun t : ℝ => multiplierConstant grade phase.gamma *
      ‖(((t : ℂ))⁻¹ •
          (iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
              (parameter + t • newDirection) oldDirections -
            iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
              parameter oldDirections)) -
        iteratedFDeriv ℝ (order + 1) (Seed.weightedSeedFamilies phase grade kind)
          parameter (Fin.cons newDirection oldDirections)‖) ?_ ?_
  · apply Eventually.of_forall
    intro t
    positivity
  · apply Eventually.of_forall
    intro t
    simp only [completedSeedParameterDerivative]
    rw [← map_sub, ← map_smul, ← map_sub]
    exact weightedCompletedMultiplier_norm_le phase grade _
  · simpa only [mul_zero] using
      (tendsto_const_nhds.mul weightedLimit)

end Grad.NonlinearQuotientBounds
