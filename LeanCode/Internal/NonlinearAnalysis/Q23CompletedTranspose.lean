import Q23CompletedMultiplier

noncomputable section

set_option maxHeartbeats 2400000

open Set Filter
open scoped BigOperators ContDiff ENNReal Topology

namespace Grad.NonlinearQuotientBounds

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers Grad.Constraints.Gauges Grad.Constraints.Seed
open Grad.GaugeCoefficients.Algebra

def weightedTransposeCoefficients (phase : PhaseParameters) (grade : ℕ)
    (sequence : WeightedSequence) (cell : ℤ) : OperatorValue 2 2 :=
  transposeOperator (weightedMultiplierCoefficients phase grade sequence cell)

theorem weightedTransposeCoefficients_summable (phase : PhaseParameters)
    (grade : ℕ) (sequence : WeightedSequence) :
    Summable (envelopeTerm phase grade
      (weightedTransposeCoefficients phase grade sequence)) :=
  transpose_envelope_summable phase grade _
    (weightedMultiplierCoefficients_summable phase grade sequence)

theorem weightedTranspose_envelope_le (phase : PhaseParameters) (grade : ℕ)
    (sequence : WeightedSequence) :
    envelope phase grade (weightedTransposeCoefficients phase grade sequence) ≤
      4 * ‖sequence‖ := by
  rw [envelope, Seed.weightedSequence_norm, ← tsum_mul_left]
  apply Summable.tsum_le_tsum
  · intro cell
    unfold weightedTransposeCoefficients envelopeTerm
    calc
      Real.exp (phase.sigma0 * cellFrequency cell) * cellPolynomialWeight cell ^ grade *
          ‖transposeOperator (weightedMultiplierCoefficients phase grade sequence cell)‖
          ≤ Real.exp (phase.sigma0 * cellFrequency cell) *
              cellPolynomialWeight cell ^ grade *
              (4 * ‖weightedMultiplierCoefficients phase grade sequence cell‖) :=
        mul_le_mul_of_nonneg_left (transposeOperator_norm_le _)
          (mul_nonneg (Real.exp_pos _).le
            (pow_nonneg (zero_lt_one.trans_le (cellPolynomialWeight_one_le cell)).le _))
      _ = 4 * ‖sequence cell‖ := by
        rw [← weightedMultiplier_envelopeTerm phase grade sequence cell]
        unfold envelopeTerm
        ring
  · exact weightedTransposeCoefficients_summable phase grade sequence
  · have normSummable : Summable (fun cell : ℤ => ‖sequence cell‖) := by
      simpa only [ENNReal.toReal_one, Real.rpow_one] using
        (lp.memℓp sequence).summable (by norm_num : 0 < (1 : ℝ≥0∞).toReal)
    exact normSummable.mul_left 4

def weightedCompletedTranspose (phase : PhaseParameters) (grade : ℕ)
    (sequence : WeightedSequence) :
    AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade :=
  completedMultiplier phase (weightedTransposeCoefficients phase grade sequence)

theorem weightedCompletedTranspose_add (phase : PhaseParameters) (grade : ℕ)
    (first second : WeightedSequence) :
    weightedCompletedTranspose phase grade (first + second) =
      weightedCompletedTranspose phase grade first +
        weightedCompletedTranspose phase grade second := by
  unfold weightedCompletedTranspose completedMultiplier
  have firstSummable := completedModes_summable phase
    (weightedTransposeCoefficients phase grade first)
    (weightedTransposeCoefficients_summable phase grade first)
  have secondSummable := completedModes_summable phase
    (weightedTransposeCoefficients phase grade second)
    (weightedTransposeCoefficients_summable phase grade second)
  have term (cell : ℤ) :
      singleModeCompleted (grade := grade) phase cell
          (weightedTransposeCoefficients phase grade (first + second) cell) =
        singleModeCompleted phase cell
            (weightedTransposeCoefficients phase grade first cell) +
          singleModeCompleted phase cell
            (weightedTransposeCoefficients phase grade second cell) := by
    rw [show weightedTransposeCoefficients phase grade (first + second) cell =
        weightedTransposeCoefficients phase grade first cell +
          weightedTransposeCoefficients phase grade second cell by
      unfold weightedTransposeCoefficients weightedMultiplierCoefficients transposeOperator
      change transposeContinuous
          (((sequenceWeight phase grade cell : ℂ)⁻¹) • (first cell + second cell)) =
        transposeContinuous (((sequenceWeight phase grade cell : ℂ)⁻¹) • first cell) +
          transposeContinuous (((sequenceWeight phase grade cell : ℂ)⁻¹) • second cell)
      rw [smul_add, map_add],
      singleModeCompleted_add_map]
  simp_rw [term]
  exact firstSummable.tsum_add secondSummable

theorem weightedCompletedTranspose_smul (phase : PhaseParameters) (grade : ℕ)
    (scalar : ℂ) (sequence : WeightedSequence) :
    weightedCompletedTranspose phase grade (scalar • sequence) =
      scalar • weightedCompletedTranspose phase grade sequence := by
  unfold weightedCompletedTranspose completedMultiplier
  have summable := completedModes_summable phase
    (weightedTransposeCoefficients phase grade sequence)
    (weightedTransposeCoefficients_summable phase grade sequence)
  have term (cell : ℤ) :
      singleModeCompleted (grade := grade) phase cell
          (weightedTransposeCoefficients phase grade (scalar • sequence) cell) =
        scalar • singleModeCompleted phase cell
          (weightedTransposeCoefficients phase grade sequence cell) := by
    rw [show weightedTransposeCoefficients phase grade (scalar • sequence) cell =
        scalar • weightedTransposeCoefficients phase grade sequence cell by
      unfold weightedTransposeCoefficients weightedMultiplierCoefficients transposeOperator
      change transposeContinuous
          (((sequenceWeight phase grade cell : ℂ)⁻¹) • (scalar • sequence cell)) =
        scalar • transposeContinuous
          (((sequenceWeight phase grade cell : ℂ)⁻¹) • sequence cell)
      calc
        transposeContinuous (((sequenceWeight phase grade cell : ℂ)⁻¹) •
            (scalar • sequence cell)) =
            (((sequenceWeight phase grade cell : ℂ)⁻¹) * scalar) •
              transposeContinuous (sequence cell) := by rw [smul_smul, map_smul]
        _ = (scalar * ((sequenceWeight phase grade cell : ℂ)⁻¹)) •
              transposeContinuous (sequence cell) := by rw [mul_comm]
        _ = scalar • transposeContinuous
              (((sequenceWeight phase grade cell : ℂ)⁻¹) • sequence cell) := by
            rw [map_smul, smul_smul],
      singleModeCompleted_smul_map]
  simp_rw [term]
  exact summable.tsum_const_smul scalar

theorem weightedCompletedTranspose_norm_le (phase : PhaseParameters) (grade : ℕ)
    (sequence : WeightedSequence) :
    ‖weightedCompletedTranspose phase grade sequence‖ ≤
      (4 * multiplierConstant grade phase.gamma) * ‖sequence‖ := by
  calc
    ‖weightedCompletedTranspose phase grade sequence‖
        ≤ multiplierConstant grade phase.gamma *
            envelope phase grade (weightedTransposeCoefficients phase grade sequence) :=
      completedMultiplier_norm_le phase _
        (weightedTransposeCoefficients_summable phase grade sequence)
    _ ≤ multiplierConstant grade phase.gamma * (4 * ‖sequence‖) :=
      mul_le_mul_of_nonneg_left (weightedTranspose_envelope_le phase grade sequence)
        (multiplierConstant_nonnegative grade phase.gamma phase.gamma_pos.le)
    _ = _ := by ring

def weightedCompletedTransposeMap (phase : PhaseParameters) (grade : ℕ) :
    WeightedSequence →L[ℂ]
      (AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade) :=
  LinearMap.mkContinuous
    { toFun := weightedCompletedTranspose phase grade
      map_add' := weightedCompletedTranspose_add phase grade
      map_smul' := weightedCompletedTranspose_smul phase grade }
    (4 * multiplierConstant grade phase.gamma)
    (weightedCompletedTranspose_norm_le phase grade)

def completedSeedTransposeDeviationFamily (phase : PhaseParameters) (grade : ℕ)
    (kind : Fin 3) (parameter : Seed.Parameters) :
    AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade :=
  weightedCompletedTransposeMap phase grade
    (Seed.weightedSeedFamilies phase grade kind parameter)

theorem completedSeedTransposeDeviationFamily_contDiffOn (phase : PhaseParameters)
    (grade : ℕ) (kind : Fin 3) :
    ContDiffOn ℝ ∞ (completedSeedTransposeDeviationFamily phase grade kind)
      Seed.parameterDomain := by
  exact q23RealSmooth_linearFunction_comp
    (fun sequence => weightedCompletedTransposeMap phase grade sequence)
    (fun x y => (weightedCompletedTransposeMap phase grade).map_add x y)
    (fun r x => by
      apply ContinuousLinearMap.ext
      intro field
      exact congrArg
        (fun operator : AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade => operator field)
        (((weightedCompletedTransposeMap phase grade).restrictScalars ℝ).map_smul r x))
    (weightedCompletedTransposeMap phase grade).continuous
    (Seed.weightedSeedFamilies phase grade kind) Seed.parameterDomain
    (Seed.weightedSeedFamilies_contDiffOn phase grade kind)

def completedSeedTransposeParameterDerivative (phase : PhaseParameters)
    (grade order : ℕ) (kind : Fin 3) (parameter : Seed.Parameters)
    (directions : Fin order → Seed.Parameters) :
    AGrade phase 2 grade →L[ℂ] AGrade phase 2 grade :=
  weightedCompletedTransposeMap phase grade
    (iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
      parameter directions)

def seedTransposeParameterMultiplier (phase : PhaseParameters) (order : ℕ)
    (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    ACore phase 2 →ₗ[ℂ] ACore phase 2 :=
  smoothMultiplier phase
    (fun cell => transposeOperator
      (seedCellParameterDerivative order kind parameter directions cell))
    (fun grade => transpose_envelope_summable phase grade _
      (seedCellParameterDerivative_summable phase grade order kind parameter inside
        directions))

theorem weightedTransposeCoefficients_seedDerivative (phase : PhaseParameters)
    (grade order : ℕ) (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) :
    weightedTransposeCoefficients phase grade
        (iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
          parameter directions) =
      fun cell => transposeOperator
        (seedCellParameterDerivative order kind parameter directions cell) := by
  funext cell
  unfold weightedTransposeCoefficients
  rw [weightedMultiplierCoefficients_seedDerivative phase grade order kind parameter inside
    directions]

theorem completedSeedTransposeParameterDerivative_core (phase : PhaseParameters)
    (grade order : ℕ) (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (directions : Fin order → Seed.Parameters) (field : ACore phase 2) :
    completedSeedTransposeParameterDerivative phase grade order kind parameter directions
        (aGradeEta phase (GradeCore.ofCoreLinear field)) =
      aGradeEta phase (GradeCore.ofCoreLinear
        (seedTransposeParameterMultiplier phase order kind parameter inside directions field)) := by
  unfold completedSeedTransposeParameterDerivative weightedCompletedTransposeMap
  change completedMultiplier phase
      (weightedTransposeCoefficients phase grade
        (iteratedFDeriv ℝ order (Seed.weightedSeedFamilies phase grade kind)
          parameter directions))
      (aGradeEta phase (GradeCore.ofCoreLinear field)) = _
  rw [weightedTransposeCoefficients_seedDerivative phase grade order kind parameter inside
    directions]
  exact (smoothMultiplier_eta phase _ _ field grade).symm

theorem completedSeedTransposeDeviationFamily_core (phase : PhaseParameters)
    (grade : ℕ) (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore phase 2) :
    completedSeedTransposeDeviationFamily phase grade kind parameter
        (aGradeEta phase (GradeCore.ofCoreLinear field)) =
      aGradeEta phase (GradeCore.ofCoreLinear
        (seedTransposeParameterMultiplier phase 0 kind parameter inside
          (fun position => position.elim0) field)) := by
  change completedSeedTransposeParameterDerivative phase grade 0 kind parameter
      (fun position => position.elim0) (aGradeEta phase (GradeCore.ofCoreLinear field)) = _
  exact completedSeedTransposeParameterDerivative_core phase grade 0 kind parameter inside
    (fun position => position.elim0) field

theorem seedTransposeParameterMultiplier_zero (phase : PhaseParameters)
    (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore phase 2) :
    seedTransposeParameterMultiplier phase 0 kind parameter inside
        (fun position => position.elim0) field =
      smoothMultiplier phase
        (fun cell => transposeOperator (Seed.actualCells kind parameter cell))
        (fun grade => transpose_envelope_summable phase grade _
          (seedCells_all_summable phase parameter inside kind grade)) field := by
  rfl

theorem seedTransposeCore_eq_identity_add_deviation (phase : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (field : ACore phase 2) :
    seedTransposeCore phase parameter inside field =
      field + seedTransposeParameterMultiplier phase 0 0 parameter inside
        (fun position => position.elim0) field := by
  change smoothMultiplier phase
      (fun index =>
        (if index = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0) +
          transposeOperator (Seed.actualCells 0 parameter index)) _ field = _
  rw [smoothMultiplier_add_coefficients phase
    (fun index => if index = 0 then ContinuousLinearMap.id ℂ (ComplexEuclidean 2) else 0)
    (fun index => transposeOperator (Seed.actualCells 0 parameter index))
    (fun grade => deltaIdentity_envelope_summable phase grade)
    (fun grade => transpose_envelope_summable phase grade _
      (seedCells_all_summable phase parameter inside 0 grade)) field,
    smoothMultiplier_delta_identity]
  rfl

theorem completedSeedTransposeParameterDerivative_genuine (phase : PhaseParameters)
    (grade order : ℕ) (kind : Fin 3) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain)
    (oldDirections : Fin order → Seed.Parameters)
    (newDirection : Seed.Parameters) :
    Tendsto (fun t : ℝ =>
      ‖(((t : ℂ))⁻¹ •
          (completedSeedTransposeParameterDerivative phase grade order
              kind (parameter + t • newDirection) oldDirections -
            completedSeedTransposeParameterDerivative phase grade order
              kind parameter oldDirections)) -
        completedSeedTransposeParameterDerivative phase grade (order + 1) kind parameter
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
    rw [zero_smul, add_zero, RCLike.real_smul_eq_coe_smul (K := ℂ)]
    change ‖((t⁻¹ : ℝ) : ℂ) • _ - _‖ = ‖((t : ℂ)⁻¹) • _ - _‖
    rw [Complex.ofReal_inv]
  refine squeeze_zero' ?_
    (g := fun t : ℝ => (4 * multiplierConstant grade phase.gamma) *
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
    simp only [completedSeedTransposeParameterDerivative]
    rw [← map_sub, ← map_smul, ← map_sub]
    exact weightedCompletedTranspose_norm_le phase grade _
  · simpa only [mul_zero] using tendsto_const_nhds.mul weightedLimit

end Grad.NonlinearQuotientBounds
