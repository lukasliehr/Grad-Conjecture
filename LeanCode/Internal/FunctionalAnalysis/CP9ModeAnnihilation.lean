import CP8RowInverse

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators
open MeasureTheory

namespace Grad.Cor18

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Gauges Grad.Constraints.Multipliers Grad.BoundaryTrace Grad.BoundaryLift

/-! # Interior-mode annihilation of the collar correction

The lift of high-angular boundary data has no angular modes of absolute
frequency at most two; coordinate multiplication shifts modes by one and the
seed multipliers (cell convolutions with constant value maps) preserve
vanishing modes. Hence the collar correction `ι M (y • E_∂ b)` has no modes
`0, ±1`, so N3's tangential projection (modes `±1`) and the toroidal mean
(mode `0`) of both written gauge integrands vanish exactly: both gauge
corrections annihilate the collar correction. -/

variable {parameters : PhaseParameters}

/-- Cellwise vanishing of every angular mode in a set. -/
def ModesVanish {dimension : ℕ} (modes : Set ℤ) (field : ACore parameters dimension) : Prop :=
  ∀ mode ∈ modes, angularCore parameters mode field = 0

theorem modesVanish_cell {dimension : ℕ} {modes : Set ℤ} {field : ACore parameters dimension}
    (vanish : ModesVanish modes field) {mode : ℤ} (mem : mode ∈ modes) (cell : ℤ) :
    angularClosedJet mode (field.1 cell) = 0 := by
  have := congrArg (fun other : ACore parameters dimension => other.1 cell) (vanish mode mem)
  simpa only [angularCore_apply, Submodule.coe_zero, Pi.zero_apply] using this

theorem modesVanish_of_cell {dimension : ℕ} {modes : Set ℤ} {field : ACore parameters dimension}
    (vanish : ∀ mode ∈ modes, ∀ cell : ℤ, angularClosedJet mode (field.1 cell) = 0) :
    ModesVanish modes field := by
  intro mode mem
  apply Subtype.ext
  funext cell
  rw [angularCore_apply, vanish mode mem cell]
  rfl

theorem modesVanish_mono {dimension : ℕ} {modes modes' : Set ℤ} (sub : modes' ⊆ modes)
    {field : ACore parameters dimension} (vanish : ModesVanish modes field) :
    ModesVanish modes' field :=
  fun mode mem => vanish mode (sub mem)

theorem modesVanish_add {dimension : ℕ} {modes : Set ℤ} {first second : ACore parameters dimension}
    (one : ModesVanish modes first) (two : ModesVanish modes second) :
    ModesVanish modes (first + second) := by
  intro mode mem
  rw [map_add, one mode mem, two mode mem, add_zero]

theorem modesVanish_smul {dimension : ℕ} {modes : Set ℤ} (scalar : ℂ)
    {field : ACore parameters dimension} (vanish : ModesVanish modes field) :
    ModesVanish modes (scalar • field) := by
  intro mode mem
  rw [map_smul, vanish mode mem, smul_zero]

/-- Zero jets have zero value. -/
theorem zero_jet_value {dimension : ℕ} (point : ClosedDisk) :
    (0 : ClosedJet dimension).value point = 0 := by
  rw [closedJet_value_zero]
  rfl

/-- Fixed value maps of the zero jet vanish. -/
theorem valueMapJet_zero_jet {s t : ℕ} (mapping : ComplexEuclidean s →L[ℂ] ComplexEuclidean t) :
    valueMapJet mapping (0 : ClosedJet s) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [valueMapJet_value, zero_jet_value, map_zero, zero_jet_value]

theorem modesVanish_valueMapCore {s t : ℕ} (mapping : ComplexEuclidean s →L[ℂ] ComplexEuclidean t)
    {modes : Set ℤ} {field : ACore parameters s} (vanish : ModesVanish modes field) :
    ModesVanish modes (valueMapCore mapping parameters field) := by
  apply modesVanish_of_cell
  intro mode mem cell
  rw [valueMapCore_apply, angularClosedJet_valueMap, modesVanish_cell vanish mem cell,
    valueMapJet_zero_jet]

/-! ### Coordinate multiplication shifts modes by one -/

theorem coordinateMultiplyJet_zero_jet {dimension : ℕ} (sign : ℝ) :
    coordinateMultiplyJet sign (0 : ClosedJet dimension) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [coordinateMultiplyJet_value, zero_jet_value, smul_zero]

theorem realCoordinateJet_zero_eq {dimension : ℕ} (field : ClosedJet dimension) :
    realCoordinateJet 0 field =
      (1 / 2 : ℂ) • (coordinateMultiplyJet 1 field + coordinateMultiplyJet (-1) field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have scalar : ((point.val 0 : ℝ) : ℂ) = (1 / 2 : ℂ) *
      (signedComplexCoordinate 1 point.val + signedComplexCoordinate (-1) point.val) := by
    unfold signedComplexCoordinate
    push_cast
    ring
  rw [realCoordinateJet_value, closedJet_value_smul, ContinuousMap.smul_apply, closedJet_value_add,
    ContinuousMap.add_apply, coordinateMultiplyJet_value, coordinateMultiplyJet_value,
    ← add_smul, smul_smul, ← scalar]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _

theorem realCoordinateJet_one_eq {dimension : ℕ} (field : ClosedJet dimension) :
    realCoordinateJet 1 field =
      (-(Complex.I / 2)) • coordinateMultiplyJet 1 field +
        (Complex.I / 2) • coordinateMultiplyJet (-1) field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  have scalar : ((point.val 1 : ℝ) : ℂ) = (-(Complex.I / 2)) * signedComplexCoordinate 1 point.val +
      (Complex.I / 2) * signedComplexCoordinate (-1) point.val := by
    unfold signedComplexCoordinate
    push_cast
    linear_combination ((point.val 1 : ℝ) : ℂ) * Complex.I_sq
  rw [realCoordinateJet_value, closedJet_value_add, ContinuousMap.add_apply, closedJet_value_smul,
    closedJet_value_smul, ContinuousMap.smul_apply, ContinuousMap.smul_apply,
    coordinateMultiplyJet_value, coordinateMultiplyJet_value, smul_smul, smul_smul, ← add_smul,
    ← scalar]
  exact RCLike.real_smul_eq_coe_smul (K := ℂ) _ _

theorem modesVanish_coordinateCore (coordinate : Fin 2) {dimension : ℕ} {modes : Set ℤ}
    {field : ACore parameters dimension} (vanish : ModesVanish modes field) :
    ModesVanish {mode | mode - 1 ∈ modes ∧ mode + 1 ∈ modes}
      (coordinateCore parameters coordinate field) := by
  apply modesVanish_of_cell
  intro mode mem cell
  rw [coordinateCore_apply]
  fin_cases coordinate
  · show angularClosedJet mode (realCoordinateJet 0 (field.1 cell)) = 0
    rw [realCoordinateJet_zero_eq, angularClosedJet_smul, angularClosedJet_add, angularClosedJet_z,
      angularClosedJet_zbar, modesVanish_cell vanish mem.1 cell, modesVanish_cell vanish mem.2 cell,
      coordinateMultiplyJet_zero_jet, coordinateMultiplyJet_zero_jet, add_zero, smul_zero]
  · show angularClosedJet mode (realCoordinateJet 1 (field.1 cell)) = 0
    rw [realCoordinateJet_one_eq, angularClosedJet_add, angularClosedJet_smul, angularClosedJet_smul,
      angularClosedJet_z, angularClosedJet_zbar, modesVanish_cell vanish mem.1 cell,
      modesVanish_cell vanish mem.2 cell, coordinateMultiplyJet_zero_jet,
      coordinateMultiplyJet_zero_jet, smul_zero, smul_zero, add_zero]

/-! ### Smooth multipliers preserve vanishing modes -/

/-- The sup norms of the cells of a core field are summable. -/
theorem cell_sup_norm_summable {dimension : ℕ} (field : ACore parameters dimension) :
    Summable (fun cell : ℤ => ‖(field.1 cell).value‖) := by
  simpa only [pow_zero, one_mul, closedDerivative_zero_order] using
    originalClosedDerivative_frequency_summable parameters field emptyCartesianWord 0

/-- Multiplier coefficients are norm-summable (the grade-zero envelope). -/
theorem coefficients_norm_summable {s t : ℕ}
    (coefficients : ℤ → ComplexEuclidean s →L[ℂ] ComplexEuclidean t)
    (summable : ∀ grade, Summable (envelopeTerm parameters grade coefficients)) :
    Summable (fun cell : ℤ => ‖coefficients cell‖) := by
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun cell => ?_) (summable 0)
  unfold envelopeTerm
  rw [pow_zero, mul_one]
  exact le_mul_of_one_le_left (norm_nonneg _)
    (Real.one_le_exp (mul_nonneg parameters.sigma0_pos.le (cellFrequency_pos cell).le))

theorem modesVanish_smoothMultiplier {s t : ℕ}
    (coefficients : ℤ → ComplexEuclidean s →L[ℂ] ComplexEuclidean t)
    (summable : ∀ grade, Summable (envelopeTerm parameters grade coefficients))
    {modes : Set ℤ} {field : ACore parameters s} (vanish : ModesVanish modes field) :
    ModesVanish modes (smoothMultiplier parameters coefficients summable field) := by
  apply modesVanish_of_cell
  intro mode mem cell
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [angularClosedJet_value, zero_jet_value]
  -- the pulled integrand of every cell shift
  set integrand : ℤ → ℝ → ComplexEuclidean t := fun shift angle =>
    coefficients shift (angularCharacter mode angle •
      (field.1 (cell - shift)).value (Grad.GaugeCoefficients.Radial.rotatedPoint angle point))
    with integrand_def
  have termsZero : ∀ shift : ℤ,
      ∫ angle in (0 : ℝ)..2 * Real.pi, integrand shift angle = 0 := by
    intro shift
    simp only [integrand_def]
    rw [(coefficients shift).intervalIntegral_comp_comm
      ((angularValueIntegrand_continuous mode _ point).intervalIntegrable _ _)]
    have vanishValue := congrArg (fun jet : ClosedJet s => jet.value point)
      (modesVanish_cell vanish mem (cell - shift))
    simp only [angularClosedJet_value, zero_jet_value] at vanishValue
    have twoPi : ((2 * Real.pi)⁻¹ : ℝ) ≠ 0 := inv_ne_zero (by positivity)
    rw [(smul_eq_zero.mp vanishValue).resolve_left twoPi, map_zero]
  obtain ⟨bound, boundLaw⟩ := (coefficients_norm_summable coefficients
    summable).tendsto_cofinite_zero.bddAbove_range_of_cofinite
  have coefficientBound : ∀ shift : ℤ, ‖coefficients shift‖ ≤ bound :=
    fun shift => boundLaw (Set.mem_range_self shift)
  have shifted : Summable (fun shift : ℤ => ‖(field.1 (cell - shift)).value‖) :=
    (cell_sup_norm_summable field).comp_injective sub_right_injective
  have majorantSummable : Summable (fun shift : ℤ =>
      ‖coefficients shift‖ * ‖(field.1 (cell - shift)).value‖) :=
    Summable.of_nonneg_of_le (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun shift => mul_le_mul_of_nonneg_right (coefficientBound shift) (norm_nonneg _))
      (shifted.mul_left bound)
  have sumLaw : HasSum (fun shift : ℤ => ∫ angle in (0 : ℝ)..2 * Real.pi, integrand shift angle)
      (∫ angle in (0 : ℝ)..2 * Real.pi, angularCharacter mode angle •
        ((smoothMultiplier parameters coefficients summable field).1 cell).value
          (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun shift _ => ‖coefficients shift‖ * ‖(field.1 (cell - shift)).value‖)
    · intro shift
      exact ((coefficients shift).continuous.comp
        (angularValueIntegrand_continuous mode _ point)).aestronglyMeasurable
    · intro shift
      filter_upwards with angle _
      simp only [integrand_def]
      calc ‖coefficients shift (angularCharacter mode angle •
            (field.1 (cell - shift)).value (Grad.GaugeCoefficients.Radial.rotatedPoint angle point))‖
          ≤ ‖coefficients shift‖ * ‖angularCharacter mode angle •
              (field.1 (cell - shift)).value
                (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)‖ :=
            (coefficients shift).le_opNorm _
        _ = ‖coefficients shift‖ * ‖(field.1 (cell - shift)).value
              (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)‖ := by
            rw [norm_smul, angularCharacter_norm, one_mul]
        _ ≤ ‖coefficients shift‖ * ‖(field.1 (cell - shift)).value‖ :=
            mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm _ _) (norm_nonneg _)
    · filter_upwards with angle _
      exact majorantSummable
    · exact intervalIntegrable_const
    · filter_upwards with angle _
      have pointwise := (smoothMultiplier_value_hasSum parameters coefficients summable field cell
        (Grad.GaugeCoefficients.Radial.rotatedPoint angle point)).const_smul
        (angularCharacter mode angle)
      simp only [integrand_def, map_smul]
      exact pointwise
  have integralZero := sumLaw.unique (by simpa only [termsZero] using hasSum_zero)
  rw [integralZero, smul_zero]

/-! ### The tangential projection kills modes `±1`-free fields -/

theorem reflectedVectorJet_zero_jet : reflectedVectorJet (0 : ClosedJet 2) = 0 :=
  reflectedVectorLinear.map_zero

theorem tangentialCore_eq_zero {field : ACore parameters 2}
    (vanish : ModesVanish {1, -1} field) : tangentialCore parameters field = 0 := by
  apply Subtype.ext
  funext cell
  rw [tangentialCore_apply, tangentialJet_eq, equivariantAverageJet_eq,
    modesVanish_cell vanish (by simp) cell, modesVanish_cell vanish (by simp) cell,
    valueMapJet_zero_jet, valueMapJet_zero_jet, add_zero, reflectedVectorJet_zero_jet, sub_zero,
    smul_zero]
  rfl

/-! ### The collar correction has no modes `0, ±1` -/

theorem boundaryLift_modesVanish (values : BoundaryCore parameters 1)
    (high : HighBoundarySupport parameters values) :
    ModesVanish {mode | |mode| ≤ 2} (boundaryLift parameters values) :=
  modesVanish_of_cell fun mode mem cell => boundaryLift_high_support parameters values high mode mem cell

theorem coordinateVector_modesVanish (values : BoundaryCore parameters 1)
    (high : HighBoundarySupport parameters values) :
    ModesVanish {mode | |mode| ≤ 1} (coordinateVector parameters (boundaryLift parameters values)) := by
  have lift := boundaryLift_modesVanish values high
  have shiftSub : {mode : ℤ | |mode| ≤ 1} ⊆
      {mode | mode - 1 ∈ {mode : ℤ | |mode| ≤ 2} ∧ mode + 1 ∈ {mode : ℤ | |mode| ≤ 2}} := by
    intro mode mem
    have bound : |mode| ≤ 1 := mem
    rw [abs_le] at bound
    exact ⟨show |mode - 1| ≤ 2 from abs_le.mpr ⟨by omega, by omega⟩,
      show |mode + 1| ≤ 2 from abs_le.mpr ⟨by omega, by omega⟩⟩
  unfold coordinateVector
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  exact modesVanish_add
    (modesVanish_valueMapCore _ (modesVanish_mono shiftSub (modesVanish_coordinateCore 0 lift)))
    (modesVanish_valueMapCore _ (modesVanish_mono shiftSub (modesVanish_coordinateCore 1 lift)))

variable (parameters) (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)

theorem collarCorrection_planar_modesVanish (values : BoundaryCore parameters 1)
    (high : HighBoundarySupport parameters values) :
    ModesVanish {mode | |mode| ≤ 1}
      (planarPartCore parameters (collarCorrection parameters parameter inside values)) := by
  unfold collarCorrection
  simp only [LinearMap.comp_apply]
  rw [planarPartCore_planarInclusionCore, seedMatrixCore_eq_full]
  exact modesVanish_smoothMultiplier _ _ (coordinateVector_modesVanish values high)

/-- The poloidal gauge correction annihilates the collar correction. -/
theorem poloidalCorrection_collarCorrection (values : BoundaryCore parameters 1)
    (high : HighBoundarySupport parameters values) :
    poloidalCorrection parameters parameter inside
      (collarCorrection parameters parameter inside values) = 0 := by
  rw [poloidalCorrection_apply]
  have transposed : ModesVanish {mode | |mode| ≤ 1} (seedTransposeCore parameters parameter inside
      (planarPartCore parameters (collarCorrection parameters parameter inside values))) := by
    unfold seedTransposeCore
    exact modesVanish_smoothMultiplier _ _
      (collarCorrection_planar_modesVanish parameters parameter inside values high)
  have pair : ({1, -1} : Set ℤ) ⊆ {mode | |mode| ≤ 1} := by
    intro mode mem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at mem
    rcases mem with rfl | rfl
    · show |(1 : ℤ)| ≤ 1
      norm_num
    · show |(-1 : ℤ)| ≤ 1
      norm_num
  rw [tangentialCore_eq_zero (modesVanish_mono pair transposed), map_zero, map_zero]

/-- The toroidal gauge correction annihilates the collar correction. -/
theorem toroidalCorrection_collarCorrection (values : BoundaryCore parameters 1)
    (high : HighBoundarySupport parameters values) :
    toroidalCorrection parameters parameter inside
      (collarCorrection parameters parameter inside values) = 0 := by
  rw [toroidalCorrection_apply]
  have planar := collarCorrection_planar_modesVanish parameters parameter inside values high
  have zeroSub : ({0} : Set ℤ) ⊆
      {mode | mode - 1 ∈ {mode : ℤ | |mode| ≤ 1} ∧ mode + 1 ∈ {mode : ℤ | |mode| ≤ 1}} := by
    intro mode mem
    simp only [Set.mem_singleton_iff] at mem
    subst mem
    exact ⟨show |(0 : ℤ) - 1| ≤ 1 by norm_num, show |(0 : ℤ) + 1| ≤ 1 by norm_num⟩
  have dot : ModesVanish {0} (derivativeDotCore parameters parameter inside
      (planarPartCore parameters (collarCorrection parameters parameter inside values))) := by
    unfold derivativeDotCore
    simp only [LinearMap.add_apply, LinearMap.comp_apply]
    exact modesVanish_add
      (modesVanish_mono zeroSub (modesVanish_coordinateCore 0
        (modesVanish_smoothMultiplier _ _ planar)))
      (modesVanish_mono zeroSub (modesVanish_coordinateCore 1
        (modesVanish_smoothMultiplier _ _ planar)))
  have toroidalZero : toroidalPartCore parameters
      (collarCorrection parameters parameter inside values) = 0 := by
    unfold collarCorrection
    simp only [LinearMap.comp_apply]
    exact toroidalPartCore_planarInclusionCore parameters _
  rw [toroidalZero, zero_add, map_smul, dot 0 (Set.mem_singleton 0), smul_zero, map_zero]

/-- Both gauge corrections vanish on the outer correction of a field in the
joint gauge kernel. -/
theorem poloidalCorrection_outerCorrection (state : ACore parameters 3)
    (poloidalZero : poloidalCorrection parameters parameter inside state = 0) :
    poloidalCorrection parameters parameter inside
      (outerCorrection parameters parameter inside state) = 0 := by
  rw [outerCorrection_apply, map_sub, poloidalZero,
    poloidalCorrection_collarCorrection parameters parameter inside _
      (physicalRow_highSupport parameters parameter inside state), sub_zero]

theorem toroidalCorrection_outerCorrection (state : ACore parameters 3)
    (toroidalZero : toroidalCorrection parameters parameter inside state = 0) :
    toroidalCorrection parameters parameter inside
      (outerCorrection parameters parameter inside state) = 0 := by
  rw [outerCorrection_apply, map_sub, toroidalZero,
    toroidalCorrection_collarCorrection parameters parameter inside _
      (physicalRow_highSupport parameters parameter inside state), sub_zero]

end Grad.Cor18
