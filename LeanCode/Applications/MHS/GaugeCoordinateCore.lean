import GaugeCoordinateRow

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Multipliers

theorem coordinate_core_membership {dimension : ℕ} (parameters : PhaseParameters)
    (coordinate : Fin 2) (field : ACore parameters dimension) :
    (fun cell => realCoordinateJet coordinate (field.1 cell)) ∈
      originalCoreSubmodule parameters dimension := by
  intro grade
  rw [memlp_iff_summable_sq]
  have original := (memlp_iff_summable_sq _).mp (field.property grade)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _)
    (fun cell => ?_) (original.mul_left (coordinateRowConstant grade ^ 2))
  have bound := pow_le_pow_left₀ (norm_nonneg _)
    (realCoordinateJet_row_le (grade := grade) parameters cell coordinate (field.1 cell)) 2
  simpa only [mul_pow, rawCartesianGradeCoordinates] using bound

/-- Actual multiplication by one literal real coordinate on the original
all-grade coefficient space. -/
def coordinateCore {dimension : ℕ} (parameters : PhaseParameters) (coordinate : Fin 2) :
    ACore parameters dimension →ₗ[ℂ] ACore parameters dimension where
  toFun field := ⟨fun cell => realCoordinateJet coordinate (field.1 cell),
    coordinate_core_membership parameters coordinate field⟩
  map_add' first second := by
    apply Subtype.ext
    funext cell
    exact realCoordinateJet_add coordinate (first.1 cell) (second.1 cell)
  map_smul' scalar field := by
    apply Subtype.ext
    funext cell
    exact realCoordinateJet_smul coordinate scalar (field.1 cell)

@[simp] theorem coordinateCore_apply {dimension : ℕ} (parameters : PhaseParameters)
    (coordinate : Fin 2) (field : ACore parameters dimension) (cell : ℤ) :
    (coordinateCore parameters coordinate field).1 cell =
      realCoordinateJet coordinate (field.1 cell) := rfl

theorem coordinateCore_coordinates_bound {dimension : ℕ} (parameters : PhaseParameters)
    (coordinate : Fin 2) (field : ACore parameters dimension) (grade : ℕ) :
    ‖cartesianGradeCoordinates parameters grade (coordinateCore parameters coordinate field)‖ ≤
      coordinateRowConstant grade * ‖cartesianGradeCoordinates parameters grade field‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (coordinateRowConstant_nonneg grade)
    (norm_nonneg _))).mp
  have original := (memlp_iff_summable_sq _).mp (field.property grade)
  have transformed := (memlp_iff_summable_sq _).mp
    ((coordinateCore parameters coordinate field).property grade)
  have sumBound := transformed.tsum_le_tsum (fun cell => by
    simpa only [mul_pow, rawCartesianGradeCoordinates, coordinateCore_apply] using
      pow_le_pow_left₀ (norm_nonneg _)
        (realCoordinateJet_row_le (grade := grade) parameters cell coordinate (field.1 cell)) 2)
    (original.mul_left (coordinateRowConstant grade ^ 2))
  rw [tsum_mul_left] at sumBound
  rw [mul_pow, cartesianGradeCoordinates_norm_sq, cartesianGradeCoordinates_norm_sq]
  simpa only [rawCartesianGradeCoordinates_norm_sq] using sumBound

theorem coordinateCore_zero_first_jets {dimension : ℕ} (parameters : PhaseParameters)
    (coordinate : Fin 2) (field : ACore parameters dimension)
    (zeroJets : ∀ cell, ZeroCartesianFirstJets (field.1 cell)) :
    ∀ cell, ZeroCartesianFirstJets ((coordinateCore parameters coordinate field).1 cell) :=
  fun cell => realCoordinateJet_zero_first_jets coordinate (field.1 cell) (zeroJets cell)

/-- One planar scalar component as a value operator into dimension one. -/
def planarComponentMap (coordinate : Fin 2) : ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 1 :=
  LinearMap.toContinuousLinearMap
    { toFun := fun value => WithLp.toLp 2 ![value coordinate]
      map_add' := by
        intro first second
        apply PiLp.ext
        intro component
        fin_cases component
        simp
      map_smul' := by
        intro scalar value
        apply PiLp.ext
        intro component
        fin_cases component
        simp }

theorem planarComponentMap_norm_le (coordinate : Fin 2) : ‖planarComponentMap coordinate‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro value
  rw [one_mul]
  have componentNorm : ‖planarComponentMap coordinate value‖ = ‖value coordinate‖ := by
    rw [show planarComponentMap coordinate value = WithLp.toLp 2 ![value coordinate] from rfl,
      PiLp.norm_eq_of_L2]
    simp
  rw [componentNorm]
  exact PiLp.norm_apply_le value coordinate

/-- The transposed derivative-seed row coefficients `(M'ᵀ ·)_j`. -/
def derivativeRowCoefficients (parameter : Seed.Parameters) (coordinate : Fin 2) (shift : ℤ) :
    ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 1 :=
  (planarComponentMap coordinate).comp
    (transposeOperator (Seed.actualCells 2 parameter shift))

theorem derivativeRowCoefficients_envelope_summable (phase : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (coordinate : Fin 2) (grade : ℕ) :
    Summable (envelopeTerm phase grade (derivativeRowCoefficients parameter coordinate)) := by
  apply Summable.of_nonneg_of_le (fun cell => envelopeTerm_nonnegative phase grade _ cell)
    (fun cell => ?_) ((seedCells_all_summable phase parameter inside 2 grade).mul_left 4)
  unfold envelopeTerm
  have compBound : ‖derivativeRowCoefficients parameter coordinate cell‖ ≤
      4 * ‖Seed.actualCells 2 parameter cell‖ := by
    calc ‖derivativeRowCoefficients parameter coordinate cell‖
        ≤ ‖planarComponentMap coordinate‖ *
            ‖transposeOperator (Seed.actualCells 2 parameter cell)‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * (4 * ‖Seed.actualCells 2 parameter cell‖) :=
          mul_le_mul (planarComponentMap_norm_le coordinate)
            (transposeOperator_norm_le _) (norm_nonneg _) zero_le_one
      _ = 4 * ‖Seed.actualCells 2 parameter cell‖ := one_mul _
  calc Real.exp (phase.sigma0 * cellFrequency cell) * cellPolynomialWeight cell ^ grade *
      ‖derivativeRowCoefficients parameter coordinate cell‖
      ≤ Real.exp (phase.sigma0 * cellFrequency cell) * cellPolynomialWeight cell ^ grade *
        (4 * ‖Seed.actualCells 2 parameter cell‖) :=
        mul_le_mul_of_nonneg_left compBound
          (mul_nonneg (Real.exp_pos _).le
            (pow_nonneg (zero_lt_one.trans_le (cellPolynomialWeight_one_le cell)).le _))
    _ = 4 * (Real.exp (phase.sigma0 * cellFrequency cell) * cellPolynomialWeight cell ^ grade *
        ‖Seed.actualCells 2 parameter cell‖) := by ring

/-- The actual Cartesian multiplication `u ↦ u · M' y`, written as the exact
sum of the two coordinate multiples of the transposed derivative-seed rows. -/
def derivativeDotCore (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) : ACore phase 2 →ₗ[ℂ] ACore phase 1 :=
  (coordinateCore phase 0).comp (smoothMultiplier phase
      (derivativeRowCoefficients parameter 0)
      (derivativeRowCoefficients_envelope_summable phase parameter inside 0)) +
    (coordinateCore phase 1).comp (smoothMultiplier phase
      (derivativeRowCoefficients parameter 1)
      (derivativeRowCoefficients_envelope_summable phase parameter inside 1))

/-- The literal pointwise value of the derivative-seed dot: the absolutely
convergent cell convolution of `u` against the transposed rows, each
multiplied by its literal coordinate. -/
theorem derivativeDotCore_value (phase : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore phase 2)
    (cell : ℤ) (point : ClosedDisk) :
    ((derivativeDotCore phase parameter inside field).1 cell).value point =
      point.val 0 • ∑' shift, derivativeRowCoefficients parameter 0 shift
          ((field.1 (cell - shift)).value point) +
        point.val 1 • ∑' shift, derivativeRowCoefficients parameter 1 shift
          ((field.1 (cell - shift)).value point) := by
  have firstValue := (smoothMultiplier_value_hasSum phase
    (derivativeRowCoefficients parameter 0)
    (derivativeRowCoefficients_envelope_summable phase parameter inside 0)
    field cell point).tsum_eq
  have secondValue := (smoothMultiplier_value_hasSum phase
    (derivativeRowCoefficients parameter 1)
    (derivativeRowCoefficients_envelope_summable phase parameter inside 1)
    field cell point).tsum_eq
  change ((coordinateCore phase 0 (smoothMultiplier phase _ _ field)).1 cell).value point +
      ((coordinateCore phase 1 (smoothMultiplier phase _ _ field)).1 cell).value point = _
  rw [coordinateCore_apply, coordinateCore_apply, realCoordinateJet_value,
    realCoordinateJet_value, firstValue, secondValue]

end Grad.Constraints.Gauges
