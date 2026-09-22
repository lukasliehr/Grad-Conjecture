import AxisDataCore

noncomputable section

open scoped BigOperators ContDiff
open MeasureTheory

namespace Grad.AxisSplit

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds

/-! ### Disk `L²` versus supremum -/

/-- The square root of the finite disk area. -/
def diskVolumeSqrt : ℝ := Real.sqrt ((volume.restrict openUnitDisk).real Set.univ)

theorem diskVolumeSqrt_nonneg : 0 ≤ diskVolumeSqrt := Real.sqrt_nonneg _

theorem l2_norm_le_sup {dimension : ℕ}
    (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    ‖closedContinuousToDiskL2 field‖ ≤ diskVolumeSqrt * ‖field‖ := by
  have squareBound := closedContinuousToDiskL2_norm_sq_le field
  have sqrtBound := Real.sqrt_le_sqrt squareBound
  rw [Real.sqrt_sq (norm_nonneg _)] at sqrtBound
  apply sqrtBound.trans_eq
  rw [Real.sqrt_mul measureReal_nonneg (‖field‖ ^ 2), Real.sqrt_sq (norm_nonneg _)]
  rfl

/-! ### Supremum bounds for the phase-weight derivative words -/

/-- The maximal phase weight sits at the axis. -/
theorem cartesianWeight_le_exp (parameters : PhaseParameters) (cell : ℤ)
    (point : SpatialPlane) :
    cartesianWeight parameters cell point ≤
      Real.exp (parameters.sigma0 * cellFrequency cell) := by
  obtain ⟨-, phaseFormula, weightFormula, -, -⟩ :=
    Grad.AnalyticWeights.Calculus.Consumer.actualFormulas parameters.sigma0
      parameters.gamma 1 cell point
  have weightAsExp : cartesianWeight parameters cell point =
      Real.exp (Grad.AnalyticWeights.Calculus.physicalPhase parameters.sigma0
        parameters.gamma 1 cell point) := weightFormula
  rw [weightAsExp]
  apply Real.exp_le_exp.mpr
  rw [phaseFormula]
  have sqrtGe : 1 ≤ Real.sqrt (Grad.AnalyticWeights.Calculus.radicand 1 cell point) := by
    have sqrtMono : Real.sqrt 1 ≤
        Real.sqrt (Grad.AnalyticWeights.Calculus.radicand 1 cell point) := by
      apply Real.sqrt_le_sqrt
      unfold Grad.AnalyticWeights.Calculus.radicand
      have termNonneg : 0 ≤ (1 : ℝ) ^ 2 * ‖point‖ ^ 2 *
          Grad.CellWeights.cellWeight cell ^ 2 := by positivity
      linarith
    rwa [Real.sqrt_one] at sqrtMono
  have subtractNonneg : 0 ≤ parameters.gamma *
      (Real.sqrt (Grad.AnalyticWeights.Calculus.radicand 1 cell point) - 1) :=
    mul_nonneg parameters.gamma_pos.le (by linarith)
  have frequencyEq : cellFrequency cell = Grad.CellWeights.cellWeight cell := rfl
  rw [frequencyEq]
  linarith

/-- One uniform constant for each order of phase-weight derivative words. -/
def weightWordConstant (parameters : PhaseParameters) (rank : ℕ) : ℝ :=
  max 1 (Grad.AnalyticWeights.Higher.partitionProductConstant rank *
    Grad.AnalyticWeights.Higher.weightCost rank parameters.gamma 1)

theorem weightWordConstant_nonneg (parameters : PhaseParameters) (rank : ℕ) :
    0 ≤ weightWordConstant parameters rank :=
  le_trans zero_le_one (le_max_left _ _)

theorem spatialBasis_norm_le (direction : Fin 2) : ‖spatialBasis direction‖ ≤ 1 := by
  have basisNorm : ‖spatialBasis direction‖ = ‖(1 : ℝ)‖ := by
    change ‖PiLp.single (β := fun _ : Fin 2 => ℝ) 2 direction (1 : ℝ)‖ = ‖(1 : ℝ)‖
    exact PiLp.norm_single 2 (fun _ : Fin 2 => ℝ) direction 1
  rw [basisNorm, norm_one]

/-- Every iterated weight derivative along unit directions is dominated by
the axis weight and the exact cell-frequency power. -/
theorem weight_iterated_word_bound (parameters : PhaseParameters) (cell : ℤ)
    (rank : ℕ) (directions : Fin rank → SpatialPlane)
    (directionNorms : ∀ position, ‖directions position‖ ≤ 1) (point : SpatialPlane) :
    ‖iteratedFDeriv ℝ rank (cartesianWeight parameters cell) point directions‖ ≤
      weightWordConstant parameters rank *
        Real.exp (parameters.sigma0 * cellFrequency cell) * cellFrequency cell ^ rank := by
  rcases Nat.eq_zero_or_pos rank with rankZero | rankPositive
  · subst rankZero
    rw [iteratedFDeriv_zero_apply, pow_zero, mul_one]
    rw [Real.norm_of_nonneg (cartesianWeight_pos parameters cell point).le]
    calc cartesianWeight parameters cell point ≤
        Real.exp (parameters.sigma0 * cellFrequency cell) :=
          cartesianWeight_le_exp parameters cell point
      _ = 1 * Real.exp (parameters.sigma0 * cellFrequency cell) := (one_mul _).symm
      _ ≤ weightWordConstant parameters 0 *
          Real.exp (parameters.sigma0 * cellFrequency cell) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le
  · have operatorBound := ContinuousMultilinearMap.le_opNorm
      (iteratedFDeriv ℝ rank (cartesianWeight parameters cell) point) directions
    have productBound : (∏ position, ‖directions position‖) ≤ 1 :=
      Finset.prod_le_one (fun position _ => norm_nonneg _)
        (fun position _ => directionNorms position)
    have iteratedBound := Grad.AnalyticWeights.Higher.physicalWeight_iterated_norm_bound
      parameters.sigma0 parameters.gamma 1 cell parameters.gamma_pos.le zero_le_one
      rank rankPositive point
    have costNonneg : 0 ≤ Grad.AnalyticWeights.Higher.partitionProductConstant rank *
        Grad.AnalyticWeights.Higher.weightCost rank parameters.gamma 1 := by
      by_contra negative
      push Not at negative
      have leftNonneg : (0 : ℝ) ≤
          ‖iteratedFDeriv ℝ rank (cartesianWeight parameters cell) point‖ := norm_nonneg _
      have rightNegative : Grad.AnalyticWeights.Higher.partitionProductConstant rank *
          Grad.AnalyticWeights.Higher.weightCost rank parameters.gamma 1 *
          cartesianWeight parameters cell point *
          Grad.CellWeights.cellWeight cell ^ rank < 0 := by
        apply mul_neg_of_neg_of_pos
        · exact mul_neg_of_neg_of_pos negative (cartesianWeight_pos parameters cell point)
        · exact pow_pos (Grad.CellWeights.cellWeight_pos cell) rank
      exact absurd (leftNonneg.trans iteratedBound) (not_le.mpr rightNegative)
    calc ‖iteratedFDeriv ℝ rank (cartesianWeight parameters cell) point directions‖ ≤
        ‖iteratedFDeriv ℝ rank (cartesianWeight parameters cell) point‖ *
          ∏ position, ‖directions position‖ := operatorBound
      _ ≤ ‖iteratedFDeriv ℝ rank (cartesianWeight parameters cell) point‖ * 1 :=
          mul_le_mul_of_nonneg_left productBound (norm_nonneg _)
      _ = ‖iteratedFDeriv ℝ rank (cartesianWeight parameters cell) point‖ := mul_one _
      _ ≤ Grad.AnalyticWeights.Higher.partitionProductConstant rank *
            Grad.AnalyticWeights.Higher.weightCost rank parameters.gamma 1 *
            cartesianWeight parameters cell point *
            Grad.CellWeights.cellWeight cell ^ rank := iteratedBound
      _ ≤ weightWordConstant parameters rank *
            Real.exp (parameters.sigma0 * cellFrequency cell) *
            cellFrequency cell ^ rank := by
          have weightBound := cartesianWeight_le_exp parameters cell point
          have stepOne : Grad.AnalyticWeights.Higher.partitionProductConstant rank *
              Grad.AnalyticWeights.Higher.weightCost rank parameters.gamma 1 *
              cartesianWeight parameters cell point ≤
              weightWordConstant parameters rank *
                Real.exp (parameters.sigma0 * cellFrequency cell) := by
            apply mul_le_mul (le_max_right _ _) weightBound
              (cartesianWeight_pos parameters cell point).le
              (weightWordConstant_nonneg parameters rank)
          apply mul_le_mul_of_nonneg_right stepOne
            (pow_nonneg (cellFrequency_pos cell).le rank)

/-! ### The uniform row bound for a fixed closed jet across all cells -/

/-- The supremum content of one derivative word of a fixed jet, with the
weight-word constants of every Leibniz subset. -/
def jetWordContent (parameters : PhaseParameters) {dimension : ℕ}
    (field : ClosedJet dimension) {order : ℕ} (word : CartesianWord order) : ℝ :=
  ∑ selected : Finset (Fin order), weightWordConstant parameters selected.card *
    ‖closedDerivative field selectedᶜ.card
      (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ)‖

theorem jetWordContent_nonneg (parameters : PhaseParameters) {dimension : ℕ}
    (field : ClosedJet dimension) {order : ℕ} (word : CartesianWord order) :
    0 ≤ jetWordContent parameters field word :=
  Finset.sum_nonneg (fun selected _ =>
    mul_nonneg (weightWordConstant_nonneg parameters selected.card) (norm_nonneg _))

/-- The pointwise bound for one weighted derivative word of a fixed jet. -/
theorem weighted_word_sup_bound (parameters : PhaseParameters) {dimension : ℕ}
    (field : ClosedJet dimension) (cell : ℤ) {order : ℕ} (word : CartesianWord order)
    (point : ClosedDisk) :
    ‖closedDerivative (phaseWeightedJet parameters cell field) order word point‖ ≤
      jetWordContent parameters field word *
        Real.exp (parameters.sigma0 * cellFrequency cell) *
        cellFrequency cell ^ order := by
  rw [phaseWeightedJet_derivative]
  change ‖∑ selected : Finset (Fin order),
    smoothScalarDerivativeFactor (cartesianWeight parameters cell)
      (cartesianWeight_contDiff parameters cell) order word selected point •
      closedDerivative field selectedᶜ.card
        (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ) point‖ ≤ _
  apply le_trans (norm_sum_le _ _)
  have termBound : ∀ selected : Finset (Fin order),
      ‖smoothScalarDerivativeFactor (cartesianWeight parameters cell)
        (cartesianWeight_contDiff parameters cell) order word selected point •
        closedDerivative field selectedᶜ.card
          (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ) point‖ ≤
      weightWordConstant parameters selected.card *
        ‖closedDerivative field selectedᶜ.card
          (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ)‖ *
        (Real.exp (parameters.sigma0 * cellFrequency cell) *
          cellFrequency cell ^ order) := by
    intro selected
    rw [norm_smul]
    have factorBound : ‖smoothScalarDerivativeFactor (cartesianWeight parameters cell)
        (cartesianWeight_contDiff parameters cell) order word selected point‖ ≤
        weightWordConstant parameters selected.card *
          Real.exp (parameters.sigma0 * cellFrequency cell) *
          cellFrequency cell ^ selected.card := by
      change ‖iteratedFDeriv ℝ selected.card (cartesianWeight parameters cell) point.val
        (fun position => spatialBasis (word (selected.orderEmbOfFin rfl position)))‖ ≤ _
      exact weight_iterated_word_bound parameters cell selected.card _
        (fun position => spatialBasis_norm_le _) point.val
    have jetBound : ‖closedDerivative field selectedᶜ.card
        (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ) point‖ ≤
        ‖closedDerivative field selectedᶜ.card
          (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ)‖ :=
      ContinuousMap.norm_coe_le_norm _ _
    have powerBound : cellFrequency cell ^ selected.card ≤ cellFrequency cell ^ order := by
      apply pow_le_pow_right₀ (cellFrequency_one_le cell)
      have cardLe := Finset.card_le_univ selected
      rwa [Fintype.card_fin] at cardLe
    calc ‖smoothScalarDerivativeFactor (cartesianWeight parameters cell)
          (cartesianWeight_contDiff parameters cell) order word selected point‖ *
          ‖closedDerivative field selectedᶜ.card
            (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ) point‖ ≤
        (weightWordConstant parameters selected.card *
          Real.exp (parameters.sigma0 * cellFrequency cell) *
          cellFrequency cell ^ selected.card) *
          ‖closedDerivative field selectedᶜ.card
            (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ)‖ :=
          mul_le_mul factorBound jetBound (norm_nonneg _)
            (mul_nonneg (mul_nonneg (weightWordConstant_nonneg parameters selected.card)
              (Real.exp_pos _).le) (pow_nonneg (cellFrequency_pos cell).le _))
      _ ≤ (weightWordConstant parameters selected.card *
          Real.exp (parameters.sigma0 * cellFrequency cell) *
          cellFrequency cell ^ order) *
          ‖closedDerivative field selectedᶜ.card
            (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ)‖ := by
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          apply mul_le_mul_of_nonneg_left powerBound
            (mul_nonneg (weightWordConstant_nonneg parameters selected.card)
              (Real.exp_pos _).le)
      _ = weightWordConstant parameters selected.card *
          ‖closedDerivative field selectedᶜ.card
            (Grad.RepresentedKernel.SpatialProduct.subword word selectedᶜ)‖ *
          (Real.exp (parameters.sigma0 * cellFrequency cell) *
            cellFrequency cell ^ order) := by ring
  apply le_trans (Finset.sum_le_sum (fun selected _ => termBound selected))
  rw [← Finset.sum_mul]
  apply le_of_eq
  unfold jetWordContent
  ring

/-- The `T`-weighted uniform cell-row bound for a fixed closed jet. -/
theorem fixedJet_row_bound (parameters : PhaseParameters) {dimension : ℕ}
    (field : ClosedJet dimension) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ cell : ℤ,
      ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ≤
        constant * axisWeight parameters grade cell := by
  refine ⟨∑ index : GradeMultiIndex grade, diskVolumeSqrt *
    jetWordContent parameters field
      (cartesianMultiIndexWord index.toCartesian), ?_, ?_⟩
  · exact Finset.sum_nonneg (fun index _ =>
      mul_nonneg diskVolumeSqrt_nonneg (jetWordContent_nonneg parameters field _))
  intro cell
  set summandBound : GradeMultiIndex grade → ℝ := fun index =>
    cellFrequency cell ^ (grade - cartesianOrder index.toCartesian) *
      ‖closedContinuousToDiskL2 (closedMultiDerivative
        (phaseWeightedJet parameters cell field) index.toCartesian)‖ with summandDef
  have rowSquare := cellGradeRow_norm_sq (grade := grade) parameters cell field
  have summandNonneg : ∀ index : GradeMultiIndex grade, 0 ≤ summandBound index := by
    intro index
    exact mul_nonneg (pow_nonneg (cellFrequency_pos cell).le _) (norm_nonneg _)
  have squareIdentity : ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ^ 2 =
      ∑ index : GradeMultiIndex grade, summandBound index ^ 2 := by
    rw [rowSquare]
    apply Finset.sum_congr rfl
    intro index _
    rw [summandDef]
    rw [mul_pow, ← pow_mul]
    ring_nf
  have sumSquareLe : (∑ index : GradeMultiIndex grade, summandBound index ^ 2) ≤
      (∑ index : GradeMultiIndex grade, summandBound index) ^ 2 := by
    rw [sq (∑ index : GradeMultiIndex grade, summandBound index), Finset.sum_mul]
    apply Finset.sum_le_sum
    intro index _
    rw [sq]
    apply mul_le_mul_of_nonneg_left _ (summandNonneg index)
    exact Finset.single_le_sum (fun inner _ => summandNonneg inner) (Finset.mem_univ index)
  have rowLe : ‖cellGradeRowLinear (grade := grade) parameters cell field‖ ≤
      ∑ index : GradeMultiIndex grade, summandBound index := by
    have sqrtStep := Real.sqrt_le_sqrt (squareIdentity.le.trans sumSquareLe)
    rwa [Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (Finset.sum_nonneg (fun index _ => summandNonneg index))] at sqrtStep
  apply rowLe.trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro index _
  have orderLe : cartesianOrder index.toCartesian ≤ grade := index.property
  have l2Bound : ‖closedContinuousToDiskL2 (closedMultiDerivative
      (phaseWeightedJet parameters cell field) index.toCartesian)‖ ≤
      diskVolumeSqrt * (jetWordContent parameters field
        (cartesianMultiIndexWord index.toCartesian) *
        Real.exp (parameters.sigma0 * cellFrequency cell) *
        cellFrequency cell ^ cartesianOrder index.toCartesian) := by
    apply (l2_norm_le_sup _).trans
    apply mul_le_mul_of_nonneg_left _ diskVolumeSqrt_nonneg
    apply (ContinuousMap.norm_le _
      (mul_nonneg (mul_nonneg (jetWordContent_nonneg parameters field _)
        (Real.exp_pos _).le) (pow_nonneg (cellFrequency_pos cell).le _))).mpr
    intro point
    exact weighted_word_sup_bound parameters field cell
      (cartesianMultiIndexWord index.toCartesian) point
  calc summandBound index ≤
      cellFrequency cell ^ (grade - cartesianOrder index.toCartesian) *
        (diskVolumeSqrt * (jetWordContent parameters field
          (cartesianMultiIndexWord index.toCartesian) *
          Real.exp (parameters.sigma0 * cellFrequency cell) *
          cellFrequency cell ^ cartesianOrder index.toCartesian)) := by
        rw [summandDef]
        exact mul_le_mul_of_nonneg_left l2Bound
          (pow_nonneg (cellFrequency_pos cell).le _)
    _ = diskVolumeSqrt * jetWordContent parameters field
          (cartesianMultiIndexWord index.toCartesian) *
          (Real.exp (parameters.sigma0 * cellFrequency cell) *
            (cellFrequency cell ^ (grade - cartesianOrder index.toCartesian) *
              cellFrequency cell ^ cartesianOrder index.toCartesian)) := by ring
    _ = diskVolumeSqrt * jetWordContent parameters field
          (cartesianMultiIndexWord index.toCartesian) *
          axisWeight parameters grade cell := by
        rw [← pow_add]
        rw [Nat.sub_add_cancel orderLe]
        rfl

end Grad.AxisSplit
