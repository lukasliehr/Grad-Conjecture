import GaugeCoordinateJet

noncomputable section

set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace Grad.Constraints.Gauges

open Grad.ClosedJets Grad.CartesianState Grad.Constraints

theorem closedContinuousToDiskL2_finset_sum {dimension : ℕ} {Index : Type*}
    (family : Index → ContinuousMap ClosedDisk (ComplexEuclidean dimension))
    (support : Finset Index) :
    closedContinuousToDiskL2 (∑ index ∈ support, family index) =
      ∑ index ∈ support, closedContinuousToDiskL2 (family index) :=
  map_sum (AddMonoidHom.mk' closedContinuousToDiskL2
    (fun first second => closedContinuousToDiskL2_add first second)) family support

theorem realCoordinateJet_closedDerivative {dimension : ℕ} (coordinate : Fin 2)
    (field : ClosedJet dimension) (order : ℕ) (word : CartesianWord order) :
    closedDerivative (realCoordinateJet coordinate field) order word =
      smoothScalarDerivativeExtension (coordinateLinearMap coordinate)
        (coordinateLinearMap coordinate).contDiff field order word :=
  smoothScalarWeightedJet_closedDerivative _ _ field order word

/-- Zero first Cartesian jets are preserved by coordinate multiplication. -/
theorem realCoordinateJet_zero_first_jets {dimension : ℕ} (coordinate : Fin 2)
    (field : ClosedJet dimension) (zeroJets : ZeroCartesianFirstJets field) :
    ZeroCartesianFirstJets (realCoordinateJet coordinate field) := by
  intro order orderBound word
  rw [realCoordinateJet_closedDerivative, coordinateExtension_eq_sum,
    ContinuousMap.sum_apply]
  apply Finset.sum_eq_zero
  intro selected _
  have complementBound : selectedᶜ.card ≤ 1 :=
    (Finset.card_le_univ selectedᶜ).trans (by rw [Fintype.card_fin]; exact orderBound)
  change smoothScalarDerivativeFactor (coordinateLinearMap coordinate)
      (coordinateLinearMap coordinate).contDiff order word selected
        ⟨0, by simp [closedUnitDisk]⟩ •
    closedDerivative field selectedᶜ.card
      (Grad.AnalyticWeights.Higher.subword word selectedᶜ) ⟨0, by simp [closedUnitDisk]⟩ = 0
  rw [zeroJets selectedᶜ.card complementBound
    (Grad.AnalyticWeights.Higher.subword word selectedᶜ)]
  exact smul_zero (A := ComplexEuclidean dimension) _

/-- The same-grade constant of one coordinate multiplication. -/
def coordinateRowConstant (grade : ℕ) : ℝ :=
  Real.sqrt (Fintype.card (GradeMultiIndex grade)) * 2 ^ grade

theorem coordinateRowConstant_nonneg (grade : ℕ) : 0 ≤ coordinateRowConstant grade :=
  mul_nonneg (Real.sqrt_nonneg _) (by positivity)

theorem realCoordinateJet_entry_le {dimension grade : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (coordinate : Fin 2) (field : ClosedJet dimension)
    (index : GradeMultiIndex grade) :
    ‖cellGradeRowLinear (grade := grade) parameters cell
        (realCoordinateJet coordinate field) index‖ ≤
      2 ^ grade * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  have frequencyOne := cellFrequency_one_le cell
  have frequencyPositive : (0 : ℝ) < cellFrequency cell := lt_of_lt_of_le zero_lt_one frequencyOne
  rw [cellGradeRowLinear_apply, norm_smul, Complex.norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos frequencyPositive]
  set exponent := grade - cartesianOrder index.toCartesian with exponent_def
  have weightedIdentity : closedMultiDerivative
      (phaseWeightedJet parameters cell (realCoordinateJet coordinate field))
        index.toCartesian =
      closedDerivative (realCoordinateJet coordinate
        (phaseWeightedJet parameters cell field))
        (cartesianOrder index.toCartesian) (cartesianMultiIndexWord index.toCartesian) := by
    rw [realCoordinateJet_phaseWeighted]
    rfl
  rw [weightedIdentity, realCoordinateJet_closedDerivative, coordinateExtension_eq_sum,
    closedContinuousToDiskL2_finset_sum]
  set weighted := phaseWeightedJet parameters cell field with weighted_def
  have termBound (selected : Finset (Fin (cartesianOrder index.toCartesian))) :
      cellFrequency cell ^ exponent * ‖closedContinuousToDiskL2
        (coordinateLeibnizTerm coordinate weighted
          (cartesianMultiIndexWord index.toCartesian) selected)‖ ≤
      ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
    have complementCard : selectedᶜ.card ≤ cartesianOrder index.toCartesian :=
      (Finset.card_le_univ selectedᶜ).trans (by rw [Fintype.card_fin])
    have orderBound : cartesianOrder index.toCartesian ≤ grade := index.property
    set subwordUsed := Grad.AnalyticWeights.Higher.subword
      (cartesianMultiIndexWord index.toCartesian) selectedᶜ with subwordUsed_def
    have subOrder : cartesianOrder (cartesianWordIndex subwordUsed) = selectedᶜ.card :=
      cartesianWordIndex_order subwordUsed
    have firstComponentBound : (cartesianWordIndex subwordUsed).1 < grade + 1 := by
      have componentLe : (cartesianWordIndex subwordUsed).1 ≤
          cartesianOrder (cartesianWordIndex subwordUsed) := Nat.le_add_right _ _
      omega
    have secondComponentBound : (cartesianWordIndex subwordUsed).2 < grade + 1 := by
      have componentLe : (cartesianWordIndex subwordUsed).2 ≤
          cartesianOrder (cartesianWordIndex subwordUsed) := Nat.le_add_left _ _
      omega
    set subIndex : GradeMultiIndex grade :=
      ⟨(⟨(cartesianWordIndex subwordUsed).1, firstComponentBound⟩,
        ⟨(cartesianWordIndex subwordUsed).2, secondComponentBound⟩), by
          change (cartesianWordIndex subwordUsed).1 + (cartesianWordIndex subwordUsed).2 ≤ grade
          have : cartesianOrder (cartesianWordIndex subwordUsed) =
            (cartesianWordIndex subwordUsed).1 + (cartesianWordIndex subwordUsed).2 := rfl
          omega⟩ with subIndex_def
    have subIndexCartesian : subIndex.toCartesian = cartesianWordIndex subwordUsed := rfl
    have derivativeBridge : closedDerivative weighted selectedᶜ.card subwordUsed =
        closedMultiDerivative weighted subIndex.toCartesian := by
      rw [subIndexCartesian]
      exact closedDerivative_eq_closedMultiDerivative_wordIndex weighted subwordUsed
    have entryValue : ‖cellGradeRowLinear (grade := grade) parameters cell field subIndex‖ =
        cellFrequency cell ^ (grade - cartesianOrder subIndex.toCartesian) *
          ‖closedContinuousToDiskL2 (closedMultiDerivative weighted subIndex.toCartesian)‖ := by
      rw [cellGradeRowLinear_apply, norm_smul, Complex.norm_pow, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos frequencyPositive]
    have exponentLe : exponent ≤ grade - cartesianOrder subIndex.toCartesian := by
      rw [exponent_def, subIndexCartesian, subOrder]
      exact Nat.sub_le_sub_left complementCard grade
    calc cellFrequency cell ^ exponent * ‖closedContinuousToDiskL2
          (coordinateLeibnizTerm coordinate weighted
            (cartesianMultiIndexWord index.toCartesian) selected)‖
        ≤ cellFrequency cell ^ exponent * ‖closedContinuousToDiskL2
            (closedDerivative weighted selectedᶜ.card subwordUsed)‖ :=
          mul_le_mul_of_nonneg_left (coordinateLeibnizTerm_L2_le coordinate weighted
            (cartesianMultiIndexWord index.toCartesian) selected)
            (pow_nonneg frequencyPositive.le _)
      _ ≤ cellFrequency cell ^ (grade - cartesianOrder subIndex.toCartesian) *
            ‖closedContinuousToDiskL2 (closedDerivative weighted selectedᶜ.card subwordUsed)‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ frequencyOne exponentLe)
            (norm_nonneg _)
      _ = ‖cellGradeRowLinear (grade := grade) parameters cell field subIndex‖ := by
          rw [entryValue, derivativeBridge]
      _ ≤ ‖cellGradeRowLinear (grade := grade) parameters cell field‖ :=
          PiLp.norm_apply_le _ subIndex
  calc cellFrequency cell ^ exponent * ‖∑ selected : Finset (Fin (cartesianOrder index.toCartesian)),
        closedContinuousToDiskL2 (coordinateLeibnizTerm coordinate weighted
          (cartesianMultiIndexWord index.toCartesian) selected)‖
      ≤ cellFrequency cell ^ exponent * ∑ selected : Finset (Fin (cartesianOrder index.toCartesian)),
          ‖closedContinuousToDiskL2 (coordinateLeibnizTerm coordinate weighted
            (cartesianMultiIndexWord index.toCartesian) selected)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (pow_nonneg frequencyPositive.le _)
    _ = ∑ selected : Finset (Fin (cartesianOrder index.toCartesian)),
          cellFrequency cell ^ exponent * ‖closedContinuousToDiskL2
            (coordinateLeibnizTerm coordinate weighted
              (cartesianMultiIndexWord index.toCartesian) selected)‖ := Finset.mul_sum _ _ _
    _ ≤ ∑ _selected : Finset (Fin (cartesianOrder index.toCartesian)),
          ‖cellGradeRowLinear (grade := grade) parameters cell field‖ :=
        Finset.sum_le_sum (fun selected _ => termBound selected)
    _ = (2 ^ cartesianOrder index.toCartesian : ℝ) *
          ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_finset, Fintype.card_fin]
        simp [nsmul_eq_mul]
    _ ≤ 2 ^ grade * ‖cellGradeRowLinear (grade := grade) parameters cell field‖ :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_two index.property)
          (norm_nonneg _)

/-- The exact same-grade cell row bound for one coordinate multiplication. -/
theorem realCoordinateJet_row_le {dimension grade : ℕ} (parameters : PhaseParameters)
    (cell : ℤ) (coordinate : Fin 2) (field : ClosedJet dimension) :
    ‖cellGradeRowLinear (grade := grade) parameters cell
        (realCoordinateJet coordinate field)‖ ≤
      coordinateRowConstant grade *
        ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
  have rowNonneg : (0 : ℝ) ≤ ‖cellGradeRowLinear (grade := grade) parameters cell field‖ :=
    norm_nonneg _
  have squareBound : ‖cellGradeRowLinear (grade := grade) parameters cell
      (realCoordinateJet coordinate field)‖ ^ 2 ≤
      (Fintype.card (GradeMultiIndex grade) : ℝ) *
        (2 ^ grade * ‖cellGradeRowLinear (grade := grade) parameters cell field‖) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    calc (∑ index : GradeMultiIndex grade, ‖cellGradeRowLinear (grade := grade) parameters cell
          (realCoordinateJet coordinate field) index‖ ^ 2)
        ≤ ∑ _index : GradeMultiIndex grade,
            (2 ^ grade * ‖cellGradeRowLinear (grade := grade) parameters cell field‖) ^ 2 :=
          Finset.sum_le_sum (fun index _ => pow_le_pow_left₀ (norm_nonneg _)
            (realCoordinateJet_entry_le parameters cell coordinate field index) 2)
      _ = (Fintype.card (GradeMultiIndex grade) : ℝ) *
            (2 ^ grade * ‖cellGradeRowLinear (grade := grade) parameters cell field‖) ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ]
          simp [nsmul_eq_mul]
  calc ‖cellGradeRowLinear (grade := grade) parameters cell
        (realCoordinateJet coordinate field)‖
      = Real.sqrt (‖cellGradeRowLinear (grade := grade) parameters cell
          (realCoordinateJet coordinate field)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((Fintype.card (GradeMultiIndex grade) : ℝ) *
          (2 ^ grade * ‖cellGradeRowLinear (grade := grade) parameters cell field‖) ^ 2) :=
        Real.sqrt_le_sqrt squareBound
    _ = Real.sqrt (Fintype.card (GradeMultiIndex grade)) *
          (2 ^ grade * ‖cellGradeRowLinear (grade := grade) parameters cell field‖) := by
        rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq (by positivity)]
    _ = coordinateRowConstant grade *
          ‖cellGradeRowLinear (grade := grade) parameters cell field‖ := by
        rw [coordinateRowConstant]
        ring

end Grad.Constraints.Gauges
