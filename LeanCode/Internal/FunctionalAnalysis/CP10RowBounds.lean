import CP9ModeAnnihilation

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Cor18

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Gauges Grad.Constraints.Multipliers Grad.BoundaryTrace Grad.BoundaryLift

/-! # Same-grade bounds of the physical row and the collar correction

`B_M : 𝒜^q → ∂^{q-1/2}` through the accepted N21 trace constant and the
two-shift domination, `C_{∂,M} : ∂^{q-1/2} → 𝒜^q` through the accepted lift
bound, the seed multiplier envelope and the coordinate rows; hence the outer
correction `I - C_{∂,M} B_M` is bounded at every grade `q ≥ 1`. -/

variable (parameters : PhaseParameters) (parameter : Seed.Parameters)
  (inside : parameter ∈ Seed.parameterDomain)

theorem boundaryWeight_sq (grade : ℕ) (mode : ℤ × ℤ) :
    boundaryWeight parameters grade mode ^ 2 =
      Real.exp (2 * boundaryPhase parameters mode.2) * boundaryFrequency mode ^ (2 * grade - 1) := by
  unfold boundaryWeight
  rw [mul_pow, Real.sq_sqrt (pow_nonneg (boundaryFrequency_pos mode).le _)]
  congr 1
  rw [← Real.exp_nat_mul]
  norm_num

/-- The seed-inverted planar field is bounded at every grade. -/
theorem rowField_norm_le (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ state : ACore parameters 3,
      ‖GradeCore.ofCoreLinear (grade := grade) (rowField parameters parameter inside state)‖ ≤
        constant * ‖GradeCore.ofCoreLinear (grade := grade) state‖ := by
  refine ⟨|multiplierConstant grade parameters.gamma *
    envelope parameters grade (seedInverseCells parameter)|, abs_nonneg _, ?_⟩
  intro state
  rw [ofCoreLinear_norm_coordinates, ofCoreLinear_norm_coordinates]
  unfold rowField
  simp only [LinearMap.comp_apply]
  rw [seedInverseCore_eq_full]
  refine (smoothMultiplier_coordinates_bound _ _ _ _).trans ?_
  calc multiplierConstant grade parameters.gamma * envelope parameters grade (seedInverseCells parameter) *
        ‖cartesianGradeCoordinates parameters grade (planarPartCore parameters state)‖
      ≤ |multiplierConstant grade parameters.gamma *
          envelope parameters grade (seedInverseCells parameter)| *
        ‖cartesianGradeCoordinates parameters grade (planarPartCore parameters state)‖ :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ |multiplierConstant grade parameters.gamma *
          envelope parameters grade (seedInverseCells parameter)| *
        ‖cartesianGradeCoordinates parameters grade state‖ :=
        mul_le_mul_of_nonneg_left
          (valueMapCore_coordinates_le_one parameters planarPartMap planarPartMap_norm_le state)
          (abs_nonneg _)

/-- The weighted trace energy of a core field against the accepted N21 constant. -/
theorem trace_energy_le (grade : ℕ) (gradePositive : 1 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ field : ACore parameters 2,
      Summable (fun mode : ℤ × ℤ => (boundaryWeight parameters grade mode *
        ‖originalBoundaryCoefficient parameters field mode‖) ^ 2) ∧
      (∑' mode : ℤ × ℤ, (boundaryWeight parameters grade mode *
        ‖originalBoundaryCoefficient parameters field mode‖) ^ 2) ≤
        constant * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 := by
  obtain ⟨constant, nonneg, bound⟩ := weightedBoundaryTrace grade gradePositive
  refine ⟨constant, nonneg, fun field => ?_⟩
  have identify : (fun mode : ℤ × ℤ => (boundaryWeight parameters grade mode *
      ‖originalBoundaryCoefficient parameters field mode‖) ^ 2) =
      fun mode => Real.exp (2 * boundaryPhase parameters mode.2) *
        boundaryFrequency mode ^ (2 * grade - 1) *
          ‖originalBoundaryCoefficient parameters field mode‖ ^ 2 := by
    funext mode
    rw [mul_pow, boundaryWeight_sq]
  rw [identify]
  exact bound 2 parameters field

/-- The physical row is bounded from grade `q` into the weighted boundary
carrier at grade `q`, for every `q ≥ 1`. -/
theorem physicalRow_norm_le (grade : ℕ) (gradePositive : 1 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ state : ACore parameters 3,
      ‖boundaryToGrade parameters grade gradePositive (physicalRow parameters parameter inside state)‖ ≤
        constant * ‖GradeCore.ofCoreLinear (grade := grade) state‖ := by
  obtain ⟨traceC, traceC_nonneg, traceBound⟩ := trace_energy_le parameters grade gradePositive
  obtain ⟨rowC, rowC_nonneg, rowBound⟩ := rowField_norm_le parameters parameter inside grade
  set firstConstant := cellPolynomialWeight 1 ^ grade with firstDef
  set secondConstant := cellPolynomialWeight (-1) ^ grade with secondDef
  set energyC : ℝ := (2 * firstConstant ^ 2 + 2 * secondConstant ^ 2) * traceC with energyDef
  have energyC_nonneg : 0 ≤ energyC := by
    rw [energyDef]
    positivity
  refine ⟨Real.sqrt energyC * rowC, mul_nonneg (Real.sqrt_nonneg _) rowC_nonneg, ?_⟩
  intro state
  set field := rowField parameters parameter inside state with fieldDef
  set weighted : ℤ × ℤ → ℝ := fun mode =>
    boundaryWeight parameters grade mode *
      ‖originalBoundaryCoefficient parameters field mode‖ with weightedDef
  obtain ⟨base, energy⟩ := traceBound field
  have shiftMinus : Summable (fun mode : ℤ × ℤ => weighted (mode.1 - 1, mode.2) ^ 2) :=
    ((Equiv.prodCongr (Equiv.subRight (1 : ℤ)) (Equiv.refl ℤ)).summable_iff
      (f := fun mode : ℤ × ℤ => weighted mode ^ 2)).mpr base
  have shiftPlus : Summable (fun mode : ℤ × ℤ => weighted (mode.1 + 1, mode.2) ^ 2) :=
    ((Equiv.prodCongr (Equiv.addRight (1 : ℤ)) (Equiv.refl ℤ)).summable_iff
      (f := fun mode : ℤ × ℤ => weighted mode ^ 2)).mpr base
  have shiftMinusSum : (∑' mode : ℤ × ℤ, weighted (mode.1 - 1, mode.2) ^ 2) =
      ∑' mode : ℤ × ℤ, weighted mode ^ 2 :=
    (Equiv.prodCongr (Equiv.subRight (1 : ℤ)) (Equiv.refl ℤ)).tsum_eq
      (fun mode : ℤ × ℤ => weighted mode ^ 2)
  have shiftPlusSum : (∑' mode : ℤ × ℤ, weighted (mode.1 + 1, mode.2) ^ 2) =
      ∑' mode : ℤ × ℤ, weighted mode ^ 2 :=
    (Equiv.prodCongr (Equiv.addRight (1 : ℤ)) (Equiv.refl ℤ)).tsum_eq
      (fun mode : ℤ × ℤ => weighted mode ^ 2)
  have weightedNonneg : ∀ pair : ℤ × ℤ, 0 ≤ weighted pair := fun pair =>
    mul_nonneg (boundaryWeight_pos parameters grade pair).le (norm_nonneg _)
  have termLe : ∀ mode : ℤ × ℤ, Real.exp (2 * boundaryPhase parameters mode.2) *
      boundaryFrequency mode ^ (2 * grade - 1) *
        ‖(physicalRow parameters parameter inside state).1 mode‖ ^ 2 ≤
      2 * firstConstant ^ 2 * weighted (mode.1 - 1, mode.2) ^ 2 +
        2 * secondConstant ^ 2 * weighted (mode.1 + 1, mode.2) ^ 2 := by
    intro mode
    rw [← boundaryWeight_sq, ← mul_pow, ← norm_weight_smul]
    have pointwise := physicalRowFamily_pointwise parameters parameter inside state grade mode
    have squared : ‖(boundaryWeight parameters grade mode : ℂ) •
        (physicalRow parameters parameter inside state).1 mode‖ ^ 2 ≤
        (firstConstant * weighted (mode.1 - 1, mode.2) +
          secondConstant * weighted (mode.1 + 1, mode.2)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) pointwise 2
    apply squared.trans
    nlinarith [sq_nonneg (firstConstant * weighted (mode.1 - 1, mode.2) -
      secondConstant * weighted (mode.1 + 1, mode.2))]
  have lhsSummable : Summable (fun mode : ℤ × ℤ =>
      Real.exp (2 * boundaryPhase parameters mode.2) *
        boundaryFrequency mode ^ (2 * grade - 1) *
          ‖(physicalRow parameters parameter inside state).1 mode‖ ^ 2) := by
    have member := (physicalRow parameters parameter inside state).property grade gradePositive
    rw [memlp_pair_iff_summable_sq] at member
    refine member.congr fun mode => ?_
    rw [norm_weight_smul, mul_pow, boundaryWeight_sq]
  have majorant : Summable (fun mode : ℤ × ℤ =>
      2 * firstConstant ^ 2 * weighted (mode.1 - 1, mode.2) ^ 2 +
        2 * secondConstant ^ 2 * weighted (mode.1 + 1, mode.2) ^ 2) :=
    (shiftMinus.mul_left (2 * firstConstant ^ 2)).add (shiftPlus.mul_left (2 * secondConstant ^ 2))
  have normSq : ‖boundaryToGrade parameters grade gradePositive
      (physicalRow parameters parameter inside state)‖ ^ 2 ≤
      energyC * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 := by
    rw [boundaryToGrade_norm_sq]
    calc (∑' mode : ℤ × ℤ, Real.exp (2 * boundaryPhase parameters mode.2) *
          boundaryFrequency mode ^ (2 * grade - 1) *
            ‖(physicalRow parameters parameter inside state).1 mode‖ ^ 2)
        ≤ ∑' mode : ℤ × ℤ, (2 * firstConstant ^ 2 * weighted (mode.1 - 1, mode.2) ^ 2 +
            2 * secondConstant ^ 2 * weighted (mode.1 + 1, mode.2) ^ 2) :=
          Summable.tsum_le_tsum termLe lhsSummable majorant
      _ = 2 * firstConstant ^ 2 * (∑' mode : ℤ × ℤ, weighted (mode.1 - 1, mode.2) ^ 2) +
            2 * secondConstant ^ 2 * (∑' mode : ℤ × ℤ, weighted (mode.1 + 1, mode.2) ^ 2) := by
          rw [Summable.tsum_add (shiftMinus.mul_left _) (shiftPlus.mul_left _), tsum_mul_left,
            tsum_mul_left]
      _ = (2 * firstConstant ^ 2 + 2 * secondConstant ^ 2) *
            ∑' mode : ℤ × ℤ, weighted mode ^ 2 := by
          rw [shiftMinusSum, shiftPlusSum]
          ring
      _ ≤ (2 * firstConstant ^ 2 + 2 * secondConstant ^ 2) *
            (traceC * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2) :=
          mul_le_mul_of_nonneg_left energy (by positivity)
      _ = energyC * ‖GradeCore.ofCoreLinear (grade := grade) field‖ ^ 2 := by
          rw [energyDef]
          ring
  have rowNorm := rowBound state
  have sqrtBound := Real.sqrt_le_sqrt normSq
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul energyC_nonneg, Real.sqrt_sq (norm_nonneg _)]
    at sqrtBound
  calc ‖boundaryToGrade parameters grade gradePositive
        (physicalRow parameters parameter inside state)‖
      ≤ Real.sqrt energyC * ‖GradeCore.ofCoreLinear (grade := grade) field‖ := sqrtBound
    _ ≤ Real.sqrt energyC * (rowC * ‖GradeCore.ofCoreLinear (grade := grade) state‖) :=
        mul_le_mul_of_nonneg_left rowNorm (Real.sqrt_nonneg _)
    _ = Real.sqrt energyC * rowC * ‖GradeCore.ofCoreLinear (grade := grade) state‖ := by ring

/-- The coordinate field `y • L` is bounded at every grade. -/
theorem coordinateVector_norm_le (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ field : ACore parameters 1,
      ‖cartesianGradeCoordinates parameters grade (coordinateVector parameters field)‖ ≤
        constant * ‖cartesianGradeCoordinates parameters grade field‖ := by
  refine ⟨(‖scalarInsertion 0‖ + ‖scalarInsertion 1‖) * |coordinateRowConstant grade|,
    mul_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (abs_nonneg _), ?_⟩
  intro field
  unfold coordinateVector
  simp only [LinearMap.add_apply, LinearMap.comp_apply]
  rw [map_add]
  have piece : ∀ coordinate : Fin 2,
      ‖cartesianGradeCoordinates parameters grade (valueMapCore (scalarInsertion coordinate) parameters
        (coordinateCore parameters coordinate field))‖ ≤
      ‖scalarInsertion coordinate‖ * (|coordinateRowConstant grade| *
        ‖cartesianGradeCoordinates parameters grade field‖) := by
    intro coordinate
    refine (valueMapCore_coordinates_bound _ parameters _ grade).trans ?_
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact (coordinateCore_coordinates_bound parameters coordinate field grade).trans
      (mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _))
  calc ‖cartesianGradeCoordinates parameters grade (valueMapCore (scalarInsertion 0) parameters
          (coordinateCore parameters 0 field)) +
        cartesianGradeCoordinates parameters grade (valueMapCore (scalarInsertion 1) parameters
          (coordinateCore parameters 1 field))‖
      ≤ ‖scalarInsertion 0‖ * (|coordinateRowConstant grade| *
            ‖cartesianGradeCoordinates parameters grade field‖) +
          ‖scalarInsertion 1‖ * (|coordinateRowConstant grade| *
            ‖cartesianGradeCoordinates parameters grade field‖) :=
        (norm_add_le _ _).trans (add_le_add (piece 0) (piece 1))
    _ = (‖scalarInsertion 0‖ + ‖scalarInsertion 1‖) * |coordinateRowConstant grade| *
          ‖cartesianGradeCoordinates parameters grade field‖ := by ring

/-- The collar correction is bounded from the weighted boundary carrier at
grade `q` into grade `q`, for every `q ≥ 1`. -/
theorem collarCorrection_norm_le (grade : ℕ) (gradePositive : 1 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ values : BoundaryCore parameters 1,
      ‖GradeCore.ofCoreLinear (grade := grade) (collarCorrection parameters parameter inside values)‖ ≤
        constant * ‖boundaryToGrade parameters grade gradePositive values‖ := by
  obtain ⟨vectorC, vectorC_nonneg, vectorBound⟩ := coordinateVector_norm_le parameters grade
  set matrixC : ℝ := |multiplierConstant grade parameters.gamma *
    envelope parameters grade (seedMatrixCells parameter)| with matrixDef
  refine ⟨matrixC * vectorC * Real.sqrt (originalLiftCellConstant parameters grade),
    mul_nonneg (mul_nonneg (abs_nonneg _) vectorC_nonneg) (Real.sqrt_nonneg _), ?_⟩
  intro values
  have liftBound := boundaryLift_norm_le parameters grade gradePositive values
  rw [ofCoreLinear_norm_coordinates] at liftBound
  rw [ofCoreLinear_norm_coordinates]
  unfold collarCorrection
  simp only [LinearMap.comp_apply]
  calc ‖cartesianGradeCoordinates parameters grade (planarInclusionCore parameters
        (seedMatrixCore parameters parameter inside
          (coordinateVector parameters (boundaryLift parameters values))))‖
      ≤ ‖cartesianGradeCoordinates parameters grade (seedMatrixCore parameters parameter inside
          (coordinateVector parameters (boundaryLift parameters values)))‖ :=
        valueMapCore_coordinates_le_one parameters planarInclusionMap planarInclusionMap_norm_le _
    _ ≤ matrixC * ‖cartesianGradeCoordinates parameters grade
          (coordinateVector parameters (boundaryLift parameters values))‖ := by
        rw [seedMatrixCore_eq_full]
        refine (smoothMultiplier_coordinates_bound _ _ _ _).trans ?_
        exact mul_le_mul_of_nonneg_right (le_abs_self _) (norm_nonneg _)
    _ ≤ matrixC * (vectorC * ‖cartesianGradeCoordinates parameters grade
          (boundaryLift parameters values)‖) :=
        mul_le_mul_of_nonneg_left (vectorBound _) (abs_nonneg _)
    _ ≤ matrixC * (vectorC * (Real.sqrt (originalLiftCellConstant parameters grade) *
          ‖boundaryToGrade parameters grade gradePositive values‖)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left liftBound vectorC_nonneg)
          (abs_nonneg _)
    _ = matrixC * vectorC * Real.sqrt (originalLiftCellConstant parameters grade) *
          ‖boundaryToGrade parameters grade gradePositive values‖ := by ring

/-- The outer correction is bounded at every grade `q ≥ 1`. -/
theorem outerCorrection_norm_le (grade : ℕ) (gradePositive : 1 ≤ grade) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ state : ACore parameters 3,
      ‖GradeCore.ofCoreLinear (grade := grade) (outerCorrection parameters parameter inside state)‖ ≤
        constant * ‖GradeCore.ofCoreLinear (grade := grade) state‖ := by
  obtain ⟨rowC, rowC_nonneg, rowBound⟩ := physicalRow_norm_le parameters parameter inside grade
    gradePositive
  obtain ⟨collarC, collarC_nonneg, collarBound⟩ := collarCorrection_norm_le parameters parameter
    inside grade gradePositive
  refine ⟨1 + collarC * rowC, by positivity, ?_⟩
  intro state
  rw [outerCorrection_apply, map_sub]
  calc ‖GradeCore.ofCoreLinear (grade := grade) state -
        GradeCore.ofCoreLinear (grade := grade) (collarCorrection parameters parameter inside
          (physicalRow parameters parameter inside state))‖
      ≤ ‖GradeCore.ofCoreLinear (grade := grade) state‖ +
          ‖GradeCore.ofCoreLinear (grade := grade) (collarCorrection parameters parameter inside
            (physicalRow parameters parameter inside state))‖ := norm_sub_le _ _
    _ ≤ ‖GradeCore.ofCoreLinear (grade := grade) state‖ +
          collarC * (rowC * ‖GradeCore.ofCoreLinear (grade := grade) state‖) :=
        add_le_add le_rfl ((collarBound _).trans
          (mul_le_mul_of_nonneg_left (rowBound state) collarC_nonneg))
    _ = (1 + collarC * rowC) * ‖GradeCore.ofCoreLinear (grade := grade) state‖ := by ring

end Grad.Cor18
