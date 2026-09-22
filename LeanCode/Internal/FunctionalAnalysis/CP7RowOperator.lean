import CP6RowFamily

noncomputable section

set_option maxHeartbeats 1600000

open scoped BigOperators

namespace Grad.Cor18

open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.Constraints.Gauges Grad.BoundaryTrace Grad.BoundaryLift

/-- The full membership of the physical-row family at every positive
grade, by the two-shift domination against the accepted trace element. -/
theorem physicalRowFamily_mem (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (state : ACore parameters 3) :
    physicalRowFamily parameters parameter inside state ∈
      boundaryCoreSubmodule parameters 1 := by
  intro grade gradePositive
  rw [memlp_pair_iff_summable_sq]
  set field := rowField parameters parameter inside state with fieldDef
  set weighted : ℤ × ℤ → ℝ := fun mode =>
    boundaryWeight parameters grade mode *
      ‖originalBoundaryCoefficient parameters field mode‖ with weightedDef
  have base : Summable (fun mode : ℤ × ℤ => weighted mode ^ 2) := by
    have member := coreFamily_weighted_memlp parameters field grade gradePositive
    rw [memlp_pair_iff_summable_sq] at member
    apply member.congr
    intro mode
    rw [weightedDef]
    rw [norm_weight_smul]
  have shiftMinus : Summable (fun mode : ℤ × ℤ =>
      weighted (mode.1 - 1, mode.2) ^ 2) :=
    ((Equiv.prodCongr (Equiv.subRight (1 : ℤ)) (Equiv.refl ℤ)).summable_iff
      (f := fun mode : ℤ × ℤ => weighted mode ^ 2)).mpr base
  have shiftPlus : Summable (fun mode : ℤ × ℤ =>
      weighted (mode.1 + 1, mode.2) ^ 2) :=
    ((Equiv.prodCongr (Equiv.addRight (1 : ℤ)) (Equiv.refl ℤ)).summable_iff
      (f := fun mode : ℤ × ℤ => weighted mode ^ 2)).mpr base
  set firstConstant := cellPolynomialWeight 1 ^ grade with firstDef
  set secondConstant := cellPolynomialWeight (-1) ^ grade with secondDef
  have majorant : Summable (fun mode : ℤ × ℤ =>
      2 * firstConstant ^ 2 * weighted (mode.1 - 1, mode.2) ^ 2 +
        2 * secondConstant ^ 2 * weighted (mode.1 + 1, mode.2) ^ 2) :=
    (shiftMinus.mul_left (2 * firstConstant ^ 2)).add
      (shiftPlus.mul_left (2 * secondConstant ^ 2))
  apply Summable.of_nonneg_of_le (fun mode => sq_nonneg _) (fun mode => ?_)
    majorant
  have weightedApply : ∀ pair : ℤ × ℤ,
      boundaryWeight parameters grade pair *
        ‖originalBoundaryCoefficient parameters field pair‖ = weighted pair :=
    fun pair => rfl
  have pointwise := physicalRowFamily_pointwise parameters parameter inside
    state grade mode
  rw [← fieldDef, ← firstDef, ← secondDef, weightedApply,
    weightedApply] at pointwise
  have weightedNonneg : ∀ pair : ℤ × ℤ, 0 ≤ weighted pair := by
    intro pair
    rw [weightedDef]
    exact mul_nonneg (boundaryWeight_pos parameters grade pair).le (norm_nonneg _)
  have squared : ‖(boundaryWeight parameters grade mode : ℂ) •
      physicalRowFamily parameters parameter inside state mode‖ ^ 2 ≤
      (firstConstant * weighted (mode.1 - 1, mode.2) +
        secondConstant * weighted (mode.1 + 1, mode.2)) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) pointwise 2
  apply squared.trans
  nlinarith [sq_nonneg (firstConstant * weighted (mode.1 - 1, mode.2) -
    secondConstant * weighted (mode.1 + 1, mode.2))]

/-- The physical row lands on high angular modes only. -/
theorem physicalRowFamily_high (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (state : ACore parameters 3) (mode : ℤ × ℤ) (low : |mode.1| ≤ 2) :
    physicalRowFamily parameters parameter inside state mode = 0 := by
  unfold physicalRowFamily
  rw [if_pos low]

/-- Pointwise additivity of the radial contraction in the state. -/
theorem rowFunction_add (parameters : PhaseParameters)
    (first second : ACore parameters 2) (cell : ℤ) :
    rowFunction parameters (first + second) cell = fun angle =>
      rowFunction parameters first cell angle +
        rowFunction parameters second cell angle := by
  funext angle
  unfold rowFunction
  rw [Submodule.coe_add, Pi.add_apply, closedJet_value_add,
    ContinuousMap.add_apply]
  have componentZero : ((first.1 cell).value (boundaryDiskPoint angle) +
      (second.1 cell).value (boundaryDiskPoint angle)) 0 =
      ((first.1 cell).value (boundaryDiskPoint angle)) 0 +
        ((second.1 cell).value (boundaryDiskPoint angle)) 0 := rfl
  have componentOne : ((first.1 cell).value (boundaryDiskPoint angle) +
      (second.1 cell).value (boundaryDiskPoint angle)) 1 =
      ((first.1 cell).value (boundaryDiskPoint angle)) 1 +
        ((second.1 cell).value (boundaryDiskPoint angle)) 1 := rfl
  rw [componentZero, componentOne]
  ring

/-- Pointwise homogeneity of the radial contraction in the state. -/
theorem rowFunction_smul (parameters : PhaseParameters) (scalar : ℂ)
    (field : ACore parameters 2) (cell : ℤ) :
    rowFunction parameters (scalar • field) cell = fun angle =>
      scalar * rowFunction parameters field cell angle := by
  funext angle
  unfold rowFunction
  rw [Submodule.coe_smul, Pi.smul_apply, closedJet_value_smul,
    ContinuousMap.smul_apply]
  have componentZero : (scalar • (field.1 cell).value (boundaryDiskPoint angle)) 0 =
      scalar * ((field.1 cell).value (boundaryDiskPoint angle)) 0 := rfl
  have componentOne : (scalar • (field.1 cell).value (boundaryDiskPoint angle)) 1 =
      scalar * ((field.1 cell).value (boundaryDiskPoint angle)) 1 := rfl
  rw [componentZero, componentOne]
  ring

/-- Family additivity in the state. -/
theorem physicalRowFamily_add (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (first second : ACore parameters 3) :
    physicalRowFamily parameters parameter inside (first + second) =
      physicalRowFamily parameters parameter inside first +
        physicalRowFamily parameters parameter inside second := by
  funext mode
  rw [Pi.add_apply]
  unfold physicalRowFamily
  by_cases low : |mode.1| ≤ 2
  · rw [if_pos low, if_pos low, if_pos low, add_zero]
  · rw [if_neg low, if_neg low, if_neg low,
      map_add (rowField parameters parameter inside), rowFunction_add,
      fourierCoeff_add_continuous _ _ mode.1
        (rowFunction_continuous parameters _ mode.2)
        (rowFunction_continuous parameters _ mode.2)]
    apply PiLp.ext
    intro index
    fin_cases index
    simp

/-- Family homogeneity in the state. -/
theorem physicalRowFamily_smul (parameters : PhaseParameters)
    (parameter : Seed.Parameters) (inside : parameter ∈ Seed.parameterDomain)
    (scalar : ℂ) (state : ACore parameters 3) :
    physicalRowFamily parameters parameter inside (scalar • state) =
      scalar • physicalRowFamily parameters parameter inside state := by
  funext mode
  rw [Pi.smul_apply]
  unfold physicalRowFamily
  by_cases low : |mode.1| ≤ 2
  · rw [if_pos low, if_pos low, smul_zero]
  · rw [if_neg low, if_neg low,
      map_smul (rowField parameters parameter inside), rowFunction_smul,
      fourierCoeff_const_mul]
    apply PiLp.ext
    intro index
    fin_cases index
    simp

/-- The N29 physical row as one linear operator into the boundary core. -/
def physicalRow (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) :
    ACore parameters 3 →ₗ[ℂ] BoundaryCore parameters 1 where
  toFun state := ⟨physicalRowFamily parameters parameter inside state,
    physicalRowFamily_mem parameters parameter inside state⟩
  map_add' first second := by
    apply Subtype.ext
    exact physicalRowFamily_add parameters parameter inside first second
  map_smul' scalar state := by
    apply Subtype.ext
    exact physicalRowFamily_smul parameters parameter inside scalar state

end Grad.Cor18
