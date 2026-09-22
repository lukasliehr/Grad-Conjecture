import RSC11LiteralRestriction

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.SourceCollarRestriction
open Grad.SourceCollarDivision Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.CompatibleCompletion

/-- The smooth-core law retains every actual radial derivative, not only values. -/
theorem completedRestriction_core_ae {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ)
    (field : GradeCore parameters dimension (power + radial)) (index : Fin (radial + 1)) (mode : ℤ × ℤ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      (completedRestriction lower positive bounded parameters power radial (aGradeEta parameters field)).val index mode radius =
        ((annularFrequency mode.1 mode.2 : ℂ) ^ power) • (Real.sqrt radius •
          radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters mode.2 (field.toCore.val mode.2)))
            mode.1 index.val radius) := by
  rw [completedRestriction_core]
  unfold restrictionModeLp
  filter_upwards [Lp.coeFn_smul ((annularFrequency mode.1 mode.2 : ℂ) ^ power)
      (radialToLp lower
        (radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters mode.2 (field.toCore.val mode.2))) mode.1 index.val)
        (radialCoefficientJet_smooth _ (originalPolarValue_smooth _) _ _).continuous),
    radialToLp_ae lower
      (radialCoefficientJet (originalPolarValue (phaseWeightedJet parameters mode.2 (field.toCore.val mode.2))) mode.1 index.val)
      (radialCoefficientJet_smooth _ (originalPolarValue_smooth _) _ _).continuous]
    with radius scaling representative
  rw [scaling, Pi.smul_apply, representative]

theorem continuousPolarValue_completed {dimension grade : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (large : 3 ≤ grade) (field : AGrade parameters dimension grade)
    (cell : ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (angle : ℝ) :
    continuousPolarValue lower positive bounded (completedWeightedCell parameters large cell field) (radius, angle) =
      cartesianWeight parameters cell (polarPlane (radius, angle)) •
        completedOriginalCell parameters large cell field
          (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2) := by
  have pointLaw : annularClosedPoint lower positive bounded (radius, angle) =
      polarClosedPoint radius angle (positive.le.trans inside.1) inside.2 := by
    apply Subtype.ext
    change polarPlane (annularClamp lower radius, angle) = polarPlane (radius, angle)
    rw [annularClamp_eq lower radius inside]
  rw [continuousPolarValue, pointLaw, completedWeightedCell,
    ContinuousLinearMap.comp_apply, originalWeightAction_apply]
  rfl

theorem completedRestriction_literal {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (power radial : ℕ) (large : 3 ≤ power + radial)
    (field : AGrade parameters dimension (power + radial)) (mode : ℤ × ℤ) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1,
      (completedRestriction lower positive bounded parameters power radial field).val 0 mode radius =
        ((annularFrequency mode.1 mode.2 : ℂ) ^ power) • (Real.sqrt radius •
          angularCoefficient (fun angle =>
            cartesianWeight parameters mode.2 (polarPlane (radius, angle)) •
              completedOriginalCell parameters large mode.2 field
                (polarClosedPoint radius angle (positive.le.trans inside.1) inside.2)) mode.1) := by
  change ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1,
    completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters (by omega) field mode radius = _
  rw [completedRestrictionRow_literal lower positive bounded parameters (by omega) large]
  filter_upwards [Lp.coeFn_smul ((annularFrequency mode.1 mode.2 : ℂ) ^ power)
      (continuousPolarLp lower positive bounded mode.1 (completedWeightedCell parameters large mode.2 field)),
    radialToLp_ae lower
      (continuousPolarCoefficient lower positive bounded mode.1 (completedWeightedCell parameters large mode.2 field))
      (continuousPolarCoefficient_continuous lower positive bounded mode.1 (completedWeightedCell parameters large mode.2 field))]
    with radius scaling representative
  intro inside
  change continuousPolarLp lower positive bounded mode.1 (completedWeightedCell parameters large mode.2 field) radius = _ at representative
  rw [scaling, Pi.smul_apply, representative]
  congr 2
  unfold continuousPolarCoefficient
  congr 1
  funext angle
  exact continuousPolarValue_completed lower positive bounded parameters large field mode.2 radius inside angle

/-- All grades use the same original grade-zero L2 restriction, with only
the prescribed nu power inserted. This includes p+k=0,1,2. -/
theorem completedRestrictionRow_zero_reference {dimension grade power : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + 0 ≤ grade)
    (field : AGrade parameters dimension grade) (mode : ℤ × ℤ) :
    completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters paid field mode =
      ((annularFrequency mode.1 mode.2 : ℂ) ^ power) •
        completedRestrictionRow (power := 0) (radial := 0) lower positive bounded parameters le_rfl
          (completedInclusion parameters (Nat.zero_le grade) field) mode := by
  let evaluation := lp.evalCLM ℂ (fun _ : ℤ × ℤ => RadialL2 dimension lower) 2 mode
  let first := evaluation.comp (completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters paid)
  let second := ((annularFrequency mode.1 mode.2 : ℂ) ^ power) •
    ((evaluation.comp (completedRestrictionRow (power := 0) (radial := 0) lower positive bounded parameters le_rfl)).comp
      (completedInclusion parameters (Nat.zero_le grade)))
  have equality : first = second := by
    apply denseCoreContinuousLinearMap_ext parameters
    intro core
    change completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters paid
      (aGradeEta parameters core) mode = ((annularFrequency mode.1 mode.2 : ℂ) ^ power) •
        completedRestrictionRow (power := 0) (radial := 0) lower positive bounded parameters le_rfl
          (completedInclusion parameters (Nat.zero_le grade) (aGradeEta parameters core)) mode
    rw [completedInclusion_apply_eta, completedRestrictionRow_core, completedRestrictionRow_core]
    change restrictionModeLp lower power 0 parameters core.toCore mode =
      ((annularFrequency mode.1 mode.2 : ℂ) ^ power) • restrictionModeLp lower 0 0 parameters core.toCore mode
    simp only [restrictionModeLp, pow_zero, one_smul]
  exact DFunLike.congr_fun equality field

end Grad.SourceCollarRestriction
