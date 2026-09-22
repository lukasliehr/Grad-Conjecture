import RSC10ContinuousPolar

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarRestriction

open Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

theorem continuousPolarValue_jet {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (field : ClosedJet dimension)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angle : ℝ) :
    continuousPolarValue lower positive bounded field.value (radius, angle) =
      originalPolarValue field (radius, angle) := by
  have radiusPositive := positive.trans_le inside.1
  have pointLaw : annularClosedPoint lower positive bounded (radius, angle) =
      polarClosedPoint radius angle radiusPositive.le inside.2 := by
    apply Subtype.ext
    change polarPlane (annularClamp lower radius, angle) = polarPlane (radius, angle)
    rw [annularClamp_eq lower radius inside]
  rw [continuousPolarValue, pointLaw, originalPolarValue_closed field radius angle radiusPositive.le inside.2]

theorem continuousPolarCoefficient_jet {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (field : ClosedJet dimension)
    (mode : ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    continuousPolarCoefficient lower positive bounded mode field.value radius =
      radialCoefficientJet (originalPolarValue field) mode 0 radius := by
  unfold continuousPolarCoefficient radialCoefficientJet
  congr 1
  funext angle
  exact continuousPolarValue_jet lower positive bounded field radius inside angle

theorem continuousPolarLp_jet {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (field : ClosedJet dimension) (mode : ℤ) :
    continuousPolarLp lower positive bounded mode field.value =
      radialToLp lower (radialCoefficientJet (originalPolarValue field) mode 0)
        (radialCoefficientJet_smooth _ (originalPolarValue_smooth _) _ _).continuous := by
  apply Lp.ext
  filter_upwards [radialToLp_ae lower
    (continuousPolarCoefficient lower positive bounded mode field.value)
    (continuousPolarCoefficient_continuous lower positive bounded mode field.value),
    radialToLp_ae lower (radialCoefficientJet (originalPolarValue field) mode 0)
      (radialCoefficientJet_smooth _ (originalPolarValue_smooth _) _ _).continuous,
    ae_restrict_mem measurableSet_Icc] with radius first second inside
  change continuousPolarLp lower positive bounded mode field.value radius =
    Real.sqrt radius • continuousPolarCoefficient lower positive bounded mode field.value radius at first
  rw [first, second, continuousPolarCoefficient_jet lower positive bounded field mode radius inside]

/-- On grades admitting actual continuous cell values, the canonical completed
restriction equals their literal weighted polar Fourier restriction. -/
theorem completedRestrictionRow_literal {dimension grade power : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + 0 ≤ grade) (large : 3 ≤ grade)
    (field : AGrade parameters dimension grade) (mode : ℤ × ℤ) :
    completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters paid field mode =
      ((annularFrequency mode.1 mode.2 : ℂ) ^ power) •
        continuousPolarLp lower positive bounded mode.1
          (completedWeightedCell parameters large mode.2 field) := by
  let first : AGrade parameters dimension grade →L[ℂ] RadialL2 dimension lower :=
    (lp.evalCLM ℂ (fun _ : ℤ × ℤ => RadialL2 dimension lower) 2 mode).comp
      (completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters paid)
  let second : AGrade parameters dimension grade →L[ℂ] RadialL2 dimension lower :=
    ((annularFrequency mode.1 mode.2 : ℂ) ^ power) •
      ((continuousPolarLp lower positive bounded mode.1).comp
        (completedWeightedCell parameters large mode.2))
  have equality : first = second := by
    apply denseCoreContinuousLinearMap_ext parameters
    intro core
    change completedRestrictionRow (power := power) (radial := 0) lower positive bounded parameters paid (aGradeEta parameters core) mode =
      ((annularFrequency mode.1 mode.2 : ℂ) ^ power) •
        continuousPolarLp lower positive bounded mode.1
          (completedWeightedCell parameters large mode.2 (aGradeEta parameters core))
    rw [completedRestrictionRow_core, completedWeightedCell_core, continuousPolarLp_jet]
    rfl
  exact DFunLike.congr_fun equality field

end Grad.SourceCollarRestriction
