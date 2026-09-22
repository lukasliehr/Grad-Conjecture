import SCD24ContinuousRadialL2

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal

namespace Grad.SourceCollarDivision

open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace

theorem continuousDifferenceQuotient_jet {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (field : ClosedJet dimension)
    (radius : ℝ) (inside : radius ∈ Icc lower 1) (angle : ℝ) :
    continuousDifferenceQuotient lower positive bounded field.value (radius, angle) =
      dividedPolarValue field (radius, angle) := by
  have radiusPositive := positive.trans_le inside.1
  have pointLaw : annularClosedPoint lower positive bounded (radius, angle) =
      polarClosedPoint radius angle radiusPositive.le inside.2 := by
    apply Subtype.ext
    change polarPlane (annularClamp lower radius, angle) = polarPlane (radius, angle)
    rw [annularClamp_eq lower radius inside]
  rw [continuousDifferenceQuotient, annularClamp_eq lower radius inside, pointLaw,
    ← dividedPolarValue_multiply field radius angle radiusPositive.le inside.2,
    smul_smul, inv_mul_cancel₀ radiusPositive.ne', one_smul]

theorem continuousDifferenceCoefficient_jet {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (field : ClosedJet dimension)
    (mode : ℤ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    continuousDifferenceCoefficient lower positive bounded mode field.value radius =
      radialCoefficientJet (dividedPolarValue field) mode 0 radius := by
  unfold continuousDifferenceCoefficient radialCoefficientJet
  congr 1
  funext angle
  exact continuousDifferenceQuotient_jet lower positive bounded field radius inside angle

theorem continuousDifferenceLp_jet {dimension : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (field : ClosedJet dimension) (mode : ℤ) :
    continuousDifferenceLp lower positive bounded mode field.value =
      radialToLp lower (radialCoefficientJet (dividedPolarValue field) mode 0)
        (radialCoefficientJet_smooth _ (dividedPolarValue_smooth _) _ _).continuous := by
  apply Lp.ext
  filter_upwards [radialToLp_ae lower
    (continuousDifferenceCoefficient lower positive bounded mode field.value)
    (continuousDifferenceCoefficient_continuous lower positive bounded mode field.value),
    radialToLp_ae lower (radialCoefficientJet (dividedPolarValue field) mode 0)
      (radialCoefficientJet_smooth _ (dividedPolarValue_smooth _) _ _).continuous,
    ae_restrict_mem measurableSet_Icc] with radius first second inside
  change continuousDifferenceLp lower positive bounded mode field.value radius =
    Real.sqrt radius • continuousDifferenceCoefficient lower positive bounded mode field.value radius at first
  rw [first, second, continuousDifferenceCoefficient_jet lower positive bounded field mode radius inside]

/-- The zeroth completed graph coordinate is the literal angular coefficient
of the Hadamard difference quotient of the actual completed weighted field.
The comparison uses a bounded map on each fixed positive annulus; the final
uniform estimate is the independently proved paid-grade estimate. -/
theorem completedDivisionRow_literal {dimension grade power : ℕ}
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (parameters : PhaseParameters) (paid : power + 0 + 3 ≤ grade)
    (field : AGrade parameters dimension grade) (mode : ℤ × ℤ) :
    completedDivisionRow (power := power) (radial := 0) lower positive bounded parameters paid field mode =
      ((annularFrequency mode.1 mode.2 : ℂ) ^ power) •
        continuousDifferenceLp lower positive bounded mode.1
          (completedWeightedCell parameters (by omega) mode.2 field) := by
  let first : AGrade parameters dimension grade →L[ℂ] RadialL2 dimension lower :=
    (lp.evalCLM ℂ (fun _ : ℤ × ℤ => RadialL2 dimension lower) 2 mode).comp
      (completedDivisionRow (power := power) (radial := 0) lower positive bounded parameters paid)
  let second : AGrade parameters dimension grade →L[ℂ] RadialL2 dimension lower :=
    ((annularFrequency mode.1 mode.2 : ℂ) ^ power) •
      ((continuousDifferenceLp lower positive bounded mode.1).comp
        (completedWeightedCell parameters (by omega) mode.2))
  have equality : first = second := by
    apply denseCoreContinuousLinearMap_ext parameters
    intro core
    change completedDivisionRow (power := power) (radial := 0) lower positive bounded parameters paid (aGradeEta parameters core) mode =
      ((annularFrequency mode.1 mode.2 : ℂ) ^ power) •
        continuousDifferenceLp lower positive bounded mode.1
          (completedWeightedCell parameters (by omega) mode.2 (aGradeEta parameters core))
    rw [completedDivisionRow_core, completedWeightedCell_core, continuousDifferenceLp_jet]
    rfl
  exact DFunLike.congr_fun equality field

end Grad.SourceCollarDivision
