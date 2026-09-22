import AIC5LiteralLocalization

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators

namespace Grad.InteriorLocalization
open Grad.PDEBootstrap Grad.WeightedJets Grad.WeightedJets.SpatialMultiplier

/-- The two literal Cartesian first-derivative indices. -/
def firstTestIndex (direction : Fin 2) : JetIndex 1 :=
  if direction = 0 then ⟨(1, 0), by decide⟩ else ⟨(0, 1), by decide⟩

def secondTestIndex (direction : Fin 2) : JetIndex 2 :=
  if direction = 0 then ⟨(2, 0), by decide⟩ else ⟨(0, 2), by decide⟩

def firstTestDerivative (direction : Fin 2) (test : Spatial → ℝ) : Spatial → ℝ :=
  scalarDerivative (firstTestIndex direction).val test

def secondTestDerivative (direction : Fin 2) (test : Spatial → ℝ) : Spatial → ℝ :=
  scalarDerivative (secondTestIndex direction).val test

theorem firstTestDerivative_smooth (direction : Fin 2) (test : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) : ContDiff ℝ ∞ (firstTestDerivative direction test) :=
  scalarDerivative_smooth _ test smooth

theorem secondTestDerivative_smooth (direction : Fin 2) (test : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) : ContDiff ℝ ∞ (secondTestDerivative direction test) :=
  scalarDerivative_smooth _ test smooth

theorem firstTestDerivative_compact (direction : Fin 2) (test : Spatial → ℝ)
    (compact : HasCompactSupport test) : HasCompactSupport (firstTestDerivative direction test) :=
  Grad.WeakTesting.orderedTestDerivative_hasCompactSupport _ _ test compact

theorem secondTestDerivative_compact (direction : Fin 2) (test : Spatial → ℝ)
    (compact : HasCompactSupport test) : HasCompactSupport (secondTestDerivative direction test) :=
  Grad.WeakTesting.orderedTestDerivative_hasCompactSupport _ _ test compact

theorem firstTestDerivative_repeat (direction : Fin 2) (test : Spatial → ℝ)
    (smooth : ContDiff ℝ ∞ test) :
    firstTestDerivative direction (firstTestDerivative direction test) = secondTestDerivative direction test := by
  unfold firstTestDerivative secondTestDerivative
  rw [scalarDerivative_comp _ _ test smooth]
  fin_cases direction <;> rfl

theorem firstTestDerivative_mul (direction : Fin 2) (first second : Spatial → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second) (point : Spatial) :
    firstTestDerivative direction (fun point => first point * second point) point =
      firstTestDerivative direction first point * second point +
        first point * firstTestDerivative direction second point := by
  fin_cases direction
  · have formula := congrFun (scalarDerivative_mul_rectangle 1 0 first second firstSmooth secondSmooth) point
    norm_num [Finset.sum_range_succ, scalarDerivative_zero] at formula
    exact formula
  · have formula := congrFun (scalarDerivative_mul_rectangle 0 1 first second firstSmooth secondSmooth) point
    norm_num [Finset.sum_range_succ, scalarDerivative_zero] at formula
    exact formula

theorem secondTestDerivative_mul (direction : Fin 2) (first second : Spatial → ℝ)
    (firstSmooth : ContDiff ℝ ∞ first) (secondSmooth : ContDiff ℝ ∞ second) (point : Spatial) :
    secondTestDerivative direction (fun point => first point * second point) point =
      secondTestDerivative direction first point * second point +
        2 * firstTestDerivative direction first point * firstTestDerivative direction second point +
        first point * secondTestDerivative direction second point := by
  fin_cases direction
  · have formula := congrFun (scalarDerivative_mul_rectangle 2 0 first second firstSmooth secondSmooth) point
    norm_num [Finset.sum_range_succ, scalarDerivative_zero] at formula
    exact formula
  · have formula := congrFun (scalarDerivative_mul_rectangle 0 2 first second firstSmooth secondSmooth) point
    norm_num [Finset.sum_range_succ, scalarDerivative_zero] at formula
    exact formula

/-- The adjoint product identity used on a merely H1 field. Individual
second derivatives of that field are never assumed. -/
theorem cutoff_test_identity (direction : Fin 2) (cutoff test : Spatial → ℝ)
    (cutoffSmooth : ContDiff ℝ ∞ cutoff) (testSmooth : ContDiff ℝ ∞ test) (point : Spatial) :
    secondTestDerivative direction (fun point => cutoff point * test point) point -
        2 * firstTestDerivative direction (fun point => firstTestDerivative direction cutoff point * test point) point +
        secondTestDerivative direction cutoff point * test point =
      cutoff point * secondTestDerivative direction test point := by
  rw [secondTestDerivative_mul direction cutoff test cutoffSmooth testSmooth,
    firstTestDerivative_mul direction (firstTestDerivative direction cutoff) test
      (firstTestDerivative_smooth direction cutoff cutoffSmooth) testSmooth,
    firstTestDerivative_repeat direction cutoff cutoffSmooth]
  ring

end Grad.InteriorLocalization
