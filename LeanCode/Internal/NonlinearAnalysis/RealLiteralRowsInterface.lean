import RealComplexification

noncomputable section

open Set
open scoped ContDiff

namespace Grad.NonlinearQuotient

open Grad.MainTarget Grad.PhysicalFamily

def complexifyMapping (field : Plane → ℝ → Vec) : Plane → ℝ → ComplexVec :=
  fun point time => complexifyVecCLM (field point time)

def complexifyPotential (field : Plane → ℝ → ℝ) : Plane → ℝ → ℂ :=
  fun point time => Complex.ofRealCLM (field point time)

def actualRealRawRows (cellLength epsilon : ℝ) (mapping : Plane → ℝ → Vec)
    (potential : Plane → ℝ → ℝ) (point : Plane) (time : ℝ) : Fin 4 → ℝ :=
  ![firstCellRow mapping potential point time, secondCellRow mapping potential point time,
    thirdCellRow cellLength epsilon mapping potential point time,
    fourthCellRow cellLength epsilon mapping point time]

/-- The actual-project O15 consumer has the original constrained potential
domain. It does not infer this gauge from an arbitrary CellSolutionFamily. -/
def RealLiteralRowsGoal : Prop :=
  ∀ (cellLength epsilon radius : ℝ) (mapping : Plane → ℝ → Vec)
    (potential : Plane → ℝ → ℝ), 1 < radius →
    ContDiffOn ℝ ∞ (Function.uncurry mapping) (Metric.ball 0 radius ×ˢ univ) →
    ContDiffOn ℝ ∞ (Function.uncurry potential) (Metric.ball 0 radius ×ˢ univ) →
    (∀ point ∈ Metric.ball (0 : Plane) radius, ∀ time, angularAverage potential point time = 0) →
    ∀ point, ‖point‖ ≤ 1 → ∀ time,
      encodeQuotient point
          (quotientFields cellLength epsilon (complexifyMapping mapping)
            (complexifyPotential potential) point time) =
        fun row => (actualRealRawRows cellLength epsilon mapping potential point time row : ℂ)

end Grad.NonlinearQuotient
