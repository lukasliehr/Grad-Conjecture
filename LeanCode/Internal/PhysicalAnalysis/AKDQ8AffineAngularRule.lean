import AKDQ7FirstIntegratedForce
import RealComplexification

noncomputable section
set_option maxHeartbeats 1000000
open Set
open scoped ContDiff

namespace Grad.PhysicalEquilibrium
open Grad.MainTarget Grad.PhysicalFamily Grad.NonlinearQuotient

def tangentGeneratorCLM : Vec →L[ℝ] Vec where
  toFun := tangentGenerator
  map_add' first second := by
    ext coordinate
    fin_cases coordinate <;> simp [tangentGenerator, vector]
    ring
  map_smul' scalar point := by
    ext coordinate
    fin_cases coordinate <;> simp [tangentGenerator, vector]
  cont := by
    have smooth : ContDiff ℝ ∞ tangentGenerator := by
      rw [contDiff_piLp]
      intro coordinate
      fin_cases coordinate <;> simp [tangentGenerator, vector] <;> fun_prop
    exact smooth.continuous

theorem inner_tangentGenerator_self (point : Vec) :
    inner ℝ point (tangentGenerator point) = 0 := by
  simp [PiLp.inner_apply, Fin.sum_univ_three, tangentGenerator, vector]
  ring

theorem affineStateDerivative_joint_smooth (length epsilon : ℝ)
    {mapping : Plane → ℝ → Vec} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry mapping) (Metric.ball 0 radius ×ˢ univ)) :
    ContDiffOn ℝ ∞ (Function.uncurry (affineStateDerivative length epsilon mapping))
      (Metric.ball 0 radius ×ˢ univ) :=
  ((cellDerivative_joint_smooth smooth).add
    ((tangentGeneratorCLM.contDiff.comp_contDiffOn smooth).const_smul epsilon)).add contDiffOn_const

/-- The affine constant contributes zero to the angular derivative;
the rotation term is the actual skew ambient generator. -/
theorem diskAngular_affineStateDerivative (length epsilon : ℝ)
    {mapping : Plane → ℝ → Vec} {radius : ℝ}
    (smooth : ContDiffOn ℝ ∞ (Function.uncurry mapping) (Metric.ball 0 radius ×ˢ univ))
    (point : Plane) (pointIn : point ∈ Metric.ball (0 : Plane) radius) (time : ℝ) :
    diskAngular (affineStateDerivative length epsilon mapping) point time =
      cellDerivative (diskAngular mapping) point time +
        epsilon • tangentGenerator (diskAngular mapping point time) := by
  have mappingDiff := smooth_spatial_differentiable smooth point pointIn time
  have timeDiff := smooth_spatial_differentiable (cellDerivative_joint_smooth smooth) point pointIn time
  have generatorDerivative := tangentGeneratorCLM.hasFDerivAt.comp point mappingDiff.hasFDerivAt
  have derivative := (timeDiff.hasFDerivAt.add (generatorDerivative.const_smul epsilon)).add
    (hasFDerivAt_const (length • tangentDirection) point)
  have value := congrArg (fun linear : Plane →L[ℝ] Vec => linear (planeQuarterTurn point)) derivative.fderiv
  change diskAngular (affineStateDerivative length epsilon mapping) point time =
    diskAngular (cellDerivative mapping) point time +
      epsilon • tangentGenerator (diskAngular mapping point time) + 0 at value
  rw [add_zero, diskAngular_cellDerivative smooth point pointIn time] at value
  exact value

end Grad.PhysicalEquilibrium
