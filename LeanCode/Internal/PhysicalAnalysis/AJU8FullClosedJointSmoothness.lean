import AJU7FullJointPhysicalDerivative
import AAZK1ClosedProductDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval ENNReal BigOperators
namespace Grad.AnnularPhysicalFourier
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularSourceGraph Grad.AnnularJointRegularity Grad.AnnularRegularity
open Grad.AnnularClosedJointRegularity

section ClosedDerivative
variable (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (jet : PhysicalFourierJet lower positive bounded)

def physicalMixedGradient (radial angular cell : ℕ) (point : ℝ × (ℝ × ℝ)) :
    (ℝ × (ℝ × ℝ)) →L[ℝ] ComplexEuclidean 1 :=
  (ContinuousLinearMap.toSpanSingleton ℝ
    (physicalMixedFourierField lower positive bounded jet (radial + 1) angular cell point)).coprod
    ((ContinuousLinearMap.toSpanSingleton ℝ
      (physicalMixedFourierField lower positive bounded jet radial (angular + 1) cell point)).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ
        (physicalMixedFourierField lower positive bounded jet radial angular (cell + 1) point)))


theorem physicalMixedGradient_continuous (radial angular cell : ℕ) :
    Continuous (physicalMixedGradient lower positive bounded jet radial angular cell) := by
  unfold physicalMixedGradient
  exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ (ComplexEuclidean 1)).continuous.comp
      (physicalMixedFourierField_continuous lower positive bounded jet (radial + 1) angular cell)).continuousLinearMapCoprod
    (((ContinuousLinearMap.toSpanSingletonLIE ℝ (ComplexEuclidean 1)).continuous.comp
      (physicalMixedFourierField_continuous lower positive bounded jet radial (angular + 1) cell)).continuousLinearMapCoprod
      ((ContinuousLinearMap.toSpanSingletonLIE ℝ (ComplexEuclidean 1)).continuous.comp
      (physicalMixedFourierField_continuous lower positive bounded jet radial angular (cell + 1))))

/-- Continuous limits of the actual interior derivative give the literal
Fréchet derivative within the full closed product, including its endpoints. -/
theorem physicalMixedFourierField_hasFDerivWithinAt_closed (radial angular cell : ℕ)
    (point : ℝ × (ℝ × ℝ)) :
    HasFDerivWithinAt (physicalMixedFourierField lower positive bounded jet radial angular cell)
      (physicalMixedGradient lower positive bounded jet radial angular cell point)
      (annularJointClosed lower) point := by
  rw [← annularJointInterior_closure lower bounded]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun point inside => (physicalMixedFourierField_hasFDerivAt lower positive bounded jet radial angular cell point inside).differentiableAt.differentiableWithinAt)
    (annularJointInterior_convex lower) (annularJointInterior_open lower)
    (fun point _ => (physicalMixedFourierField_continuous lower positive bounded jet radial angular cell).continuousAt.continuousWithinAt)
  have equality : fderiv ℝ (physicalMixedFourierField lower positive bounded jet radial angular cell) =ᶠ[𝓝[annularJointInterior lower] point]
      physicalMixedGradient lower positive bounded jet radial angular cell := by
    filter_upwards [self_mem_nhdsWithin] with nearby inside
    exact (physicalMixedFourierField_hasFDerivAt lower positive bounded jet radial angular cell nearby inside).fderiv
  exact (tendsto_congr' equality).mpr
    (physicalMixedGradient_continuous lower positive bounded jet radial angular cell).continuousAt.continuousWithinAt.tendsto

end ClosedDerivative


section SmoothReconstruction
variable (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (jet : PhysicalFourierJet lower positive bounded)

/-- Finite-order induction uses the three next actual mixed derivatives.
No joint smoothness or bounds without the original phase are assumed. -/
theorem physicalMixedFourierField_contDiffOn_closed (order radial angular cell : ℕ) :
    ContDiffOn ℝ order
      (physicalMixedFourierField lower positive bounded jet radial angular cell)
      (annularJointClosed lower) := by
  induction order generalizing radial angular cell with
  | zero =>
      exact contDiffOn_zero.mpr
        (physicalMixedFourierField_continuous lower positive bounded jet radial angular cell).continuousOn
  | succ order previous =>
      have unique := annularJointClosed_unique lower bounded
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_apply unique]
      refine ⟨fun point _ =>
        (physicalMixedFourierField_hasFDerivWithinAt_closed lower positive bounded jet radial angular cell point).differentiableWithinAt,
        by simp, fun direction => ?_⟩
      have smooth : ContDiffOn ℝ order (fun point =>
          direction.1 • physicalMixedFourierField lower positive bounded jet (radial + 1) angular cell point +
          (direction.2.1 • physicalMixedFourierField lower positive bounded jet radial (angular + 1) cell point +
           direction.2.2 • physicalMixedFourierField lower positive bounded jet radial angular (cell + 1) point))
          (annularJointClosed lower) :=
        ((previous (radial + 1) angular cell).const_smul direction.1).add
          (((previous radial (angular + 1) cell).const_smul direction.2.1).add
            ((previous radial angular (cell + 1)).const_smul direction.2.2))
      apply smooth.congr
      intro point inside
      rw [(physicalMixedFourierField_hasFDerivWithinAt_closed lower positive bounded jet radial angular cell point).fderivWithin
        (unique point inside)]
      rfl

/-- Joint smoothness of every formally mixed physical Fourier field. on the literal CLOSED product domain. This theorem asserts within-domain
smoothness, including both endpoints, and makes no ambient smoothness claim. -/
theorem physicalMixedFourierField_smooth_closed (radial angular cell : ℕ) :
    ContDiffOn ℝ ∞
      (physicalMixedFourierField lower positive bounded jet radial angular cell)
      (annularJointClosed lower) :=
  contDiffOn_infty.mpr (fun order => physicalMixedFourierField_contDiffOn_closed lower positive bounded jet order radial angular cell)

end SmoothReconstruction
end Grad.AnnularPhysicalFourier
