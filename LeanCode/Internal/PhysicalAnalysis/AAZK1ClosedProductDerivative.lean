import AAZJ15SameSolutionJointSmoothConsumer
import Mathlib.Analysis.Calculus.FDeriv.Extend

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularClosedJointRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularRadialJets Grad.AnnularJointRegularity

/-- The literal closed radial product domain in the original real coordinates. -/
def annularJointClosed (lower : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  Icc lower 1 ×ˢ (univ : Set (ℝ × ℝ))

theorem annularJointInterior_product (lower : ℝ) :
    annularJointInterior lower = Ioo lower 1 ×ˢ (univ : Set (ℝ × ℝ)) := by
  ext point
  simp only [annularJointInterior, mem_ofPred_eq, mem_prod, mem_univ, and_true]

theorem annularJointInterior_closure (lower : ℝ) (bounded : lower < 1) :
    closure (annularJointInterior lower) = annularJointClosed lower := by
  rw [annularJointInterior_product]
  rw [closure_prod_eq, closure_Ioo bounded.ne, closure_univ]
  rfl

theorem annularJointInterior_convex (lower : ℝ) : Convex ℝ (annularJointInterior lower) := by
  rw [annularJointInterior_product]
  exact (convex_Ioo lower 1).prod convex_univ

theorem annularJointClosed_unique (lower : ℝ) (bounded : lower < 1) :
    UniqueDiffOn ℝ (annularJointClosed lower) :=
  (uniqueDiffOn_Icc bounded).prod uniqueDiffOn_univ

section ClosedDerivative
variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (jet : ℕ → AnnularRawFamily lower)
    (weak : ∀ order, AnnularPhysicalWeakDerivative parameters lower positive (jet order) (jet (order + 1)))

def annularMixedPhysicalGradient (radial angular cell : ℕ) (point : ℝ × (ℝ × ℝ)) :
    (ℝ × (ℝ × ℝ)) →L[ℝ] ComplexEuclidean 1 :=
  (ContinuousLinearMap.toSpanSingleton ℝ
    (annularMixedFourierField parameters lower positive bounded jet weak (radial + 1) angular cell point)).coprod
    ((ContinuousLinearMap.toSpanSingleton ℝ
      (annularMixedFourierField parameters lower positive bounded jet weak radial (angular + 1) cell point)).coprod
      (ContinuousLinearMap.toSpanSingleton ℝ
        (annularMixedFourierField parameters lower positive bounded jet weak radial angular (cell + 1) point)))

variable (grades : ∀ order grade, HasAnnularRawGrade lower grade (jet order))
include grades

theorem annularMixedPhysicalGradient_continuous (radial angular cell : ℕ) :
    Continuous (annularMixedPhysicalGradient parameters lower positive bounded jet weak radial angular cell) := by
  unfold annularMixedPhysicalGradient
  exact ((ContinuousLinearMap.toSpanSingletonLIE ℝ (ComplexEuclidean 1)).continuous.comp
      (annularMixedFourierField_continuous parameters lower positive bounded jet weak grades (radial + 1) angular cell)).continuousLinearMapCoprod
    (((ContinuousLinearMap.toSpanSingletonLIE ℝ (ComplexEuclidean 1)).continuous.comp
      (annularMixedFourierField_continuous parameters lower positive bounded jet weak grades radial (angular + 1) cell)).continuousLinearMapCoprod
      ((ContinuousLinearMap.toSpanSingletonLIE ℝ (ComplexEuclidean 1)).continuous.comp
      (annularMixedFourierField_continuous parameters lower positive bounded jet weak grades radial angular (cell + 1))))

/-- Continuous limits of the actual interior derivative give the literal
Fréchet derivative within the full closed product, including its endpoints. -/
theorem annularMixedFourierField_hasFDerivWithinAt_closed (radial angular cell : ℕ)
    (point : ℝ × (ℝ × ℝ)) :
    HasFDerivWithinAt (annularMixedFourierField parameters lower positive bounded jet weak radial angular cell)
      (annularMixedPhysicalGradient parameters lower positive bounded jet weak radial angular cell point)
      (annularJointClosed lower) point := by
  rw [← annularJointInterior_closure lower bounded]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun point inside => (annularMixedFourierField_hasFDerivAt parameters lower positive bounded jet weak grades radial angular cell point inside).differentiableAt.differentiableWithinAt)
    (annularJointInterior_convex lower) (annularJointInterior_open lower)
    (fun point _ => (annularMixedFourierField_continuous parameters lower positive bounded jet weak grades radial angular cell).continuousAt.continuousWithinAt)
  have equality : fderiv ℝ (annularMixedFourierField parameters lower positive bounded jet weak radial angular cell) =ᶠ[𝓝[annularJointInterior lower] point]
      annularMixedPhysicalGradient parameters lower positive bounded jet weak radial angular cell := by
    filter_upwards [self_mem_nhdsWithin] with nearby inside
    exact (annularMixedFourierField_hasFDerivAt parameters lower positive bounded jet weak grades radial angular cell nearby inside).fderiv
  exact (tendsto_congr' equality).mpr
    (annularMixedPhysicalGradient_continuous parameters lower positive bounded jet weak grades radial angular cell).continuousAt.continuousWithinAt.tendsto

end ClosedDerivative
end Grad.AnnularClosedJointRegularity
