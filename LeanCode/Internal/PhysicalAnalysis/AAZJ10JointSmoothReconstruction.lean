import AAZJ9JointFrechetDerivative
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularJointRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace Grad.PhaseAlgebra Grad.AnnularGrades
open Grad.GaugeCoefficients.Physical.WeightedTrace Grad.AnnularRadialJets Grad.AnnularRegularity

/-- The original collar interior times both actual Fourier coordinates. -/
def annularJointInterior (lower : ℝ) : Set (ℝ × (ℝ × ℝ)) :=
  {point | point.1 ∈ Ioo lower 1}

theorem annularJointInterior_open (lower : ℝ) : IsOpen (annularJointInterior lower) :=
  isOpen_Ioo.preimage continuous_fst

section SmoothReconstruction
variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (jet : ℕ → AnnularRawFamily lower)
    (weak : ∀ order, AnnularPhysicalWeakDerivative parameters lower positive (jet order) (jet (order + 1)))
    (grades : ∀ order grade, HasAnnularRawGrade lower grade (jet order))
include grades

/-- Finite-order induction uses the three next actual mixed derivatives.
No joint smoothness or bounds without the original phase are assumed. -/
theorem annularMixedFourierField_contDiffOn (order radial angular cell : ℕ) :
    ContDiffOn ℝ order
      (annularMixedFourierField parameters lower positive bounded jet weak radial angular cell)
      (annularJointInterior lower) := by
  induction order generalizing radial angular cell with
  | zero =>
      exact contDiffOn_zero.mpr
        (annularMixedFourierField_continuous parameters lower positive bounded jet weak grades radial angular cell).continuousOn
  | succ order previous =>
      have unique := (annularJointInterior_open lower).uniqueDiffOn (𝕜 := ℝ)
      rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_fderiv_apply unique]
      refine ⟨fun point inside =>
        (annularMixedFourierField_hasFDerivAt parameters lower positive bounded jet weak grades radial angular cell point inside).differentiableAt.differentiableWithinAt,
        by simp, fun direction => ?_⟩
      have smooth : ContDiffOn ℝ order (fun point =>
          direction.1 • annularMixedFourierField parameters lower positive bounded jet weak (radial + 1) angular cell point +
          (direction.2.1 • annularMixedFourierField parameters lower positive bounded jet weak radial (angular + 1) cell point +
           direction.2.2 • annularMixedFourierField parameters lower positive bounded jet weak radial angular (cell + 1) point))
          (annularJointInterior lower) :=
        ((previous (radial + 1) angular cell).const_smul direction.1).add
          (((previous radial (angular + 1) cell).const_smul direction.2.1).add
            ((previous radial angular (cell + 1)).const_smul direction.2.2))
      apply smooth.congr
      intro point inside
      rw [(annularMixedFourierField_hasFDerivAt parameters lower positive bounded jet weak grades radial angular cell point inside).hasFDerivWithinAt.fderivWithin
        (unique point inside)]
      rfl

/-- Joint smoothness of every formally mixed physical Fourier field. Together
with the closed-product continuity and exact endpoint derivative laws, this
is the actual smooth closed-collar reconstruction. -/
theorem annularMixedFourierField_smooth (radial angular cell : ℕ) :
    ContDiffOn ℝ ∞
      (annularMixedFourierField parameters lower positive bounded jet weak radial angular cell)
      (annularJointInterior lower) :=
  contDiffOn_infty.mpr (fun order => annularMixedFourierField_contDiffOn parameters lower positive bounded jet weak grades order radial angular cell)

end SmoothReconstruction
end Grad.AnnularJointRegularity
