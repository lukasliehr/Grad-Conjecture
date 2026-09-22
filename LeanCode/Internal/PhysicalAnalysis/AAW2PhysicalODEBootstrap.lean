import AAW1WeakEndpointDifferentiation
import AAR19PhysicalSecondRow

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators ENNReal
namespace Grad.AnnularRegularity
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularVariational Grad.AnnularSourceGraph Grad.CircularHighWeak Grad.AnnularReconstruction
open Grad.CircularHighRegularity Grad.AnnularFluxTrace
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- One actual derivative gains one closed-collar order. -/
theorem annular_closedCollar_succ (lower : ℝ) (bounded : lower < 1) (order : ℕ)
    (field derivative : ℝ → ComplexEuclidean 1)
    (law : ∀ radius ∈ Icc lower 1, HasDerivWithinAt field (derivative radius) (Icc lower 1) radius)
    (smooth : ContDiffOn ℝ order derivative (Icc lower 1)) :
    ContDiffOn ℝ (order + 1 : ℕ) field (Icc lower 1) := by
  have unique : UniqueDiffOn ℝ (Icc lower 1) := uniqueDiffOn_Icc bounded
  rw [Nat.cast_add, Nat.cast_one, contDiffOn_succ_iff_derivWithin unique]
  refine ⟨fun radius inside => (law radius inside).differentiableWithinAt, by simp, ?_⟩
  have equality : EqOn (derivWithin field (Icc lower 1)) derivative (Icc lower 1) :=
    fun radius inside => (law radius inside).derivWithin (unique radius inside)
  exact (contDiffOn_congr equality).mpr smooth

/-- The physical first-order annular system is bootstrapped through both
endpoints. The induction starts from continuity and assumes no higher
regularity of either solution coordinate. -/
theorem annularPhysicalSystem_smooth (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (mode : HighAnnularMode)
    (f g h : C(ℝ, ComplexEuclidean 1))
    (fSmooth : ContDiffOn ℝ ∞ f (Icc lower 1))
    (gSmooth : ContDiffOn ℝ ∞ g (Icc lower 1))
    (hSmooth : ContDiffOn ℝ ∞ h (Icc lower 1))
    (xi q : C(ℝ, ComplexEuclidean 1))
    (xiLaw : ∀ radius ∈ Icc lower 1,
      HasDerivWithinAt xi (q radius - (2 / radius : ℝ) • xi radius + f radius) (Icc lower 1) radius)
    (qLaw : ∀ radius ∈ Icc lower 1,
      HasDerivWithinAt q ((1 / radius : ℝ) • q radius +
        annularPotential length radius mode.val.1 mode.val.2 • xi radius -
        (4 : ℝ) • ((1 / radius : ℝ) • ((1 / radius : ℝ) • xi radius)) -
        annularDSymbol mode • g radius - annularCellSymbol length mode • h radius) (Icc lower 1) radius) :
    ContDiffOn ℝ ∞ xi (Icc lower 1) ∧ ContDiffOn ℝ ∞ q (Icc lower 1) := by
  have everyOrder (order : ℕ) : ContDiffOn ℝ order xi (Icc lower 1) ∧
      ContDiffOn ℝ order q (Icc lower 1) := by
    induction order with
    | zero => exact ⟨contDiffOn_zero.mpr xi.continuous.continuousOn,
        contDiffOn_zero.mpr q.continuous.continuousOn⟩
    | succ order previous =>
      have inverse : ContDiffOn ℝ order (fun radius : ℝ => 1 / radius) (Icc lower 1) :=
        contDiffOn_const.div contDiffOn_id (fun radius inside => (positive.trans_le inside.1).ne')
      have twice : ContDiffOn ℝ order (fun radius : ℝ => 2 / radius) (Icc lower 1) :=
        contDiffOn_const.div contDiffOn_id (fun radius inside => (positive.trans_le inside.1).ne')
      have potential : ContDiffOn ℝ order
          (fun radius => annularPotential length radius mode.val.1 mode.val.2) (Icc lower 1) :=
        (contDiffOn_const.div (contDiffOn_id.pow 2)
          (fun radius inside => pow_ne_zero 2 (positive.trans_le inside.1).ne')).add contDiffOn_const
      have first := (previous.2.sub (twice.smul previous.1)).add ((contDiffOn_infty.mp fSmooth) order)
      have second := (((inverse.smul previous.2).add (potential.smul previous.1)).sub
        ((inverse.smul (inverse.smul previous.1)).const_smul (4 : ℝ))).sub
          (((contDiffOn_infty.mp gSmooth) order).const_smul (annularDSymbol mode))
      have last := second.sub (((contDiffOn_infty.mp hSmooth) order).const_smul (annularCellSymbol length mode))
      exact ⟨annular_closedCollar_succ lower bounded order xi _ xiLaw first,
        annular_closedCollar_succ lower bounded order q _ qLaw last⟩
  exact ⟨contDiffOn_infty.mpr (fun order => (everyOrder order).1),
    contDiffOn_infty.mpr (fun order => (everyOrder order).2)⟩

end Grad.AnnularRegularity
