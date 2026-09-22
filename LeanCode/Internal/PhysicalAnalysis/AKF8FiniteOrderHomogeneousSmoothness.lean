import AKF7ReservedHomogeneousOperator

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff
namespace Grad.AnnularWeightedSystem
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.AnnularReconstruction Grad.SourceCollarCoefficients Grad.AnnularStrongOrbit
open Grad.AnnularSmoothCore Grad.PhaseAlgebra Grad.AnnularCurrentLow
open Grad.AnnularWeightedSmoothness Grad.AnnularKernelL2

/-- Finite-order real calculus for the original complex operator spaces. -/
theorem finiteOrderOperatorComposition {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G]
    {order : WithTop ℕ∞} {domain : Set ℝ}
    {outer : ℝ → F →L[ℂ] G} {inner : ℝ → E →L[ℂ] F}
    (one : ContDiffOn ℝ order outer domain) (two : ContDiffOn ℝ order inner domain) :
    ContDiffOn ℝ order (fun radius => (outer radius).comp (inner radius)) domain :=
  ((ContinuousLinearMap.compL ℂ E F G).bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp₂_contDiffOn one two

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (state : RetainedInverseState parameters length compact)
    (positive : 0 < lower) (bounded : lower < 1)

theorem reservedConjugatedRadialSystemOperator_smooth (grade reserve order : ℕ)
    (rowsSmooth : ∀ index : Fin 3, ContDiffOn ℝ order
      (radialConjugatedAction parameters lower positive bounded.le
        (lowPhysicalRowKernel parameters length compact state index) (grade + 1) reserve) (Icc lower 1)) :
    ContDiffOn ℝ order
      (reservedConjugatedRadialSystemOperator parameters length compact lower state positive bounded grade reserve)
      (Icc lower 1) := by
  let input := rawUnknownSevenOperator parameters
  let row := fun index : Fin 3 => radialConjugatedAction parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state index) (grade + 1) reserve
  let drop := hilbertFrequencyOperator parameters 1 none
  let angular := hilbertFrequencyOperator parameters 1 (some false)
  let axial := hilbertFrequencyOperator parameters 1 (some true)
  let xBase : PhysicalHilbertPair →L[ℂ] CellL2 1 :=
    drop.comp (drop.comp ((ContinuousLinearMap.fst ℂ (CellL2 1) (CellL2 1)).comp
      (physicalPairReserve parameters reserve)))
  have inputSmooth : ContDiffOn ℝ order input (Icc lower 1) :=
    (contDiffOn_infty.mp (rawUnknownSevenOperator_smooth parameters lower positive)) order
  have composed (index : Fin 3) : ContDiffOn ℝ order
      (fun radius => (row index radius).comp (input radius)) (Icc lower 1) :=
    finiteOrderOperatorComposition (rowsSmooth index) inputSmooth
  have firstSmooth : ContDiffOn ℝ order
      (fun radius => (hilbertMeanFree parameters).comp (drop.comp ((row 0 radius).comp (input radius)))) (Icc lower 1) :=
    finiteOrderOperatorComposition
      (show ContDiffOn ℝ order (fun _ : ℝ => hilbertMeanFree parameters) (Icc lower 1) from contDiffOn_const)
      (finiteOrderOperatorComposition
        (show ContDiffOn ℝ order (fun _ : ℝ => drop) (Icc lower 1) from contDiffOn_const) (composed 0))
  have axialSmooth : ContDiffOn ℝ order (fun radius => axial.comp ((row 1 radius).comp (input radius))) (Icc lower 1) :=
    finiteOrderOperatorComposition
      (show ContDiffOn ℝ order (fun _ : ℝ => axial) (Icc lower 1) from contDiffOn_const) (composed 1)
  have angularSmooth : ContDiffOn ℝ order (fun radius => angular.comp ((row 2 radius).comp (input radius))) (Icc lower 1) :=
    finiteOrderOperatorComposition
      (show ContDiffOn ℝ order (fun _ : ℝ => angular) (Icc lower 1) from contDiffOn_const) (composed 2)
  have inverse := (contDiffOn_infty.mp (reciprocalRadius_smooth lower positive)) order
  have secondSmooth : ContDiffOn ℝ order (fun radius : ℝ =>
      (-((radius : ℂ)⁻¹)) • xBase - (length : ℂ)⁻¹ • axial.comp ((row 1 radius).comp (input radius)) -
        (radius : ℂ)⁻¹ • angular.comp ((row 2 radius).comp (input radius))) (Icc lower 1) :=
    ((inverse.neg.smul (show ContDiffOn ℝ order (fun _ : ℝ => xBase) (Icc lower 1) from contDiffOn_const)).sub
      (axialSmooth.const_smul (length : ℂ)⁻¹)).sub (inverse.smul angularSmooth)
  have combined := (finiteOrderOperatorComposition
    (show ContDiffOn ℝ order (fun _ : ℝ => ContinuousLinearMap.inl ℂ (CellL2 1) (CellL2 1)) (Icc lower 1) from contDiffOn_const)
      secondSmooth).add (finiteOrderOperatorComposition
    (show ContDiffOn ℝ order (fun _ : ℝ => ContinuousLinearMap.inr ℂ (CellL2 1) (CellL2 1)) (Icc lower 1) from contDiffOn_const)
      firstSmooth)
  apply combined.congr
  intro radius _
  apply ContinuousLinearMap.ext
  intro field
  apply Prod.ext <;> simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.inl_apply, ContinuousLinearMap.inr_apply, Prod.fst_add, Prod.snd_add,
    add_zero, zero_add] <;> rfl

end Grad.AnnularWeightedSystem
