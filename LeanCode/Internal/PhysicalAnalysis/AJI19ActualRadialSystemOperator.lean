import AJI18HilbertFrequencyOperators
import AJI12ActualFullPhysicalRowsSmooth

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
open scoped ContDiff
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryLift Grad.AnnularRadialSmoothness
open Grad.AnnularReconstruction Grad.AnnularCurrentLow Grad.GaugeCoefficients.Physical.Ledger

abbrev PhysicalHilbertPair := CellL2 1 × CellL2 1

def hilbertSlotInjection (parameters : PhaseParameters) (slot : Fin 7) : CellL2 1 →L[ℂ] CellL2 7 :=
  coefficientOperator parameters 0 (Equiv.refl _) (fun _ => matrixUnit slot 0)
    (norm_nonneg (matrixUnit slot (0 : Fin 1))) (fun _ => le_rfl)

def hilbertMeanFree (parameters : PhaseParameters) : CellL2 1 →L[ℂ] CellL2 1 :=
  boundedHilbertMultiplier parameters 1 (fun mode => if mode.1 = 0 then 0 else 1) 1 zero_le_one
    (fun mode => by split_ifs <;> norm_num)

def rawUnknownSevenOperator (parameters : PhaseParameters) (radius : ℝ) : PhysicalHilbertPair →L[ℂ] CellL2 7 :=
  let drop := hilbertFrequencyOperator parameters 1 none
  let angular := hilbertFrequencyOperator parameters 1 (some false)
  let axial := hilbertFrequencyOperator parameters 1 (some true)
  let x := ContinuousLinearMap.fst ℂ (CellL2 1) (CellL2 1)
  let xi := ContinuousLinearMap.snd ℂ (CellL2 1) (CellL2 1)
  (((hilbertSlotInjection parameters 0).comp (drop.comp x) +
    (radius : ℂ)⁻¹ • (hilbertSlotInjection parameters 1).comp (angular.comp xi)) +
    (hilbertSlotInjection parameters 2).comp (axial.comp xi)) +
    (radius : ℂ)⁻¹ • (hilbertSlotInjection parameters 3).comp (drop.comp xi)

theorem reciprocalRadius_smooth (lower : ℝ) (positive : 0 < lower) :
    ContDiffOn ℝ ∞ (fun radius : ℝ => (radius : ℂ)⁻¹) (Icc lower 1) := by
  have realInverse : ContDiffOn ℝ ∞ (fun radius : ℝ => radius⁻¹) (Icc lower 1) :=
    contDiffOn_id.inv (fun radius inside => (positive.trans_le inside.1).ne')
  simpa only [Function.comp_def, Complex.ofRealCLM_apply, Complex.ofReal_inv] using
    Complex.ofRealCLM.contDiff.comp_contDiffOn realInverse

theorem rawUnknownSevenOperator_smooth (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) :
    ContDiffOn ℝ ∞ (rawUnknownSevenOperator parameters) (Icc lower 1) := by
  exact (((contDiffOn_const.add ((reciprocalRadius_smooth lower positive).smul contDiffOn_const)).add
    contDiffOn_const).add ((reciprocalRadius_smooth lower positive).smul contDiffOn_const))

theorem smoothOperatorComposition {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F]
    [NormedAddCommGroup G] [NormedSpace ℂ G] [NormedSpace ℝ G] [IsScalarTower ℝ ℂ G]
    {set : Set ℝ} {outer : ℝ → F →L[ℂ] G} {inner : ℝ → E →L[ℂ] F}
    (one : ContDiffOn ℝ ∞ outer set) (two : ContDiffOn ℝ ∞ inner set) :
    ContDiffOn ℝ ∞ (fun radius : ℝ => (outer radius).comp (inner radius)) set :=
  ((ContinuousLinearMap.compL ℂ E F G).bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp₂_contDiffOn one two

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (state : RetainedInverseState parameters length compact)
    (positive : 0 < lower) (bounded : lower < 1)

/-- The actual mean-free radial system for (x,xi), with two polynomial
input grades available. The physical P in rV remains inside row 2; the first
row is projected to the original nonzero angular sectors. -/
def originalRadialSystemOperator (grade : ℕ) (radius : ℝ) : PhysicalHilbertPair →L[ℂ] PhysicalHilbertPair :=
  let input := rawUnknownSevenOperator parameters radius
  let drop := hilbertFrequencyOperator parameters 1 none
  let angular := hilbertFrequencyOperator parameters 1 (some false)
  let axial := hilbertFrequencyOperator parameters 1 (some true)
  let row := fun row : Fin 3 => radialPolynomialAction parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state row) (grade + 1) radius
  let xiDerivative := (hilbertMeanFree parameters).comp (drop.comp ((row 0).comp input))
  let xDerivative :=
    (-((radius : ℂ)⁻¹)) • drop.comp (drop.comp (ContinuousLinearMap.fst ℂ (CellL2 1) (CellL2 1))) -
    (length : ℂ)⁻¹ • axial.comp ((row 1).comp input) -
    (radius : ℂ)⁻¹ • angular.comp ((row 2).comp input)
  (ContinuousLinearMap.inl ℂ (CellL2 1) (CellL2 1)).comp xDerivative +
    (ContinuousLinearMap.inr ℂ (CellL2 1) (CellL2 1)).comp xiDerivative

theorem originalRadialSystemOperator_smooth (grade : ℕ) :
    ContDiffOn ℝ ∞ (originalRadialSystemOperator parameters length compact lower state positive bounded grade) (Icc lower 1) := by
  let input := rawUnknownSevenOperator parameters
  let row := fun (index : Fin 3) => radialPolynomialAction parameters lower positive bounded.le
    (lowPhysicalRowKernel parameters length compact state index) (grade + 1)
  let drop := hilbertFrequencyOperator parameters 1 none
  let angular := hilbertFrequencyOperator parameters 1 (some false)
  let axial := hilbertFrequencyOperator parameters 1 (some true)
  let xBase : PhysicalHilbertPair →L[ℂ] CellL2 1 :=
    drop.comp (drop.comp (ContinuousLinearMap.fst ℂ (CellL2 1) (CellL2 1)))
  have inputSmooth : ContDiffOn ℝ ∞ input (Icc lower 1) := rawUnknownSevenOperator_smooth parameters lower positive
  have rowSmooth (index : Fin 3) : ContDiffOn ℝ ∞ (row index) (Icc lower 1) :=
    (sameFullPhysicalRows_smooth parameters length compact state lower positive bounded index) (grade + 1)
  have composed (index : Fin 3) : ContDiffOn ℝ ∞
      (fun radius : ℝ => (row index radius).comp (input radius)) (Icc lower 1) :=
    smoothOperatorComposition (rowSmooth index) inputSmooth
  have firstSmooth : ContDiffOn ℝ ∞
      (fun radius : ℝ => (hilbertMeanFree parameters).comp (drop.comp ((row 0 radius).comp (input radius)))) (Icc lower 1) :=
    smoothOperatorComposition (show ContDiffOn ℝ ∞ (fun _ : ℝ => hilbertMeanFree parameters) (Icc lower 1) from contDiffOn_const)
      (smoothOperatorComposition (show ContDiffOn ℝ ∞ (fun _ : ℝ => drop) (Icc lower 1) from contDiffOn_const) (composed 0))
  have axialSmooth : ContDiffOn ℝ ∞ (fun radius : ℝ => axial.comp ((row 1 radius).comp (input radius))) (Icc lower 1) :=
    smoothOperatorComposition (show ContDiffOn ℝ ∞ (fun _ : ℝ => axial) (Icc lower 1) from contDiffOn_const) (composed 1)
  have angularSmooth : ContDiffOn ℝ ∞ (fun radius : ℝ => angular.comp ((row 2 radius).comp (input radius))) (Icc lower 1) :=
    smoothOperatorComposition (show ContDiffOn ℝ ∞ (fun _ : ℝ => angular) (Icc lower 1) from contDiffOn_const) (composed 2)
  have inverse := reciprocalRadius_smooth lower positive
  have secondSmooth : ContDiffOn ℝ ∞ (fun radius : ℝ =>
      (-((radius : ℂ)⁻¹)) • xBase - (length : ℂ)⁻¹ • axial.comp ((row 1 radius).comp (input radius)) -
        (radius : ℂ)⁻¹ • angular.comp ((row 2 radius).comp (input radius))) (Icc lower 1) :=
    ((inverse.neg.smul (show ContDiffOn ℝ ∞ (fun _ : ℝ => xBase) (Icc lower 1) from contDiffOn_const)).sub
      ((show ContDiffOn ℝ ∞ (fun _ : ℝ => (length : ℂ)⁻¹) (Icc lower 1) from contDiffOn_const).smul axialSmooth)).sub
      (inverse.smul angularSmooth)
  exact (smoothOperatorComposition
    (show ContDiffOn ℝ ∞ (fun _ : ℝ => ContinuousLinearMap.inl ℂ (CellL2 1) (CellL2 1)) (Icc lower 1) from contDiffOn_const) secondSmooth).add
    (smoothOperatorComposition
      (show ContDiffOn ℝ ∞ (fun _ : ℝ => ContinuousLinearMap.inr ℂ (CellL2 1) (CellL2 1)) (Icc lower 1) from contDiffOn_const) firstSmooth)

end Grad.AnnularSmoothCore
