import AKDN2LiteralBalancedUnknownPacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularKernelL2 Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularWeightedSystem Grad.AnnularStrongData

theorem radialConjugatedAction_zero_apply {source target : ℕ} (parameters : PhaseParameters)
    (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (kernel : (radius : RadialPoint) → RadialKernel parameters radius source target)
    (grade : ℕ) (radius : ℝ) (field : CellL2 source) :
    radialConjugatedAction parameters lower positive bounded kernel grade 0 radius field =
      bulkKernelAction parameters grade (collarRadius lower positive bounded radius)
        (kernel (collarRadius lower positive bounded radius)) field :=
  conjugatedKernelAction_same parameters grade 0 _ _ field field (fun _ => by rw [pow_zero,one_smul])

theorem actualKnownPhysicalRow_shift (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (curves : ActualSourceRadialCurves parameters lower positive bounded data)
    (row : Fin 3) (grade reserve : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    generalConjugatedKnownRowCurve parameters length compact lower positive bounded state data curves row (grade+reserve) radius mode =
      (annularFrequency mode.1 mode.2 : ℂ)^reserve •
        generalConjugatedKnownRowCurve parameters length compact lower positive bounded state data curves row grade radius mode := by
  have same := actualWeightedCurve_shift lower bounded curves.seven (fun grade => (curves.sevenSmooth grade).continuousOn)
    _ curves.sevenSame grade reserve radius inside
  unfold generalConjugatedKnownRowCurve
  rw [radialConjugatedAction_zero_apply,radialConjugatedAction_zero_apply]
  exact actualBulkKernelAction_shift parameters grade reserve _ _ _ _ same mode

def balancedUnknownPhysicalRow (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) (field : CoupledSpace lower length positive lengthPositive)
    (row : Fin 3) (grade : ℕ) (radius : ℝ) : CellL2 1 :=
  bulkKernelAction parameters (grade+1) (collarRadius lower positive bounded.le radius)
    (lowPhysicalRowKernel parameters length compact state row (collarRadius lower positive bounded.le radius))
    (balancedSevenInput parameters radius (balancedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1) radius))

theorem balancedUnknownPhysicalRow_original (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (row : Fin 3) (grade : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    balancedUnknownPhysicalRow parameters length compact lower positive bounded lengthPositive state field row grade radius =
      radialConjugatedAction parameters lower positive bounded.le (lowPhysicalRowKernel parameters length compact state row)
        (grade+1) 0 radius (rawUnknownSevenOperator parameters radius
          (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+2) radius)) := by
  rw [radialConjugatedAction_zero_apply,balancedUnknownPhysicalRow,
    balancedSevenInput_original parameters lower length positive bounded lengthPositive field allGrades grade radius inside]

theorem balancedUnknownPhysicalRow_shift (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact) (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (row : Fin 3) (grade reserve : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    balancedUnknownPhysicalRow parameters length compact lower positive bounded lengthPositive state field row (grade+reserve) radius mode =
      (annularFrequency mode.1 mode.2 : ℂ)^reserve •
        balancedUnknownPhysicalRow parameters length compact lower positive bounded lengthPositive state field row grade radius mode := by
  have same := balancedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive field allGrades
    (grade+1) reserve radius inside
  have inputSame := balancedSevenInput_sameGrade parameters radius reserve _ _ same
  unfold balancedUnknownPhysicalRow
  rw [show grade+reserve+1=grade+1+reserve by omega]
  exact actualBulkKernelAction_shift parameters (grade+1) reserve _ _ _ _ inputSame mode

theorem hilbertFrequencyDrop_same {dimension : ℕ} (parameters : PhaseParameters) (high low : CellL2 dimension)
    (same : ∀ mode, high mode=(annularFrequency mode.1 mode.2 : ℂ) • low mode) :
    hilbertFrequencyOperator parameters dimension none high = low := by
  apply lp.ext
  funext mode
  change frequencyRatioSymbol none mode • high mode = low mode
  rw [same,frequencyRatioSymbol,one_div,inv_smul_smul₀]
  exact Complex.ofReal_ne_zero.mpr (Grad.SourceBoundaryTrace.annularFrequency_pos mode).ne'

end Grad.OriginalCartesianTameEstimate
