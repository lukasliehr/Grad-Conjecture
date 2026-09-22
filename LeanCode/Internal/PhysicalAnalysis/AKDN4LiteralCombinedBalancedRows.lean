import AKDN3SameBalancedPhysicalRows

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularKernelL2 Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularWeightedSystem Grad.AnnularStrongData

theorem conjugatedOriginalPairCurve_meanZero (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (grade : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (cell : ℤ) :
    hilbertPairCoefficient (0,cell) (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius) = 0 := by
  rw [conjugatedOriginalPairCurve_coefficient parameters lower length positive bounded lengthPositive field allGrades grade radius inside (0,cell),
    sameCoupledXCoefficient_meanZero,sameCoupledXiCoefficient_meanZero]
  exact smul_zero _

theorem balancedOriginalPairCurve_meanZero (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (grade : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) (cell : ℤ) :
    hilbertPairCoefficient (0,cell) (balancedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius) = 0 := by
  have first := congrArg Prod.snd (conjugatedOriginalPairCurve_meanZero parameters lower length positive bounded lengthPositive field allGrades
    (grade+1) radius inside cell)
  have second := congrArg Prod.fst (conjugatedOriginalPairCurve_meanZero parameters lower length positive bounded lengthPositive field allGrades
    grade radius inside cell)
  change (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1) radius).2 (0,cell) = 0 at first
  change (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius).1 (0,cell) = 0 at second
  change (radius⁻¹ • (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1) radius).2 (0,cell),
    (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field grade radius).1 (0,cell)) = 0
  rw [first,second,smul_zero]
  rfl

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (lowerHalf : lower ≤ 1/2) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : StrongDataCarrier parameters lower positive (lowerHalf.trans (by norm_num)) 0 0)
    (field : CoupledSpace lower length positive lengthPositive)
    (curves : ActualSourceRadialCurves parameters lower positive (lowerHalf.trans_lt (by norm_num)) data)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)

local notation "bounded" => lowerHalf.trans_lt (by norm_num : (1:ℝ)/2<1)
local notation "pair" => conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field
local notation "unknownRow" => balancedUnknownPhysicalRow parameters length compact lower positive bounded lengthPositive state field
local notation "knownRow" => generalConjugatedKnownRowCurve parameters length compact lower positive bounded state data curves
local notation "rhs" => generalConjugatedSystemRHS parameters length compact lower positive lowerHalf lengthPositive state data field curves

include allGrades

/-- Literal combination of SAME homogeneous and prescribed-source rows.
The actual native angular projection remains on both components. -/
theorem generalConjugatedSystemRHS_combinedRows (grade : ℕ) (radius : ℝ)
    (inside : radius ∈ Icc lower 1) (mode : ℤ × ℤ) :
    let row := fun index : Fin 3 => unknownRow index grade radius mode+knownRow index (grade+1) radius mode
    hilbertPairCoefficient mode (rhs grade radius) =
      (if mode.1=0 then (0 : ℂ) else 1) •
        ((-((radius : ℂ)⁻¹)) • (pair grade radius).1 mode-
          (length : ℂ)⁻¹ • (frequencyRatioSymbol (some true) mode • row 1)-
          (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • row 2)+
          (radius : ℂ)⁻¹ • (frequencyRatioSymbol (some false) mode • curves.third (grade+1) radius mode),
          (if mode.1=0 then (0 : ℂ) else 1) •
            (frequencyRatioSymbol none mode • row 0+curves.force grade radius mode)) := by
  dsimp only
  unfold generalConjugatedSystemRHS
  rw [physicalPairMeanFree_coefficient,(hilbertPairCoefficient mode).map_add,
    conjugatedRadialSystemOperator_coefficient]
  have rows (index : Fin 3) :
      radialConjugatedAction parameters lower positive (bounded).le (lowPhysicalRowKernel parameters length compact state index)
        (grade+1) 0 radius (rawUnknownSevenOperator parameters radius (pair (grade+2) radius)) =
        unknownRow index grade radius :=
    (balancedUnknownPhysicalRow_original parameters length compact lower positive bounded lengthPositive state field allGrades index grade radius inside).symm
  dsimp only
  have rowsMode (index : Fin 3) := congrArg (fun value : CellL2 1 => value mode) (rows index)
  dsimp only at rowsMode
  rw [rowsMode 0,rowsMode 1,rowsMode 2]
  have source := generalConjugatedSystemSource_coefficient parameters length compact lower positive bounded state data curves grade radius mode
  change hilbertPairCoefficient mode
    (generalConjugatedSystemSource parameters length compact lower positive bounded state data curves grade radius) = _ at source
  rw [source]
  have high := congrArg Prod.fst (conjugatedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive field allGrades grade 2 radius inside mode)
  change (pair (grade+2) radius).1 mode = (annularFrequency mode.1 mode.2 : ℂ)^2 • (pair grade radius).1 mode at high
  unfold conjugatedUnknownPointRHS
  rw [high]
  congr 1
  have frequencyNonzero : (annularFrequency mode.1 mode.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Grad.SourceBoundaryTrace.annularFrequency_pos mode).ne'
  have radiusNonzero : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (positive.trans_le inside.1).ne'
  have lengthNonzero : (length : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr lengthPositive.ne'
  apply Prod.ext <;> apply PiLp.ext <;> intro coordinate
  · simp only [Prod.fst_add,PiLp.add_apply,PiLp.sub_apply,PiLp.smul_apply,smul_eq_mul,frequencyRatioSymbol]
    field_simp
    ring
  · simp only [Prod.snd_add,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
    ring

end Grad.OriginalCartesianTameEstimate
