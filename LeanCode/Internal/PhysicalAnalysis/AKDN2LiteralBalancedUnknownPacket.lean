import AKDN1SameBalancedHilbertCurve

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set
namespace Grad.OriginalCartesianTameEstimate
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.BoundaryKernelAction Grad.AnnularReconstruction
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularWeightedSmoothness
open Grad.AnnularGeneralSourceRegularity Grad.AnnularKernelL2 Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularWeightedSystem
open Grad.GaugeCoefficients.Physical.Ledger

/-- Exact nu shifts through the SAME original-width action. -/
theorem actualBulkKernelAction_shift {source target : ℕ} (parameters : PhaseParameters)
    (grade reserve : ℕ) (radius : RadialPoint) (kernel : RadialKernel parameters radius source target)
    (high low : CellL2 source)
    (same : ∀ mode, high mode=(annularFrequency mode.1 mode.2 : ℂ)^reserve • low mode)
    (mode : ℤ × ℤ) :
    bulkKernelAction parameters (grade+reserve) radius kernel high mode =
      (annularFrequency mode.1 mode.2 : ℂ)^reserve • bulkKernelAction parameters grade radius kernel low mode := by
  have actual := congrArg (fun mapping : CellL2 source →L[ℂ] CellL2 target => mapping high mode)
    (bulkKernelAction_reserve parameters grade reserve radius kernel)
  change bulkKernelAction parameters grade radius kernel (hilbertReserve parameters source reserve high) mode =
    frequencyReserveSymbol reserve mode • bulkKernelAction parameters (grade+reserve) radius kernel high mode at actual
  rw [hilbertReserve_same parameters source reserve high low same] at actual
  have nonzero : (annularFrequency mode.1 mode.2 : ℂ)^reserve ≠ 0 :=
    pow_ne_zero reserve (Complex.ofReal_ne_zero.mpr (Grad.SourceBoundaryTrace.annularFrequency_pos mode).ne')
  calc
    _ = (annularFrequency mode.1 mode.2 : ℂ)^reserve •
        (frequencyReserveSymbol reserve mode • bulkKernelAction parameters (grade+reserve) radius kernel high mode) :=
      (smul_inv_smul₀ nonzero _).symm
    _ = _ := congrArg ((annularFrequency mode.1 mode.2 : ℂ)^reserve • ·) actual.symm

theorem balancedSevenPointMap_unknown (radius : ℝ) (nonzero : radius ≠ 0) (mode : ℤ × ℤ)
    (x xi : ComplexEuclidean 1) :
    balancedSevenPointMap radius mode ((radius : ℂ)⁻¹ • xi,frequencyRatioSymbol none mode • x) =
      unknownSevenPointMap radius mode (x,xi) := by
  have radiusNonzero : (radius : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr nonzero
  change (((matrixUnit (0 : Fin 7) (0 : Fin 1)) (frequencyRatioSymbol none mode • x)+
    (matrixUnit (1 : Fin 7) (0 : Fin 1)) (frequencyRatioSymbol (some false) mode • ((radius : ℂ)⁻¹ • xi)))+
    (radius : ℂ) • (matrixUnit (2 : Fin 7) (0 : Fin 1)) (frequencyRatioSymbol (some true) mode • ((radius : ℂ)⁻¹ • xi)))+
    (matrixUnit (3 : Fin 7) (0 : Fin 1)) (frequencyRatioSymbol none mode • ((radius : ℂ)⁻¹ • xi)) =
    (((matrixUnit (0 : Fin 7) (0 : Fin 1)) (frequencyRatioSymbol none mode • x)+
      (radius : ℂ)⁻¹ • (matrixUnit (1 : Fin 7) (0 : Fin 1)) (frequencyRatioSymbol (some false) mode • xi))+
      (matrixUnit (2 : Fin 7) (0 : Fin 1)) (frequencyRatioSymbol (some true) mode • xi))+
      (radius : ℂ)⁻¹ • (matrixUnit (3 : Fin 7) (0 : Fin 1)) (frequencyRatioSymbol none mode • xi)
  apply PiLp.ext
  intro slot
  simp only [map_smul,smul_smul,PiLp.add_apply,PiLp.smul_apply,smul_eq_mul]
  field_simp

/-- The exact balanced next-grade packet is the already constructed
homogeneous seven-slot input. No new unknown field is introduced. -/
theorem balancedSevenInput_original (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive)
    (allGrades : ∀ grade : ℕ, ∃ weighted : CoupledSpace lower length positive lengthPositive,
      CoupledInsertedGrade lower length positive lengthPositive grade field weighted)
    (grade : ℕ) (radius : ℝ) (inside : radius ∈ Icc lower 1) :
    balancedSevenInput parameters radius (balancedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1) radius) =
      rawUnknownSevenOperator parameters radius
        (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+2) radius) := by
  apply lp.ext
  funext mode
  rw [balancedSevenInput_point,rawUnknownSevenOperator_point]
  have shifted := congrArg Prod.fst (conjugatedOriginalPairCurve_shift parameters lower length positive bounded lengthPositive field allGrades
    (grade+1) 1 radius inside mode)
  change (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1+1) radius).1 mode =
    (annularFrequency mode.1 mode.2 : ℂ)^1 •
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1) radius).1 mode at shifted
  rw [pow_one] at shifted
  have frequencyNonzero : (annularFrequency mode.1 mode.2 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Grad.SourceBoundaryTrace.annularFrequency_pos mode).ne'
  have lowerSame : (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1) radius).1 mode =
      frequencyRatioSymbol none mode •
        (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+2) radius).1 mode := by
    rw [show grade+2=grade+1+1 by omega,shifted]
    simp only [frequencyRatioSymbol,one_div]
    change (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1) radius).1 mode =
      (annularFrequency mode.1 mode.2 : ℂ)⁻¹ • ((annularFrequency mode.1 mode.2 : ℂ) •
        (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1) radius).1 mode)
    exact (inv_smul_smul₀ frequencyNonzero _).symm
  change balancedSevenPointMap radius mode
    (radius⁻¹ • (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1+1) radius).2 mode,
      (conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+1) radius).1 mode) = _
  rw [show grade+1+1=grade+2 by omega,lowerSame]
  convert balancedSevenPointMap_unknown radius (positive.trans_le inside.1).ne' mode
    ((conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+2) radius).1 mode)
    ((conjugatedOriginalPairCurve parameters lower length positive bounded lengthPositive field (grade+2) radius).2 mode) using 1
  · congr 2
    apply PiLp.ext
    intro coordinate
    simp only [PiLp.smul_apply,← Complex.coe_smul,Complex.ofReal_inv]
  · rfl

end Grad.OriginalCartesianTameEstimate
