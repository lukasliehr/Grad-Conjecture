import AKAQ4ActualFourierTaylorSymbols

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open scoped BigOperators
namespace Grad.OriginalFlatAxisDecay
open Grad.FourierGrade Grad.CartesianState Grad.ClosedJets Grad.COR12Extension
open Grad.COR13Completion Grad.SourceCollarDivision Grad.DiskExtension.Operator

local instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

theorem reconstructedTorus_single {dimension : ℕ} (mode : FourierMode)
    (value : ComplexEuclidean dimension) :
    reconstructedTorus (singleCore mode value) = vectorTorusTerm mode value := by
  classical
  unfold reconstructedTorus
  rw [tsum_eq_single mode]
  · simp [singleCore,coreOfFiniteSupport]
  · intro other different
    have : vectorTorusTerm other (0 : ComplexEuclidean dimension) = 0 := by ext; simp [vectorTorusTerm]
    simpa [singleCore,coreOfFiniteSupport,different] using this

theorem torusCharacter_disk (mode : SpatialMode) (source : ℤ) (point : ClosedDisk) (circle : CellCircle) :
    torusCharacter (fibreMode (source,mode)) (torusCellToProduct (diskToTorus (point,circle))) =
      cellCharacter source circle * Complex.exp (Complex.I * (waveAngle mode point.val : ℂ)) := by
  induction circle using QuotientAddGroup.induction_on with
  | H coordinate =>
    have pointIdentity : diskToTorus (point,(coordinate : CellCircle)) =
        torusCellPoint (assembleSpatialCell point.val coordinate) := by rfl
    rw [pointIdentity,torusCellToProduct_torusCellPoint,torusCharacter_normalized_apply,cellCharacter_coe]
    simp only [fibreMode,assembleSpatialCell,Fin.isValue,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
    unfold cellExponential
    rw [← Complex.exp_add]
    congr 1
    simp only [waveAngle,Complex.ofReal_add,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_intCast]
    ring

theorem retraction_weighted_core {dimension : ℕ} (parameters : PhaseParameters)
    (values : JCore (ComplexEuclidean dimension)) (cell : ℤ) :
    phaseWeightedJet parameters cell ((weightedFourierRetraction parameters values).val cell) =
      diskCellFourierCoefficientJet
        (ordinaryExtensionRetraction.restriction dimension (reconstructedTorusSmoothField values)) cell := by
  have law := diskCellFourierCoefficientJet_weightedSmoothEquiv parameters
    (weightedFourierRetraction parameters values) cell
  rw [weightedFourierRetraction,LinearMap.coe_mk,AddHom.coe_mk,LinearEquiv.apply_symm_apply] at law
  exact law.symm

theorem completedRetraction_single_weightedCell {dimension : ℕ} (parameters : PhaseParameters)
    (mode : SpatialMode) (source cell : ℤ) (value : ComplexEuclidean dimension) (point : ClosedDisk) :
    completedWeightedCell parameters (by omega : 3 ≤ 4) cell
      (completedRetraction parameters (coefficientSingle 4 (fibreMode (source,mode)) value)) point =
      if source = cell then Complex.exp (Complex.I * (waveAngle mode point.val : ℂ)) • value else 0 := by
  classical
  rw [← coreToGrade_single,completedRetraction_apply_core,completedWeightedCell_core]
  change (phaseWeightedJet parameters cell ((weightedFourierRetraction parameters (singleCore (fibreMode (source,mode)) value)).val cell)).value point = _
  rw [retraction_weighted_core,diskCellFourierCoefficientJet_value,diskCellFourierValue_apply]
  have values : (fun circle : CellCircle =>
      (ordinaryExtensionRetraction.restriction dimension
        (reconstructedTorusSmoothField (singleCore (fibreMode (source,mode)) value))).value (point,circle)) =
      (fun circle : CellCircle => cellCharacter source circle •
        (Complex.exp (Complex.I * (waveAngle mode point.val : ℂ)) • value)) := by
    funext circle
    change reconstructedTorus (singleCore (fibreMode (source,mode)) value)
      (torusCellToProduct (diskToTorus (point,circle))) = _
    rw [reconstructedTorus_single]
    change torusCharacter _ _ • value = _
    rw [torusCharacter_disk,mul_smul]
  rw [values,fourierCoeff_cellCharacter_smul]

end Grad.OriginalFlatAxisDecay
