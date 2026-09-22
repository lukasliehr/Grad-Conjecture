import AKAW9LowPacketInsertedTransport

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.AnnularCurrentEnergy Grad.AnnularReconstruction Grad.AnnularVariational Grad.AnnularCrossMaps
open Grad.AnnularTiltedReference Grad.AnnularGrades Grad.CircularHighWeak Grad.CircularHighRegularity

private theorem highBulkSlot_scaled {dimension : ℕ} (lower : ℝ) (slot : Fin dimension)
    (first second : AnnularBulk lower) (scale : ℤ × ℤ → ℂ)
    (same : ∀ mode, second mode = scale mode.val • first mode) (mode : ℤ × ℤ) :
    highBulkSlot lower slot second mode = scale mode • highBulkSlot lower slot first mode := by
  change radialMatrixUnit lower slot 0 (highBulkIntoFull lower second mode) =
    scale mode • radialMatrixUnit lower slot 0 (highBulkIntoFull lower first mode)
  by_cases high : 3 ≤ |mode.1|
  · rw [highBulkIntoFull_high lower second ⟨mode,high⟩,highBulkIntoFull_high lower first ⟨mode,high⟩,
      same ⟨mode,high⟩,map_smul]
  · rw [highBulkIntoFull_low lower second mode high,highBulkIntoFull_low lower first mode high,map_zero,smul_zero]

/-- The true b-normalized high energy coordinates commute with the insertion
on the original stored graph, with no change of physical field. -/
theorem highSevenPacket_scaled (lower length : ℝ) (positive : 0 < lower) (lengthPositive : 0 < length)
    (first second : CrossHighSpace lower length positive lengthPositive) (scale : ℤ × ℤ → ℂ)
    (sameEnergy : ∀ mode : HighAnnularMode, second.ofLp.1.val mode = scale mode.val • first.ofLp.1.val mode)
    (sameFlux : ∀ mode : HighAnnularMode, second.ofLp.2.val 0 mode = scale mode.val • first.ofLp.2.val 0 mode)
    (mode : ℤ × ℤ) :
    highCrossSevenInput lower length positive lengthPositive second mode =
      scale mode • highCrossSevenInput lower length positive lengthPositive first mode := by
  have mass (index : HighAnnularMode) :
      annularEnergyMass lower length positive (bEnergyDecode lower length positive second.ofLp.1) index =
        scale index.val • annularEnergyMass lower length positive (bEnergyDecode lower length positive first.ofLp.1) index := by
    change annularModeMass lower ((bEnergyDecode lower length positive second.ofLp.1).val index) =
      scale index.val • annularModeMass lower ((bEnergyDecode lower length positive first.ofLp.1).val index)
    rw [bEnergyDecode,annularEnergyDiagonal_apply,annularEnergyDiagonal_apply,sameEnergy index,
      smul_comm (Real.sqrt (highMultiplier index.val.1) : ℂ) (scale index.val),map_smul]
  have value (index : HighAnnularMode) :
      annularEnergyValue lower length positive (bEnergyDecode lower length positive second.ofLp.1) index =
        scale index.val • annularEnergyValue lower length positive (bEnergyDecode lower length positive first.ofLp.1) index := by
    change annularValueMassMap lower length positive index
      (annularEnergyMass lower length positive (bEnergyDecode lower length positive second.ofLp.1) index) =
      scale index.val • annularValueMassMap lower length positive index
        (annularEnergyMass lower length positive (bEnergyDecode lower length positive first.ofLp.1) index)
    rw [mass index,map_smul]
  have radial (index : HighAnnularMode) :
      highEnergyRadius lower length positive (bEnergyDecode lower length positive second.ofLp.1) index =
        scale index.val • highEnergyRadius lower length positive (bEnergyDecode lower length positive first.ofLp.1) index := by
    rw [highEnergyRadius_mode,highEnergyRadius_mode,value index,map_smul]
  have angular (index : HighAnnularMode) :
      highEnergyAngularRadius lower length positive (bEnergyDecode lower length positive second.ofLp.1) index =
        scale index.val • highEnergyAngularRadius lower length positive (bEnergyDecode lower length positive first.ofLp.1) index := by
    rw [highEnergyAngularRadius_mode,highEnergyAngularRadius_mode,radial index,smul_comm]
  have cell (index : HighAnnularMode) :
      ((length : ℂ) • highEnergyCell lower length positive (bEnergyDecode lower length positive second.ofLp.1)) index =
        scale index.val • ((length : ℂ) • highEnergyCell lower length positive (bEnergyDecode lower length positive first.ofLp.1)) index := by
    have one := highEnergyCell_mode lower length positive (bEnergyDecode lower length positive second.ofLp.1) index
    have two := highEnergyCell_mode lower length positive (bEnergyDecode lower length positive first.ofLp.1) index
    change (length : ℂ) • highEnergyCell lower length positive (bEnergyDecode lower length positive second.ofLp.1) index =
      scale index.val • ((length : ℂ) • highEnergyCell lower length positive (bEnergyDecode lower length positive first.ofLp.1) index)
    rw [one,two,value index]
    simp only [smul_smul]
    congr 1
    ring
  change highBulkSlot lower (0 : Fin 7) (crossHighX lower length positive lengthPositive second) mode +
    highBulkSlot lower (1 : Fin 7) (highEnergyAngularRadius lower length positive (bEnergyDecode lower length positive second.ofLp.1)) mode +
    highBulkSlot lower (2 : Fin 7) ((length : ℂ) • highEnergyCell lower length positive (bEnergyDecode lower length positive second.ofLp.1)) mode +
    highBulkSlot lower (3 : Fin 7) (highEnergyRadius lower length positive (bEnergyDecode lower length positive second.ofLp.1)) mode = _
  have a := highBulkSlot_scaled lower (0 : Fin 7)
    (crossHighX lower length positive lengthPositive first) (crossHighX lower length positive lengthPositive second) scale sameFlux mode
  have b := highBulkSlot_scaled lower (1 : Fin 7)
    (highEnergyAngularRadius lower length positive (bEnergyDecode lower length positive first.ofLp.1))
    (highEnergyAngularRadius lower length positive (bEnergyDecode lower length positive second.ofLp.1)) scale angular mode
  have c := highBulkSlot_scaled lower (2 : Fin 7)
    ((length : ℂ) • highEnergyCell lower length positive (bEnergyDecode lower length positive first.ofLp.1))
    ((length : ℂ) • highEnergyCell lower length positive (bEnergyDecode lower length positive second.ofLp.1)) scale cell mode
  have d := highBulkSlot_scaled lower (3 : Fin 7)
    (highEnergyRadius lower length positive (bEnergyDecode lower length positive first.ofLp.1))
    (highEnergyRadius lower length positive (bEnergyDecode lower length positive second.ofLp.1)) scale radial mode
  have assembled : highCrossSevenInput lower length positive lengthPositive first mode =
      highBulkSlot lower (0 : Fin 7) (crossHighX lower length positive lengthPositive first) mode +
      highBulkSlot lower (1 : Fin 7) (highEnergyAngularRadius lower length positive (bEnergyDecode lower length positive first.ofLp.1)) mode +
      highBulkSlot lower (2 : Fin 7) ((length : ℂ) • highEnergyCell lower length positive (bEnergyDecode lower length positive first.ofLp.1)) mode +
      highBulkSlot lower (3 : Fin 7) (highEnergyRadius lower length positive (bEnergyDecode lower length positive first.ofLp.1)) mode := rfl
  have added := congrArg₂ (fun x y : RadialL2 7 lower => x+y)
    (congrArg₂ (fun x y : RadialL2 7 lower => x+y)
      (congrArg₂ (fun x y : RadialL2 7 lower => x+y) a b) c) d
  have scaledAssembly := congrArg (fun value : RadialL2 7 lower => scale mode • value) assembled
  simp only [smul_add] at scaledAssembly
  exact added.trans scaledAssembly.symm

end Grad.ActualNativeCellMoments
