import AKBV4MixedJetOriginalCompletion

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set Filter MeasureTheory
open scoped BigOperators ContDiff Topology
namespace Grad.CartesianCoreRecovery
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap
open Grad.WeightedJets Grad.CompatibleCompletion Grad.RawSourceFaithfulness
open Grad.ActualOriginalSourceMoments Grad.ActualOriginalSourceFirst Grad.CartesianStartup

/-- Existing original grade-zero coordinates faithfully represent the same joint weighted carrier. -/
theorem originalSourceMoments_zeroCell {dimension : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (cell : ℤ) :
    zeroCell parameters cell (aGradeEta parameters (GradeCore.ofCoreLinear core)) =
      fieldCellProjection dimension openUnitDisk cell (originalSourceMoments parameters core).field := by
  rw [zeroCell_core]
  apply Lp.ext
  filter_upwards [closedContinuousToDiskL2_ae (phaseWeightedJet parameters cell (core.val cell)).value,
    fieldCellProjection_ae dimension openUnitDisk (originalSourceMoments parameters core).field,
    originalSourceJointField_weightedCell parameters core,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point closed projected same inside
  rw [closed,closedDiskLift,dif_pos (openDiskMembershipClosed point inside),projected cell]
  change _ = originalSourceJointField parameters core 0 point cell
  rw [same cell]
  exact (Grad.Constraints.smoothClosedExtension_value
    (phaseWeightedJet parameters cell (core.val cell)) ⟨point,openDiskMembershipClosed point inside⟩).symm

/-- Standard all-order mixed weak jets of one weighted joint field recover one actual original ACore, simultaneously in every original grade. -/
theorem allMixed_sameOriginalCore {dimension : ℕ} (parameters : PhaseParameters)
    (field : StartupL2 dimension) (jets : ∀ grade, Mixed dimension grade openUnitDisk)
    (sameBase : ∀ grade, base dimension grade openUnitDisk (fun index => grade-degree index) (jets grade) = field) :
    ∃ core : ACore parameters dimension,
      (originalSourceMoments parameters core).field = field ∧
      ∀ grade, ‖aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) core)‖ = ‖jets grade‖ := by
  have completion := fun grade => mixedJet_originalCompletion parameters (jets grade)
  let values : ∀ grade, AGrade parameters dimension grade := fun grade => Classical.choose (completion grade)
  have norms (grade : ℕ) : ‖values grade‖ = ‖jets grade‖ := (Classical.choose_spec (completion grade)).1
  have cells (grade : ℕ) (cell : ℤ) :
      zeroCell parameters cell (completedInclusion parameters (Nat.zero_le grade) (values grade)) =
        fieldCellProjection dimension openUnitDisk cell field := by
    exact ((Classical.choose_spec (completion grade)).2 cell).trans
      (congrArg (fieldCellProjection dimension openUnitDisk cell) (sameBase grade))
  have compatible : ∀ lower upper (ordered : lower ≤ upper),
      completedInclusion parameters ordered (values upper) = values lower := by
    intro lower upper ordered
    apply completedInclusion_injective parameters (Nat.zero_le lower)
    apply zeroCell_ext parameters
    intro cell
    have composition := DFunLike.congr_fun
      (completedInclusion_comp (dimension := dimension) parameters ordered (Nat.zero_le lower)) (values upper)
    exact (congrArg (zeroCell parameters cell) composition).trans
      ((cells upper cell).trans (cells lower cell).symm)
  let family : CompatibleAGrades parameters dimension := ⟨values,compatible⟩
  let core := compatibleToCore parameters family
  have coreGrade (grade : ℕ) : aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) core) = values grade :=
    compatibleToCore_component parameters family grade
  refine ⟨core,?_,fun grade => (congrArg norm (coreGrade grade)).trans (norms grade)⟩
  apply (Grad.FullCellKernel.coordinateIsometry dimension openUnitDisk).injective
  apply lp.ext
  funext cell
  change fieldCellProjection dimension openUnitDisk cell (originalSourceMoments parameters core).field =
    fieldCellProjection dimension openUnitDisk cell field
  rw [← originalSourceMoments_zeroCell,coreGrade 0]
  have zero := cells 0 cell
  rw [completedInclusion_self,ContinuousLinearMap.id_apply] at zero
  exact zero

/-- Literal same-cell representative of the recovered original core, with no loss of sigma or gamma. -/
theorem allMixed_sameOriginalCore_cells {dimension : ℕ} (parameters : PhaseParameters)
    (field : StartupL2 dimension) (jets : ∀ grade, Mixed dimension grade openUnitDisk)
    (sameBase : ∀ grade, base dimension grade openUnitDisk (fun index => grade-degree index) (jets grade) = field) :
    ∃ core : ACore parameters dimension,
      (∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
        field point cell = cartesianWeight parameters cell point •
          Grad.ActualScalarWeakEquations.originalCoreCell parameters core cell point) ∧
      ∀ grade, ‖aGradeEta parameters (GradeCore.ofCoreLinear (grade := grade) core)‖ = ‖jets grade‖ := by
  obtain ⟨core,same,norms⟩ := allMixed_sameOriginalCore parameters field jets sameBase
  exact ⟨core,same ▸ originalSourceMoments_same parameters core,norms⟩

end Grad.CartesianCoreRecovery
