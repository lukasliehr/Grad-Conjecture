import FC2Proof
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section

open Set MeasureTheory
open scoped ENNReal BigOperators Topology

namespace Grad.CartesianState

open Grad.ClosedJets

instance closedJetZeroInstance (dimension : ℕ) : Zero (ClosedJet dimension) :=
  ⟨closedJetZero dimension⟩

instance closedJetAddInstance (dimension : ℕ) : Add (ClosedJet dimension) :=
  ⟨closedJetAdd⟩

instance closedJetNegInstance (dimension : ℕ) : Neg (ClosedJet dimension) :=
  ⟨fun field => closedJetSmul (-1) field⟩

instance closedJetSubInstance (dimension : ℕ) : Sub (ClosedJet dimension) :=
  ⟨fun first second => first + -second⟩

instance closedJetNatSMulInstance (dimension : ℕ) : SMul ℕ (ClosedJet dimension) :=
  ⟨nsmulRec⟩

instance closedJetIntSMulInstance (dimension : ℕ) : SMul ℤ (ClosedJet dimension) :=
  ⟨zsmulRec⟩

instance closedJetComplexSMulInstance (dimension : ℕ) : SMul ℂ (ClosedJet dimension) :=
  ⟨closedJetSmul⟩

@[simp] theorem closedJet_value_zero (dimension : ℕ) :
    (0 : ClosedJet dimension).value = 0 := rfl

@[simp] theorem closedJet_value_add {dimension : ℕ} (first second : ClosedJet dimension) :
    (first + second).value = first.value + second.value := rfl

@[simp] theorem closedJet_value_neg {dimension : ℕ} (field : ClosedJet dimension) :
    (-field).value = -field.value := by
  apply ContinuousMap.ext
  intro point
  change (-1 : ℂ) • field.value point = -field.value point
  exact neg_one_smul ℂ (field.value point)

@[simp] theorem closedJet_value_smul {dimension : ℕ} (scalar : ℂ)
    (field : ClosedJet dimension) :
    (scalar • field).value = scalar • field.value := rfl

instance closedJetAddCommGroup (dimension : ℕ) : AddCommGroup (ClosedJet dimension) where
  add_assoc first second third := by
    apply closedJet_eq_of_value_eq
    ext point
    exact add_assoc _ _ _
  zero_add field := by
    apply closedJet_eq_of_value_eq
    ext point
    exact zero_add _
  add_zero field := by
    apply closedJet_eq_of_value_eq
    ext point
    exact add_zero _
  add_comm first second := by
    apply closedJet_eq_of_value_eq
    ext point
    exact add_comm _ _
  neg_add_cancel field := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    change (-1 : ℂ) • field.value point + field.value point = 0
    rw [neg_one_smul, neg_add_cancel]

instance closedJetModule (dimension : ℕ) : Module ℂ (ClosedJet dimension) where
  one_smul field := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact one_smul ℂ (field.value point)
  mul_smul first second field := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact mul_smul first second (field.value point)
  smul_zero scalar := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact smul_zero scalar
  smul_add scalar first second := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact smul_add scalar (first.value point) (second.value point)
  add_smul first second field := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact add_smul first second (field.value point)
  zero_smul field := by
    apply closedJet_eq_of_value_eq
    apply ContinuousMap.ext
    intro point
    exact zero_smul ℂ (field.value point)

theorem closedMultiDerivative_add {dimension : ℕ} (first second : ClosedJet dimension)
    (index : CartesianMultiIndex) :
    closedMultiDerivative (first + second) index =
      closedMultiDerivative first index + closedMultiDerivative second index := by
  change closedDerivative (closedJetAdd first second) (cartesianOrder index)
      (cartesianMultiIndexWord index) = _
  rw [closedJetAdd_derivative]
  rfl

theorem closedMultiDerivative_smul {dimension : ℕ} (scalar : ℂ)
    (field : ClosedJet dimension) (index : CartesianMultiIndex) :
    closedMultiDerivative (scalar • field) index =
      scalar • closedMultiDerivative field index := by
  change closedDerivative (closedJetSmul scalar field) (cartesianOrder index)
      (cartesianMultiIndexWord index) = _
  rw [closedJetSmul_derivative]
  rfl

theorem closedDiskLift_continuousMap_add {dimension : ℕ}
    (first second : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    closedDiskLift (first + second) = closedDiskLift first + closedDiskLift second := by
  funext point
  by_cases membership : point ∈ closedUnitDisk <;>
    simp [closedDiskLift, membership]

theorem closedDiskLift_continuousMap_smul {dimension : ℕ} (scalar : ℂ)
    (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    closedDiskLift (scalar • field) = scalar • closedDiskLift field := by
  funext point
  by_cases membership : point ∈ closedUnitDisk <;>
    simp [closedDiskLift, membership]

theorem closedDiskLift_continuousOn_open {dimension : ℕ}
    (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    ContinuousOn (closedDiskLift field) openUnitDisk := by
  rw [continuousOn_iff_continuous_domRestrict]
  have equality : openUnitDisk.domRestrict (closedDiskLift field) =
      fun point : OpenDisk => field (openDiskInclusion point) := by
    funext point
    simp [Set.domRestrict, closedDiskLift, openDiskInclusion,
      openDiskMembershipClosed point.val point.property]
  rw [equality]
  exact field.continuous.comp (continuous_subtype_val.subtype_mk _)

instance diskFiniteMeasure : IsFiniteMeasure (volume.restrict openUnitDisk) := by
  rw [isFiniteMeasure_restrict, openUnitDisk_eq_ball]
  exact measure_ball_lt_top.ne

instance closedDiskCompactSpace : CompactSpace ClosedDisk := by
  apply isCompact_iff_compactSpace.mp
  rw [closedUnitDisk_eq_closedBall]
  exact isCompact_closedBall 0 1

/-- The actual area-measure `L²(D,E)` space for the open Euclidean unit disk. -/
abbrev DiskL2 (dimension : ℕ) :=
  Lp (ComplexEuclidean dimension) 2 (volume.restrict openUnitDisk)

theorem closedContinuous_memLp {dimension : ℕ}
    (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    MemLp (closedDiskLift field) 2 (volume.restrict openUnitDisk) := by
  let bounded : BoundedContinuousFunction ClosedDisk (ComplexEuclidean dimension) :=
    BoundedContinuousFunction.mkOfCompact field
  refine MemLp.of_bound
    ((closedDiskLift_continuousOn_open field).aemeasurable
      openUnitDisk_isOpen.measurableSet |>.aestronglyMeasurable) ‖bounded‖ ?_
  filter_upwards [ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point membership
  change ‖closedDiskLift field point‖ ≤ ‖bounded‖
  rw [show closedDiskLift field point = field
    ⟨point, openDiskMembershipClosed point membership⟩ by
      simp [closedDiskLift, openDiskMembershipClosed point membership]]
  exact bounded.norm_coe_le_norm _

/-- A continuous boundary jet, represented as its actual `L²(D,E)` equivalence class. -/
def closedContinuousToDiskL2 {dimension : ℕ}
    (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) : DiskL2 dimension :=
  (closedContinuous_memLp field).toLp (closedDiskLift field)

theorem closedContinuousToDiskL2_ae {dimension : ℕ}
    (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,
      closedContinuousToDiskL2 field point = closedDiskLift field point :=
  (closedContinuous_memLp field).coeFn_toLp

theorem closedContinuousToDiskL2_add {dimension : ℕ}
    (first second : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    closedContinuousToDiskL2 (first + second) =
      closedContinuousToDiskL2 first + closedContinuousToDiskL2 second := by
  apply Lp.ext
  filter_upwards [closedContinuousToDiskL2_ae (first + second),
    closedContinuousToDiskL2_ae first, closedContinuousToDiskL2_ae second,
    Lp.coeFn_add (closedContinuousToDiskL2 first) (closedContinuousToDiskL2 second)]
      with point added firstAt secondAt targetAdd
  simp only [Pi.add_apply] at targetAdd
  rw [added, targetAdd, firstAt, secondAt]
  exact congrFun (closedDiskLift_continuousMap_add first second) point

theorem closedContinuousToDiskL2_smul {dimension : ℕ} (scalar : ℂ)
    (field : ContinuousMap ClosedDisk (ComplexEuclidean dimension)) :
    closedContinuousToDiskL2 (scalar • field) =
      scalar • closedContinuousToDiskL2 field := by
  apply Lp.ext
  filter_upwards [closedContinuousToDiskL2_ae (scalar • field),
    closedContinuousToDiskL2_ae field,
    Lp.coeFn_smul scalar (closedContinuousToDiskL2 field)]
      with point scaled fieldAt targetSmul
  simp only [Pi.smul_apply] at targetSmul
  rw [scaled, targetSmul, fieldAt]
  exact congrFun (closedDiskLift_continuousMap_smul scalar field) point

/-- The actual `L²(D,E)` representative of one Cartesian derivative of a closed jet. -/
def closedDerivativeL2 {dimension : ℕ} (index : CartesianMultiIndex) :
    ClosedJet dimension →ₗ[ℂ] DiskL2 dimension where
  toFun field := closedContinuousToDiskL2 (closedMultiDerivative field index)
  map_add' first second := by
    rw [closedMultiDerivative_add, closedContinuousToDiskL2_add]
  map_smul' scalar field := by
    rw [closedMultiDerivative_smul]
    exact closedContinuousToDiskL2_smul scalar (closedMultiDerivative field index)

theorem closedDerivativeL2_ae {dimension : ℕ} (field : ClosedJet dimension)
    (index : CartesianMultiIndex) :
    ∀ᵐ point ∂volume.restrict openUnitDisk,
      closedDerivativeL2 index field point =
        closedDiskLift (closedMultiDerivative field index) point :=
  closedContinuousToDiskL2_ae _

end Grad.CartesianState
