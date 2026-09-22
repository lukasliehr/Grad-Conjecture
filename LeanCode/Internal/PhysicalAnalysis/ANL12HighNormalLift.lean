import ANL11SmoothNormalLift
import BL40HighSupport

noncomputable section
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
open Set Filter MeasureTheory
open scoped BigOperators Topology ENNReal
namespace Grad.CircularNormalLift
open Grad.ClosedJets Grad.CartesianState Grad.BoundaryTrace Grad.BoundaryLift Grad.Constraints
open Grad.CircularHighWeak Grad.OrdinaryDiskCalculus Grad.GaugeCoefficients.Radial
local instance (priority := 2000) highLiftUnitSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) := unitNormedSpace grade
local instance (priority := 2000) highLiftBoundarySpace (grade : ℕ) : NormedSpace ℂ (normalBoundaryGrade grade) :=
  (normalBoundaryGrade grade).normedSpace

theorem normalKernel_rotated (mode : ℤ) (angle : ℝ) (point : ClosedDisk) :
    normalKernel mode (rotatedPoint angle point).val = cellExponential mode angle * normalKernel mode point.val := by
  have normEquality : ‖(rotatedPoint angle point).val‖ = ‖point.val‖ := planeRotation_norm angle point.val
  rw [normalKernel, normEquality, boundaryKernel_rotated, normalKernel]
  ring

theorem angularClosedJet_normalMode (mode angular : ℤ) (value : ComplexEuclidean 1) :
    angularClosedJet mode (normalModeJetLinear angular value) =
      if mode = angular then normalModeJetLinear angular value else 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [angularClosedJet_value]
  have integrandLaw : ∀ angle : ℝ,
      angularCharacter mode angle • (normalModeJetLinear angular value).value (rotatedPoint angle point) =
        angularCharacter (mode - angular) angle • (normalKernel angular point.val • value) := by
    intro angle
    change angularCharacter mode angle • (normalKernel angular (rotatedPoint angle point).val • value) = _
    rw [normalKernel_rotated, smul_smul, smul_smul]
    congr 1
    have character : cellExponential angular angle = angularCharacter (-angular) angle := by
      unfold angularCharacter
      rw [neg_neg]
    rw [← mul_assoc, character, angularCharacter_mul, ← sub_eq_add_neg]
  simp_rw [integrandLaw]
  rw [angularCharacter_normalized_integral]
  by_cases equal : mode = angular
  · rw [if_pos (sub_eq_zero.mpr equal), if_pos equal]
    rfl
  · rw [if_neg (fun h => equal (sub_eq_zero.mp h)), if_neg equal]
    rfl

theorem angularClosedJet_finiteNormal (mode : ℤ) (values : NormalFiniteData) :
    angularClosedJet mode (finiteNormalLinear values) = normalModeJetLinear mode (values mode) := by
  change angularClosedJetLinear 1 mode (finiteNormalLinear values) = _
  rw [finiteNormalLinear, Finsupp.lsum_apply, Finsupp.sum, map_sum]
  change (∑ angular ∈ values.support, angularClosedJet mode (normalModeJetLinear angular (values angular))) = _
  simp_rw [angularClosedJet_normalMode]
  rw [Finset.sum_ite_eq]
  by_cases member : mode ∈ values.support
  · rw [if_pos member]
  · rw [if_neg member, Finsupp.notMem_support_iff.mp member, map_zero]

def normalBoundarySelectLinear (grade : ℕ) (mode : ℤ) : normalBoundaryGrade grade →ₗ[ℂ] normalBoundaryGrade grade :=
  (normalBoundaryInto grade).comp ((Finsupp.lsingle mode).comp (normalBoundaryCoefficientCLM grade mode).toLinearMap)

theorem normalBoundarySelectLinear_ambient (grade : ℕ) (mode : ℤ) (field : normalBoundaryGrade grade) :
    (normalBoundarySelectLinear grade mode field).val = lp.single 2 (mode, 0) (field.val (mode, 0)) :=
  normalBoundaryAmbient_single grade mode (field.val (mode, 0))

theorem normalBoundarySelectLinear_bound (grade : ℕ) (mode : ℤ) (field : normalBoundaryGrade grade) :
    ‖normalBoundarySelectLinear grade mode field‖ ≤ ‖field‖ := by
  change ‖(normalBoundarySelectLinear grade mode field).val‖ ≤ ‖field.val‖
  rw [normalBoundarySelectLinear_ambient, lp.norm_single (by norm_num : (0 : ENNReal) < 2)]
  exact lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) field.val (mode, 0)

def normalBoundarySelect (grade : ℕ) (mode : ℤ) : normalBoundaryGrade grade →L[ℂ] normalBoundaryGrade grade :=
  (normalBoundarySelectLinear grade mode).mkContinuous 1
    (fun field => (normalBoundarySelectLinear_bound grade mode field).trans_eq (one_mul _).symm)

theorem normalBoundarySelect_finite (grade : ℕ) (mode : ℤ) (values : NormalFiniteData) :
    normalBoundarySelect grade mode (normalBoundaryInto grade values) =
      normalBoundaryInto grade (Finsupp.single mode (values mode)) := by
  change normalBoundaryInto grade (Finsupp.single mode
    (normalBoundaryCoefficient grade (normalBoundaryInto grade values) mode)) = _
  rw [normalBoundaryInto_coefficient]

theorem normalBoundarySelect_zero (grade : ℕ) (mode : ℤ) (field : normalBoundaryGrade grade)
    (zeroCoefficient : normalBoundaryCoefficient grade field mode = 0) : normalBoundarySelect grade mode field = 0 := by
  change normalBoundaryInto grade (Finsupp.single mode (normalBoundaryCoefficient grade field mode)) = 0
  rw [zeroCoefficient, Finsupp.single_zero, map_zero]

theorem completedNormalLift_mode (grade : ℕ) (gradeBound : 2 ≤ grade) (mode : ℤ) (field : normalBoundaryGrade grade) :
    diskMode mode (unitDiskBulk grade (completedNormalLift grade field)) =
      unitDiskBulk grade (completedNormalLift grade (normalBoundarySelect grade mode field)) := by
  apply isClosed_property (normalBoundaryInto_denseRange grade)
    (isClosed_eq ((diskMode mode).continuous.comp ((unitDiskBulk grade).continuous.comp (completedNormalLift grade).continuous))
      ((unitDiskBulk grade).continuous.comp ((completedNormalLift grade).continuous.comp (normalBoundarySelect grade mode).continuous))) _ field
  intro values
  dsimp only [Function.comp_apply]
  have bulk := (congrArg (fun field : unitDiskSobolev grade => unitDiskBulk grade field)
    (completedNormalLift_finite grade gradeBound values)).trans (unitDiskBulk_core grade (finiteNormalLinear values))
  have selected := congrArg (fun field : normalBoundaryGrade grade => unitDiskBulk grade (completedNormalLift grade field))
    (normalBoundarySelect_finite grade mode values)
  have right := selected.trans ((congrArg (fun field : unitDiskSobolev grade => unitDiskBulk grade field)
    (completedNormalLift_finite grade gradeBound (Finsupp.single mode (values mode)))).trans
      (unitDiskBulk_core grade (finiteNormalLinear (Finsupp.single mode (values mode)))))
  have single : finiteNormalLinear (Finsupp.single mode (values mode)) = normalModeJetLinear mode (values mode) := by
    simp [finiteNormalLinear]
  exact (congrArg (diskMode mode) bulk).trans ((diskMode_core mode (finiteNormalLinear values)).trans
    ((congrArg closedL2Core (angularClosedJet_finiteNormal mode values)).trans
      ((congrArg closedL2Core single).symm.trans right.symm)))

theorem completedNormalLift_high (grade : ℕ) (gradeBound : 2 ≤ grade) (field : normalBoundaryGrade grade)
    (high : ∀ mode ∈ lowAngularModes, normalBoundaryCoefficient grade field mode = 0) :
    unitDiskBulk grade (completedNormalLift grade field) ∈ highDiskL2 := by
  intro mode small
  rw [completedNormalLift_mode grade gradeBound, normalBoundarySelect_zero grade mode field (high mode small), map_zero, map_zero]

theorem normalSmoothLift_high (parameters : PhaseParameters) (data : NormalSmoothBoundary)
    (high : ∀ mode ∈ lowAngularModes, normalBoundaryCoefficient 2 (data.grade 0) mode = 0) :
    closedL2Core (normalSmoothLift parameters data) ∈ highDiskL2 := by
  rw [normalSmoothLift_bulk]
  exact completedNormalLift_high 2 (by omega) (data.grade 0) high

end Grad.CircularNormalLift
