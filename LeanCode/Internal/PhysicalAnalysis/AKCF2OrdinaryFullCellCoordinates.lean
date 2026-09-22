import AKCF1NativeAnnularCutoffJet
import CellFieldExchange
import GC18APWeakCore
import JetInclusionsProof

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped ContDiff Topology BigOperators
namespace Grad.NativePuncturedGraph
open Grad.ClosedJets Grad.CartesianState Grad.CartesianCoreRecovery Grad.PDEBootstrap
open Grad.GenericCarriers Grad.CartesianStartup Grad.CellWeights

variable {dimension : ℕ} (field : OrdinaryCoefficientCore dimension)

def ordinaryDerivativeCoordinate (weight : ℕ) (index : ℕ×ℕ) (cell : ℤ) : DiskL2 dimension :=
  (cellFrequency cell : ℂ)^weight • closedContinuousToDiskL2 (closedMultiDerivative (field.val cell) index)

theorem ordinaryDerivativeCoordinate_summable (weight : ℕ) (index : ℕ×ℕ) :
    Summable (fun cell => ‖ordinaryDerivativeCoordinate field weight index cell‖^2) := by
  let grade := weight+cartesianOrder index
  let selected : GradeMultiIndex grade := ⟨(⟨index.1,by dsimp [grade,cartesianOrder]; omega⟩,
    ⟨index.2,by dsimp [grade,cartesianOrder]; omega⟩),by dsimp [grade,cartesianOrder]; omega⟩
  have same (cell : ℤ) : ordinaryDerivativeCoordinate field weight index cell=
      ordinaryRawGradeCoordinates grade field.val cell selected := by
    change (cellFrequency cell : ℂ)^weight • closedContinuousToDiskL2 (closedMultiDerivative (field.val cell) index)=
      (cellFrequency cell : ℂ)^(grade-cartesianOrder index) • closedContinuousToDiskL2 (closedMultiDerivative (field.val cell) index)
    have powers : grade-cartesianOrder index=weight := by dsimp only [grade]; omega
    rw [powers]
  have summable := (memlp_iff_summable_sq (ordinaryRawGradeCoordinates grade field.val)).mp (field.property grade)
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ summable
  intro cell
  rw [same]
  exact pow_le_pow_left₀ (norm_nonneg _) (PiLp.norm_apply_le (ordinaryRawGradeCoordinates grade field.val cell) selected) 2

/-- The actual complete integer-cell carrier of each ordinary derivative and
cell power, assembled with the accepted full-cell isometry. -/
def ordinaryDerivativeJoint (weight : ℕ) (index : ℕ×ℕ) : StartupL2 dimension :=
  (Grad.FullCellKernel.exchange dimension openUnitDisk).symm
    ⟨ordinaryDerivativeCoordinate field weight index,
      (memlp_iff_summable_sq _).mpr (ordinaryDerivativeCoordinate_summable field weight index)⟩

theorem ordinaryDerivativeJoint_coordinate (weight : ℕ) (index : ℕ×ℕ) (cell : ℤ) :
    fieldCellProjection dimension openUnitDisk cell (ordinaryDerivativeJoint field weight index)=
      ordinaryDerivativeCoordinate field weight index cell :=
  Grad.FullCellKernel.exchange_symm_coordinate dimension openUnitDisk _ cell

theorem ordinaryDerivativeJoint_same (weight : ℕ) (index : ℕ×ℕ) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ cell : ℤ,
      ordinaryDerivativeJoint field weight index point cell=
        (cellFrequency cell : ℂ)^weight • closedDiskLift (closedMultiDerivative (field.val cell) index) point := by
  have coefficients := ae_all_iff.mpr (fun cell : ℤ =>
    (Lp.coeFn_smul ((cellFrequency cell : ℂ)^weight)
      (closedContinuousToDiskL2 (closedMultiDerivative (field.val cell) index))).and
      (closedContinuousToDiskL2_ae (closedMultiDerivative (field.val cell) index)))
  filter_upwards [fieldCellProjection_ae dimension openUnitDisk (ordinaryDerivativeJoint field weight index),coefficients]
    with point projection coefficients
  intro cell
  rw [←projection cell,ordinaryDerivativeJoint_coordinate]
  exact (coefficients cell).1.trans (congrArg (fun value => (cellFrequency cell : ℂ)^weight • value) (coefficients cell).2)

theorem ordinaryDerivativeJoint_inverse (weight : ℕ) (index : ℕ×ℕ) :
    inverseFieldCLM dimension openUnitDisk weight (ordinaryDerivativeJoint field weight index)=ordinaryDerivativeJoint field 0 index := by
  apply Lp.ext
  filter_upwards [inverseFieldCLM_coordinate dimension openUnitDisk weight (ordinaryDerivativeJoint field weight index),
    ordinaryDerivativeJoint_same field weight index,ordinaryDerivativeJoint_same field 0 index] with point inverse weighted plain
  apply lp.ext
  funext cell
  rw [inverse cell,weighted cell,plain cell]
  simp only [pow_zero,one_smul,smul_smul,inverseFactor]
  have nonzero : (cellWeight cell : ℂ)^weight≠0 := pow_ne_zero weight (Complex.ofReal_ne_zero.mpr (cellWeight_pos cell).ne')
  change (((cellWeight cell : ℂ)^weight)⁻¹*(cellWeight cell : ℂ)^weight) • _=_
  rw [inv_mul_cancel₀ nonzero,one_smul]

end Grad.NativePuncturedGraph
