import AKDP45ActualMatrixAdjustableCellEndpoint
import AKDP35ActualPrincipalRankRemainderNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1300000
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap
open Grad.ActualOriginalSourceMoments Grad.OriginalCartesianTameEstimate

/-- The genuine original natural-cell moment is a linear map on ACore. -/
def startupOriginalNaturalMomentLinear {dimension : ℕ} (parameters : PhaseParameters) (grade : ℕ) :
    ACore parameters dimension →ₗ[ℂ] StartupL2 dimension where
  toFun core := originalSourceJointField parameters core grade
  map_add' first second := by
    apply Grad.CellWeights.fields_ext dimension openUnitDisk
    intro cell
    rw [map_add,startupOriginalJoint_projection,startupOriginalJoint_projection,startupOriginalJoint_projection]
    change cartesianGradeCoordinates parameters grade (first+second) cell (zeroGradeIndex grade)=
      cartesianGradeCoordinates parameters grade first cell (zeroGradeIndex grade)+
        cartesianGradeCoordinates parameters grade second cell (zeroGradeIndex grade)
    rw [map_add]
    rfl
  map_smul' scalar core := by
    apply Grad.CellWeights.fields_ext dimension openUnitDisk
    intro cell
    rw [map_smul,startupOriginalJoint_projection,startupOriginalJoint_projection]
    change cartesianGradeCoordinates parameters grade (scalar • core) cell (zeroGradeIndex grade)=
      scalar • cartesianGradeCoordinates parameters grade core cell (zeroGradeIndex grade)
    rw [map_smul]
    rfl

theorem startupOriginalNaturalMomentLinear_norm {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (core : ACore parameters dimension) :
    ‖startupOriginalNaturalMomentLinear parameters grade core‖=originalCellNorm parameters grade core :=
  (originalCellNorm_eq_actualMoment parameters core (startupOriginalAllMoments parameters core)
    (startupOriginalAllMoments_projection parameters core) grade).symm

theorem startupOriginalCellNorm_add {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (first second : ACore parameters dimension) :
    originalCellNorm parameters grade (first+second)≤
      originalCellNorm parameters grade first+originalCellNorm parameters grade second := by
  simp only [←startupOriginalNaturalMomentLinear_norm,map_add]
  exact norm_add_le _ _

theorem startupOriginalCellNorm_sub {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (first second : ACore parameters dimension) :
    originalCellNorm parameters grade (first-second)≤
      originalCellNorm parameters grade first+originalCellNorm parameters grade second := by
  simp only [←startupOriginalNaturalMomentLinear_norm,map_sub]
  exact norm_sub_le _ _

theorem startupOriginalCellNorm_smul {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (scalar : ℂ) (core : ACore parameters dimension) :
    originalCellNorm parameters grade (scalar • core)=‖scalar‖*originalCellNorm parameters grade core := by
  simp only [←startupOriginalNaturalMomentLinear_norm,map_smul,norm_smul]

end Grad.CartesianStartup
