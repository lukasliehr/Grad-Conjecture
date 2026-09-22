import AKAW20ActualSourceNativeMoments

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Set Filter MeasureTheory
open scoped BigOperators ENNReal Topology
namespace Grad.ActualNativeCellMoments
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace Grad.SourceCollarCoefficients
open Grad.ActualSmoothPhysicalField Grad.AnnularWeightedSmoothness Grad.AnnularKernelContinuity Grad.AnnularKernelL2
open Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction Grad.ActualPhysicalField Grad.BoundaryKernelAction
open Grad.BoundaryLift
open Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Ledger Grad.GaugeCoefficients.Physical.Allocation

theorem covariantCurve_uniformBound (parameters : PhaseParameters) (length compact : ℝ)
    (state : AnnularReconstructionState parameters length compact) (grade : ℕ) :
    ∃ constant : ℝ, 0 ≤ constant ∧ ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
      (row : DivisionRow 7 lower) (curves : SmoothLowPhysicalRow parameters lower positive row) (radius : ℝ),
      ‖(curves.covariant parameters length compact lower positive bounded state).cartesianCovariant.curve grade radius‖ ≤
        constant * ‖curves.curve grade radius‖ := by
  have regular := radialNormalizedCovariantKernel_regular parameters length compact state
  obtain ⟨bound,nonnegative,estimate⟩ := regular.2 grade
  refine ⟨‖nativeCovariantRotation parameters grade‖ * bound, by positivity, ?_⟩
  intro lower positive bounded row curves radius
  have polar := actionCurve_norm parameters _ regular grade bound estimate lower positive bounded
    (radialNormalizedCovariantKernel_conjugated_smooth parameters length compact state lower positive bounded) curves radius
  rw [nativeCovariantRotation_same]
  exact ((nativeCovariantRotation parameters grade).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_left polar (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

def nativeXiProjection (parameters : PhaseParameters) : CellL2 7 →L[ℂ] CellL2 1 :=
  coefficientOperator parameters 0 (Equiv.refl _) (fun _ => matrixUnit (0 : Fin 1) (3 : Fin 7))
    (norm_nonneg _) (fun _ => le_rfl)

theorem xiCurve_uniformBound {parameters : PhaseParameters} {lower : ℝ} {positive : 0 < lower}
    {row : DivisionRow 7 lower} (curves : SmoothLowPhysicalRow parameters lower positive row) (grade : ℕ) (radius : ℝ) :
    ‖(curves.bulkUnit (0 : Fin 1) (3 : Fin 7)).curve grade radius‖ ≤
      ‖nativeXiProjection parameters‖ * ‖curves.curve grade radius‖ :=
  (nativeXiProjection parameters).le_opNorm _

end Grad.ActualNativeCellMoments
