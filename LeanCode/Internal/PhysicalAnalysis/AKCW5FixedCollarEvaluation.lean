import AKCW2OriginalCollarDerivativePackets
import AKCW4OriginalAllGradeParameterSmoothness
import Mathlib.Analysis.Calculus.FDeriv.Partial

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 600000
open Set Filter
open scoped ContDiff Topology
namespace Grad.OriginalParameterEvaluation
open Grad.CartesianState Grad.ClosedJets Grad.DiskExtension.Operator

/-- One fixed collar, independent of parameter and derivative order. -/
def originalOpenCollar : Set SpatialCell := {point | ‖planarPart point‖ < (4/3 : ℝ)}

theorem originalOpenCollar_isOpen : IsOpen originalOpenCollar :=
  isOpen_lt continuous_planarPart.norm continuous_const

def fixedCollarRetraction (point : SpatialPlane) : PhysicalCollar :=
  ⟨(4/3 : ℝ) • (radialRetraction ((3/4 : ℝ) • point)).val, by
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs]
    have bounded := (radialRetraction ((3/4 : ℝ) • point)).property
    change ‖(radialRetraction ((3/4 : ℝ) • point)).val‖≤1 at bounded
    norm_num only [abs_of_pos (by norm_num : (0:ℝ)<4/3)]
    nlinarith⟩

theorem fixedCollarRetraction_continuous : Continuous fixedCollarRetraction := by
  have scaled : Continuous (fun point : SpatialPlane => (3/4 : ℝ) • point) :=
    (continuous_id : Continuous (id : SpatialPlane → SpatialPlane)).const_smul (3/4 : ℝ)
  apply Continuous.subtype_mk
  exact (continuous_subtype_val.comp (continuous_radialRetraction.comp scaled)).const_smul (4/3 : ℝ)

theorem fixedCollarRetraction_same (point : SpatialPlane) (inside : ‖point‖≤(4/3 : ℝ)) :
    (fixedCollarRetraction point).val=point := by
  have scaled : ((3/4 : ℝ) • point)∈closedUnitDisk := by
    change ‖(3/4 : ℝ) • point‖≤1
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ)<3/4)]
    nlinarith
  change (4/3 : ℝ) • (radialRetraction ((3/4 : ℝ) • point)).val=point
  rw [radialRetraction_val_of_mem _ scaled, smul_smul]
  norm_num

def fixedCollarPoint (point : SpatialCell) : PhysicalCollarDomain :=
  (fixedCollarRetraction (planarPart point), (point 2 : CellCircle))

theorem fixedCollarPoint_continuous : Continuous fixedCollarPoint := by
  unfold fixedCollarPoint
  exact (fixedCollarRetraction_continuous.comp continuous_planarPart).prodMk (by fun_prop)

variable {dimension : ℕ} (parameters : PhaseParameters)

/-- An ambient continuous representative used only to handle the fixed
collar as a subset of the Euclidean spatial domain. -/
def originalClampedDerivative (order : ℕ) (field : ACore parameters dimension)
    (point : SpatialCell) : SpatialCell [×order]→L[ℝ] ComplexEuclidean dimension :=
  originalCollarDerivative parameters order field (fixedCollarPoint point)

theorem originalClampedDerivative_same (order : ℕ) (field : ACore parameters dimension)
    (point : SpatialCell) (inside : point∈originalOpenCollar) :
    originalClampedDerivative parameters order field point=
      ambientHigherDerivative (originalPhysicalClosedJet parameters field) order point := by
  have collar : (fixedCollarRetraction (planarPart point)).val=planarPart point :=
    fixedCollarRetraction_same _ inside.le
  have fundamental := physicalCollar_mem_fundamentalIocSquare
    (fixedCollarRetraction (planarPart point))
  rw [collar] at fundamental
  have assembled : assembleSpatialCell (planarPart point) (point 2)=point := by
    ext index
    fin_cases index <;> rfl
  apply continuousMultilinearMap_ext_spatialCellBasis
  intro word
  change torusPhysicalOperatorDerivative (periodizedExtension (originalPhysicalClosedJet parameters field)) order
    (physicalCollarToTorus (fixedCollarPoint point)) _=_
  rw [torusPhysicalOperatorDerivative_basis]
  have torusEquality : physicalCollarToTorus (fixedCollarPoint point)=
      torusCellPoint (assembleSpatialCell (planarPart point) (point 2)) := by
    unfold physicalCollarToTorus fixedCollarPoint torusCellPoint
    rw [collar]
    rfl
  rw [torusEquality, periodized_mixedDerivative_eq_ambient_on_fundamental
    (originalPhysicalClosedJet parameters field) word (planarPart point) (point 2) fundamental]
  unfold mixedCartesianDerivative
  rw [assembled, ← ambientHigherDerivative_eq_iteratedFDeriv_ambient]

theorem originalClampedDerivative_joint_continuous
    {Parameter : Type*} [NormedAddCommGroup Parameter] [NormedSpace ℝ Parameter]
    {domain : Set Parameter} (order : ℕ) (field : Parameter → ACore parameters dimension)
    (smooth : ContDiffOn ℝ ∞ (completedCoreBranch parameters field (order+3)) domain) :
    ContinuousOn (fun point : Parameter × SpatialCell =>
      originalClampedDerivative parameters order (field point.1) point.2) (domain ×ˢ univ) := by
  have packet := (originalCollarDerivative_parameter_smooth parameters field smooth).continuousOn
  exact continuous_eval.comp_continuousOn
    ((packet.comp continuous_fst.continuousOn (fun point member => member.1)).prodMk
      (fixedCollarPoint_continuous.comp continuous_snd).continuousOn)

end Grad.OriginalParameterEvaluation
