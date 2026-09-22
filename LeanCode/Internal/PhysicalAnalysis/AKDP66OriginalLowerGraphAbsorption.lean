import AKDP43FiniteMixedOrderAbsorption
import AKDP61SameOriginalMixedGraphNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers Grad.PDEBootstrap Grad.WeightedJets
open Grad.ActualOriginalSourceMoments Grad.OriginalCartesianTameEstimate Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.SourceCollarCoefficients Grad.WeakTesting.Commutation
open Grad.ActualOriginalSourceFirst Grad.CellWeights

/-- Stored weight-zero coordinates are exactly the original closed-core
weak derivatives, including lower orders. -/
theorem startupOriginalGraph_coordinate {dimension order : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (graph : GraphGrade dimension order 0 openUnitDisk)
    (same : base dimension order openUnitDisk (fun _ => 0) graph=(originalSourceMoments parameters core).field)
    (index : JetIndex order) :
    graph.val index=originalSourceOrderedJoint parameters core (degree index) (derivativeWord index) := by
  have actual := startupRecoveredDerivative_originalCore parameters core graph same index
  rw [Realization.recoveredDerivative_apply,inverseFieldCLM_zero,ContinuousLinearMap.id_apply] at actual
  exact actual

/-- An actual strict lower graph is adjustable against the same original
planar and pure-cell endpoints. The constant precedes every input core. -/
theorem startupOriginalGraph_lower_adjustable (order grade : ℕ) (strict : order<grade)
    (epsilon : ℝ) (positive : 0<epsilon) :
    ∃ constant : ℝ,0≤constant ∧ ∀ (dimension : ℕ) (parameters : PhaseParameters)
      (core : ACore parameters dimension) (graph : GraphGrade dimension order 0 openUnitDisk),
      base dimension order openUnitDisk (fun _ => 0) graph=(originalSourceMoments parameters core).field →
      ‖graph‖≤epsilon*originalPlanarNorm parameters grade core+constant*originalCellNorm parameters grade core := by
  obtain ⟨constant,nonnegative,bounded⟩ := startupFiniteMixedOrders_adjustable grade
    (fun index : JetIndex order => degree index) (fun index => lt_of_le_of_lt (degree_le index) strict)
    (fun _ => 1) (fun _ => zero_le_one) epsilon positive
  refine ⟨constant,nonnegative,?_⟩
  intro dimension parameters core graph same
  have finite := startupFiniteHilbert_norm_le_sum (fun index : JetIndex order => graph.val index)
  change ‖graph‖≤_ at finite
  apply (finite.trans (Finset.sum_le_sum (fun index _ => ?_))).trans (bounded dimension parameters core)
  rw [startupOriginalGraph_coordinate parameters core graph same,
    startupOriginalOrdered_eq_zeroReserve parameters (unitDiskAdmissible parameters),one_mul]
  exact startupOriginalNaturalDerivative_mixedNorm parameters core grade (degree index) 0
    (by have degreeBound := degree_le index; omega) (derivativeWord index)

/-- An arbitrary representative graph of the original weighted field is
controlled by its original norm at the same or higher grade. -/
theorem startupOriginalGraph_norm_le_full {dimension order grade : ℕ} (parameters : PhaseParameters)
    (core : ACore parameters dimension) (graph : GraphGrade dimension order 0 openUnitDisk)
    (same : base dimension order openUnitDisk (fun _ => 0) graph=(originalSourceMoments parameters core).field)
    (allocated : order≤grade) :
    ‖graph‖≤(Fintype.card (JetIndex order) : ℝ)*originalGradeNorm grade core := by
  have finite := startupFiniteHilbert_norm_le_sum (fun index : JetIndex order => graph.val index)
  change ‖graph‖≤_ at finite
  have each (index : JetIndex order) : ‖graph.val index‖≤originalGradeNorm grade core := by
    rw [startupOriginalGraph_coordinate parameters core graph same]
    exact (startupOriginalOrdered_norm parameters (unitDiskAdmissible parameters) core _ _).trans
      (originalGradeNorm_mono ((degree_le index).trans allocated) core)
  exact (finite.trans (Finset.sum_le_sum (fun index _ => each index))).trans_eq
    (by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul])

theorem startupOriginalPlanarNorm_le_full {dimension : ℕ} (parameters : PhaseParameters)
    (grade : ℕ) (core : ACore parameters dimension) :
    originalPlanarNorm parameters grade core≤(Fintype.card (JetIndex grade) : ℝ)*originalGradeNorm grade core := by
  let existsGraph := startupOriginal_reservedGraph parameters core (L := 1) (ell := 1) one_ne_zero one_ne_zero grade 0
  let graph := existsGraph.choose
  have same := existsGraph.choose_spec
  rw [startupOriginalPlanarNorm_eq_graph parameters core graph same]
  exact startupOriginalGraph_norm_le_full parameters core graph same le_rfl

end Grad.CartesianStartup
