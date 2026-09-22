import AKDP8SameSignedOriginalNorm

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.ClosedJets Grad.CartesianState Grad.PDEBootstrap Grad.GenericCarriers Grad.WeightedJets
open Grad.ActualOriginalSourceMoments Grad.ActualOriginalSourceFirst Grad.NonlinearProduct
open Grad.OriginalCartesianTameEstimate Grad.CartesianCoreRecovery Grad.CellWeights
open Grad.GaugeCoefficients.Physical.RadialLedger

/-- Each coordinate of the SAME weight-zero graph is the literal ordinary
phase-weighted spatial derivative in the original planar endpoint. -/
theorem startupOriginalPlanarGraph_coordinate {dimension grade : ℕ}
    (parameters : PhaseParameters) (core : ACore parameters dimension)
    (jet : GraphGrade dimension grade 0 openUnitDisk)
    (same : base dimension grade openUnitDisk (fun _ => 0) jet = (originalSourceMoments parameters core).field)
    (cell : ℤ) (index : GradeMultiIndex grade) :
    apMassRow 1 grade (phaseWeightedJet parameters cell (core.val cell)) index =
      fieldCellProjection dimension openUnitDisk cell (jet.val (originalJetIndexEquiv grade index)) := by
  have recovered := startupRecoveredDerivative_originalCore parameters core jet same (originalJetIndexEquiv grade index)
  rw [Realization.recoveredDerivative_apply,inverseFieldCLM_zero,ContinuousLinearMap.id_apply] at recovered
  rw [recovered,originalSourceOrderedJoint_coordinate]
  change (1 : ℂ)^_ • _ = _
  simp only [one_pow,one_smul]
  rfl

/-- Exact planar endpoint norm of the genuine original weighted core and
its stored weak graph, including every lower derivative once. -/
theorem startupOriginalPlanarNorm_eq_graph {dimension grade : ℕ}
    (parameters : PhaseParameters) (core : ACore parameters dimension)
    (jet : GraphGrade dimension grade 0 openUnitDisk)
    (same : base dimension grade openUnitDisk (fun _ => 0) jet = (originalSourceMoments parameters core).field) :
    originalPlanarNorm parameters grade core = ‖jet‖ := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (norm_nonneg _)).mp
  change originalPlanarNorm parameters grade core^2 = ‖jet‖^2
  rw [originalPlanarNorm_sq,jet_norm_sq]
  simp_rw [PiLp.norm_sq_eq_of_L2,startupOriginalPlanarGraph_coordinate parameters core jet same]
  rw [Summable.tsum_finsetSum (fun index _ =>
    Grad.CellEnergy.cellEnergy_summable dimension openUnitDisk (jet.val (originalJetIndexEquiv grade index)))]
  simp_rw [← Grad.CellEnergy.field_norm_sq_eq_tsum]
  exact Equiv.sum_comp (originalJetIndexEquiv grade) (fun index => ‖jet.val index‖^2)

end Grad.CartesianStartup
