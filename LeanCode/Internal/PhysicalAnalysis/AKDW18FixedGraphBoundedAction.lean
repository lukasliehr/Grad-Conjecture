import AKCC22OriginalFixedAllOrderGraphs
import AKDP10SameOriginalPlanarGraphNorm
import Mathlib.Analysis.Normed.Operator.Banach

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Filter
open scoped Topology
namespace Grad.CartesianStartup
open Grad.WeightedJets Grad.PDEBootstrap Grad.GenericCarriers Grad.ClosedJets

/-- A fixed bounded field operator preserving all weak spatial derivatives
acts linearly on their unique closed graph. -/
def startupPreservedGraphLinear {input output : ℕ}
    (kernel : StartupL2 input →L[ℂ] StartupL2 output) (preserves : StartupPreservesGraph kernel)
    (order weight : ℕ) : GraphGrade input order weight openUnitDisk →ₗ[ℂ] GraphGrade output order weight openUnitDisk where
  toFun field := (preserves order weight field).choose
  map_add' first second := by
    apply base_injective output order openUnitDisk openUnitDisk_isOpen (fun _ => weight)
    change base output order openUnitDisk (fun _ => weight) (preserves order weight (first+second)).choose =
      base output order openUnitDisk (fun _ => weight) ((preserves order weight first).choose+(preserves order weight second).choose)
    rw [(preserves order weight (first+second)).choose_spec]
    simp only [map_add,(preserves order weight first).choose_spec,(preserves order weight second).choose_spec]
  map_smul' scalar field := by
    apply base_injective output order openUnitDisk openUnitDisk_isOpen (fun _ => weight)
    change base output order openUnitDisk (fun _ => weight) (preserves order weight (scalar • field)).choose =
      base output order openUnitDisk (fun _ => weight) (scalar • (preserves order weight field).choose)
    rw [(preserves order weight (scalar • field)).choose_spec]
    simp only [map_smul,(preserves order weight field).choose_spec]

theorem startupPreservedGraphLinear_same {input output : ℕ}
    (kernel : StartupL2 input →L[ℂ] StartupL2 output) (preserves : StartupPreservesGraph kernel)
    (order weight : ℕ) (field : GraphGrade input order weight openUnitDisk) :
    base output order openUnitDisk (fun _ => weight) (startupPreservedGraphLinear kernel preserves order weight field)=
      kernel (base input order openUnitDisk (fun _ => weight) field) :=
  (preserves order weight field).choose_spec

/-- Closedness of the weak graph makes this SAME fixed action bounded;
the resulting constant is independent of every original core and phase. -/
def startupPreservedGraphCLM {input output : ℕ}
    (kernel : StartupL2 input →L[ℂ] StartupL2 output) (preserves : StartupPreservesGraph kernel)
    (order weight : ℕ) : GraphGrade input order weight openUnitDisk →L[ℂ] GraphGrade output order weight openUnitDisk where
  toLinearMap := startupPreservedGraphLinear kernel preserves order weight
  cont := by
    apply LinearMap.continuous_of_seq_closed_graph
    intro sequence first second firstLimit secondLimit
    apply base_injective output order openUnitDisk openUnitDisk_isOpen (fun _ => weight)
    have outputLimit := ((base output order openUnitDisk (fun _ => weight)).continuous.tendsto second).comp secondLimit
    have inputLimit := ((kernel.continuous.comp (base input order openUnitDisk (fun _ => weight)).continuous).tendsto first).comp firstLimit
    have sameLimit : Tendsto
        ((base output order openUnitDisk (fun _ => weight)) ∘ (startupPreservedGraphLinear kernel preserves order weight ∘ sequence))
        atTop (𝓝 (kernel (base input order openUnitDisk (fun _ => weight) first))) := by
      simpa only [Function.comp_def,startupPreservedGraphLinear_same] using inputLimit
    exact (tendsto_nhds_unique outputLimit sameLimit).trans
      (startupPreservedGraphLinear_same kernel preserves order weight first).symm

theorem startupPreservedGraphCLM_same {input output : ℕ}
    (kernel : StartupL2 input →L[ℂ] StartupL2 output) (preserves : StartupPreservesGraph kernel)
    (order weight : ℕ) (field : GraphGrade input order weight openUnitDisk) :
    base output order openUnitDisk (fun _ => weight) (startupPreservedGraphCLM kernel preserves order weight field)=
      kernel (base input order openUnitDisk (fun _ => weight) field) :=
  startupPreservedGraphLinear_same kernel preserves order weight field

end Grad.CartesianStartup
