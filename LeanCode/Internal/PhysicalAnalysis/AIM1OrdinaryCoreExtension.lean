import ANG24OrdinarySobolevSource
import AIC7DiskScalarMultiplication

noncomputable section
namespace Grad.OrdinaryDiskCalculus
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak
open Grad.GaugeCoefficients.Physical.RadialLedger

abbrev unitNormedSpace (grade : ℕ) : NormedSpace ℂ (unitDiskSobolev grade) :=
  (unitDiskSobolev grade).normedSpace
attribute [local instance] unitNormedSpace

local instance unitComplete (grade : ℕ) : CompleteSpace (unitDiskSobolev grade) := by
  unfold unitDiskSobolev
  infer_instance

theorem unitDiskCoreInto_injective (grade : ℕ) : Function.Injective (unitDiskCoreInto grade) := by
  intro first second equality
  apply closedL2Core_injective
  exact (unitDiskBulk_core grade first).symm.trans
    ((congrArg (unitDiskBulk grade) equality).trans (unitDiskBulk_core grade second))

/-- Extend a proved ordinary disk core estimate without any weighted
analytic admissibility assumption. -/
theorem unitCore_extension (input output : ℕ) (mapping : ClosedJet 1 →ₗ[ℂ] ClosedJet 1)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (bound : ∀ core, ‖unitSobolevRow output (mapping core)‖ ≤ constant * ‖unitSobolevRow input core‖) :
    ∃ completed : unitDiskSobolev input →L[ℂ] unitDiskSobolev output,
      (∀ core, completed (unitDiskCoreInto input core) = unitDiskCoreInto output (mapping core)) ∧
      (∀ field, ‖completed field‖ ≤ constant * ‖field‖) := by
  apply @apDense_extension (ClosedJet 1) (unitDiskSobolev input) (unitDiskSobolev output)
    inferInstance inferInstance
    (inferInstance : NormedAddCommGroup (unitDiskSobolev input)) (unitNormedSpace input)
    (inferInstance : NormedAddCommGroup (unitDiskSobolev output)) (unitNormedSpace output)
    (unitComplete output) (unitDiskCoreInto input) (unitDiskCoreInto_injective input)
    (unitDiskCoreInto_denseRange input) ((unitDiskCoreInto output).comp mapping)
    constant nonnegative
  intro core
  change ‖unitDiskCoreInto output (mapping core)‖ ≤ constant * ‖unitDiskCoreInto input core‖
  simpa only [unitDiskCore_norm] using bound core

end Grad.OrdinaryDiskCalculus
