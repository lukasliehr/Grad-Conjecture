import AIM2CompletedMultiplication

noncomputable section
namespace Grad.OrdinaryDiskCalculus
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.Compensated (partialJetLinear)
attribute [local instance] unitNormedSpace

theorem unitPartial_exists (grade : ℕ) (direction : Fin 2) :
    ∃ completed : unitDiskSobolev (grade + 1) →L[ℂ] unitDiskSobolev grade,
      (∀ core, completed (unitDiskCoreInto (grade + 1) core) = unitDiskCoreInto grade (partialJet direction core)) ∧
      (∀ field, ‖completed field‖ ≤ Real.sqrt (Fintype.card (DerivativeIndex grade)) * ‖field‖) :=
  unitCore_extension (grade + 1) grade (partialJetLinear 1 direction) _
    (Real.sqrt_nonneg _) (Grad.CircularHighWeak.unitPartial_bound grade direction)

def unitPartial (grade : ℕ) (direction : Fin 2) : unitDiskSobolev (grade + 1) →L[ℂ] unitDiskSobolev grade :=
  (unitPartial_exists grade direction).choose

theorem unitPartial_core (grade : ℕ) (direction : Fin 2) (core : ClosedJet 1) :
    unitPartial grade direction (unitDiskCoreInto (grade + 1) core) = unitDiskCoreInto grade (partialJet direction core) :=
  (unitPartial_exists grade direction).choose_spec.1 core

theorem unitPartial_bound (grade : ℕ) (direction : Fin 2) (field : unitDiskSobolev (grade + 1)) :
    ‖unitPartial grade direction field‖ ≤ Real.sqrt (Fintype.card (DerivativeIndex grade)) * ‖field‖ :=
  (unitPartial_exists grade direction).choose_spec.2 field

theorem unitLower_exists {low high : ℕ} (ordered : low ≤ high) :
    ∃ completed : unitDiskSobolev high →L[ℂ] unitDiskSobolev low,
      (∀ core, completed (unitDiskCoreInto high core) = unitDiskCoreInto low core) ∧
      (∀ field, ‖completed field‖ ≤ apLoweringConstant low * ‖field‖) :=
  unitCore_extension high low (LinearMap.id) _ (apLoweringConstant_nonnegative low)
    (apLowerRow_bound 1 0 0 1 ordered 0)

def unitLower {low high : ℕ} (ordered : low ≤ high) : unitDiskSobolev high →L[ℂ] unitDiskSobolev low :=
  (unitLower_exists ordered).choose

theorem unitLower_core {low high : ℕ} (ordered : low ≤ high) (core : ClosedJet 1) :
    unitLower ordered (unitDiskCoreInto high core) = unitDiskCoreInto low core :=
  (unitLower_exists ordered).choose_spec.1 core

theorem unitLower_bound {low high : ℕ} (ordered : low ≤ high) (field : unitDiskSobolev high) :
    ‖unitLower ordered field‖ ≤ apLoweringConstant low * ‖field‖ :=
  (unitLower_exists ordered).choose_spec.2 field

theorem unitLower_bulk {low high : ℕ} (ordered : low ≤ high) (field : unitDiskSobolev high) :
    unitDiskBulk low (unitLower ordered field) = unitDiskBulk high field := by
  apply isClosed_property (unitDiskCoreInto_denseRange high)
    (isClosed_eq ((unitDiskBulk low).continuous.comp (unitLower ordered).continuous)
      (unitDiskBulk high).continuous) _ field
  intro core
  exact (congrArg (unitDiskBulk low) (unitLower_core ordered core)).trans
    ((unitDiskBulk_core low core).trans (unitDiskBulk_core high core).symm)

end Grad.OrdinaryDiskCalculus
