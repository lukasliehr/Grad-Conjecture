import ANG26CommutedSourceFunctional

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
open Set
open scoped ContDiff
namespace Grad.CircularHighWeak
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearRange
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.GaugeTransfer

theorem rotationJetPower_succ_left (order : ℕ) (field : ClosedJet 1) :
    rotationJetPower (order + 1) field = rotationJet (rotationJetPower order field) := by
  induction order generalizing field with
  | zero => rfl
  | succ order previous => exact previous (rotationJet field)

/-- Adjacent completed source powers satisfy the literal weak Cartesian
rotation identity against every compact smooth test on the disk. -/
theorem sourceRotationPower_weak_step (order : ℕ) (source : apGrade 1 0 0 1 1 (order + 1))
    (cell : ℤ) (vector : Grad.GenericCarriers.PhysicalValue 1)
    (test : Grad.PDEBootstrap.Spatial → ℝ) (smooth : ContDiff ℝ ∞ test) (compact : HasCompactSupport test)
    (supported : tsupport test ⊆ openUnitDisk) :
    apDiskPairing 1 cell vector test smooth compact (sourceRotationPower (order + 1) source) =
      angularWeakPairing 1 cell vector test smooth compact
        (sourceRotationPower order (apLowering 1 0 0 1 (Nat.le_succ order) source)) := by
  apply isClosed_property (apFiniteInto_denseRange (dimension := 1) (grade := order + 1) 1 0 0 1)
    (isClosed_eq ((apDiskPairing 1 cell vector test smooth compact).continuous.comp (sourceRotationPower (order + 1)).continuous)
      ((angularWeakPairing 1 cell vector test smooth compact).continuous.comp
        ((sourceRotationPower order).continuous.comp (apLowering 1 0 0 1 (Nat.le_succ order)).continuous))) _ source
  intro core
  have first := (sourceRotationPower_core (order + 1) core).trans
    (congrArg closedL2Core (rotationJetPower_succ_left order (core 0)))
  have second := (congrArg (sourceRotationPower order) (apLowering_core 1 0 0 1 (Nat.le_succ order) core)).trans
    (sourceRotationPower_core order core)
  exact (congrArg (apDiskPairing 1 cell vector test smooth compact) first).trans
    ((rotationJet_weak (rotationJetPower order (core 0)) cell vector test smooth compact supported).trans
      (congrArg (angularWeakPairing 1 cell vector test smooth compact) second).symm)

theorem sourceRotationPower_high (order : ℕ) (source : apGrade 1 0 0 1 1 order)
    (high : sourceBulk order source ∈ highDiskL2) : sourceRotationPower order source ∈ highDiskL2 := by
  intro mode low
  exact (sourceRotationPower_coefficient order mode source).trans
    ((congrArg (fun value : DiskL2 1 => (Complex.I * (mode : ℂ)) ^ order • value) (high mode low)).trans (smul_zero _))

theorem sourceHighPower_original (order : ℕ) (source : apGrade 1 0 0 1 1 order)
    (high : sourceBulk order source ∈ highDiskL2) :
    (sourceHighPower order source).val = sourceRotationPower order source :=
  highL2Projection_fixed ⟨sourceRotationPower order source, sourceRotationPower_high order source high⟩

/-- Exact all-order source functional −∫R^sF·conj(Rw), retaining the original
high input rather than changing it to an additional projected source. -/
theorem angularWeakSolutionPower_original_functional (parameter : ℝ) (order : ℕ)
    (source : apGrade 1 0 0 1 1 order) (high : sourceBulk order source ∈ highDiskL2) (test : highDiskGrade) :
    robinValue parameter (angularWeakSolutionPower parameter order source) test =
      -inner ℂ (highRotation test) (sourceRotationPower order source) :=
  (angularWeakSolutionPower_functional parameter order source test).trans
    (congrArg (fun value : DiskL2 1 => -inner ℂ (highRotation test) value) (sourceHighPower_original order source high))

end Grad.CircularHighWeak
