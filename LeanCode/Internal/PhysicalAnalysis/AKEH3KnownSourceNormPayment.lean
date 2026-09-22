import AKEH1OriginalSourceNormPacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace Grad.OriginalMainConsumer
open Grad.ClosedJets Grad.CartesianState Grad.CartesianStartup Grad.NonlinearProduct Grad.NonlinearQuotientBounds
open Grad.OriginalCoreRealization Grad.QuotientProjection Grad.FinitePhysicalJetLift

/-- The known packet sources cost one genuine source order and no
coefficient or unknown-state norm. -/
theorem originalSourceNormPacket_sourceNorms (parameters : PhaseParameters) (length : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0≤constant ∧ ∀ {radius : ℝ}
      (coefficient : OriginalUnitRankState parameters length radius)
      (core : ACore parameters 3) (source : SmoothQuotient parameters),
      StartupOriginalUnitNormPacket.sourceNorms grade (originalSourceNormPacket coefficient core source)≤
        constant*‖quotientEta parameters (grade+1) source‖ := by
  let firstCertificate := startupOriginalKnownForceCore_bound parameters grade
  let first := firstCertificate.choose
  have first0 := firstCertificate.choose_spec.1
  let lastCertificate := startupOriginalKnownForceCore_bound parameters (grade+1)
  let last := lastCertificate.choose
  have last0 := lastCertificate.choose_spec.1
  let scalar := ‖(length : ℂ)⁻¹‖
  refine ⟨first+scalar+scalar+last,by positivity,?_⟩
  intro radius coefficient core source
  have sourceMono := referenceSource_norm_mono parameters (Nat.le_succ grade) source
  have force := (firstCertificate.choose_spec.2 source).trans (mul_le_mul_of_nonneg_left sourceMono first0)
  have third := (startupOriginalKnownScalarCore_bound parameters length grade source 3).trans
    (mul_le_mul_of_nonneg_left sourceMono (norm_nonneg _))
  have determinant := (startupOriginalKnownScalarCore_bound parameters length grade source 2).trans
    (mul_le_mul_of_nonneg_left sourceMono (norm_nonneg _))
  have derivative := lastCertificate.choose_spec.2 source
  change originalGradeNorm grade (startupOriginalKnownForceCore parameters source)+
    originalGradeNorm grade (startupOriginalKnownScalarCore parameters length source 3)+
    originalGradeNorm grade (startupOriginalKnownScalarCore parameters length source 2)+
    originalGradeNorm (grade+1) (startupOriginalKnownForceCore parameters source)≤_
  exact (add_le_add (add_le_add (add_le_add force third) determinant) derivative).trans_eq (by ring)

/-- The complete known tensor/flux payment keeps the physical scale
fixed before every coefficient, unknown core and original source. -/
theorem originalSourceNormPacket_sourcePayment (parameters : PhaseParameters) (length scale : ℝ) (grade : ℕ) :
    ∃ constant : ℝ, 0≤constant ∧ ∀ {radius : ℝ}
      (coefficient : OriginalUnitRankState parameters length radius)
      (core : ACore parameters 3) (source : SmoothQuotient parameters),
      StartupOriginalUnitNormPacket.sourcePayment grade scale (originalSourceNormPacket coefficient core source)≤
        constant*‖quotientEta parameters (grade+1) source‖ := by
  let sources := originalSourceNormPacket_sourceNorms parameters length grade
  let tensors := StartupOriginalUnitNormPacket.sourcePayment_bound parameters grade scale
  refine ⟨tensors.choose*sources.choose,mul_nonneg tensors.choose_spec.1 sources.choose_spec.1,?_⟩
  intro radius coefficient core source
  exact (tensors.choose_spec.2 (originalSourceNormPacket coefficient core source)).trans
    ((mul_le_mul_of_nonneg_left (sources.choose_spec.2 coefficient core source) tensors.choose_spec.1).trans_eq
      (mul_assoc _ _ _).symm)

end Grad.OriginalMainConsumer
