import QU6Consumer
import GaugeSliceBounds

noncomputable section

open scoped ComplexConjugate

namespace Grad.ConstrainedTransfer

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.CompletedReality Grad.RealFixedRanges Grad.SmoothingFamily Grad.Cor18

theorem gaugeComposite_conjugate (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore parameters 2) :
    cartesianCoreConjugation parameters (gaugeComposite parameters parameter inside field) =
      gaugeComposite parameters parameter inside (cartesianCoreConjugation parameters field) := by
  rw [gaugeComposite_apply, tangentialCore_conjugate, seedTransposeCore_conjugate,
    seedMatrixCore_conjugate, gaugeComposite_apply]

theorem sliceProjection_conjugate (parameters : PhaseParameters) (parameter : Seed.Parameters)
    (inside : parameter ∈ Seed.parameterDomain) (field : ACore parameters 2) :
    cartesianCoreConjugation parameters (sliceProjection parameters parameter inside field) =
      sliceProjection parameters parameter inside (cartesianCoreConjugation parameters field) := by
  rw [sliceProjection_apply, map_sub, gaugeComposite_conjugate, sliceProjection_apply]

theorem planarTransfer_conjugate (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (field : ACore parameters 2) :
    cartesianCoreConjugation parameters (planarTransfer parameters first insideFirst second insideSecond field) =
      planarTransfer parameters first insideFirst second insideSecond (cartesianCoreConjugation parameters field) := by
  rw [planarTransfer_apply, seedMatrixCore_conjugate, sliceProjection_conjugate,
    seedInverseCore_conjugate, planarTransfer_apply]

theorem transferToroidalComponent_conjugate (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (field : ACore parameters 3) :
    cartesianCoreConjugation parameters
        (transferToroidalComponent parameters first insideFirst second insideSecond field) =
      transferToroidalComponent parameters first insideFirst second insideSecond
        (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters
    ((toroidalPartCore parameters field - angularCore parameters 0 (toroidalPartCore parameters field)) -
      (parameters.length⁻¹ : ℂ) • angularCore parameters 0 (derivativeDotCore parameters second insideSecond
        (planarTransfer parameters first insideFirst second insideSecond (planarPartCore parameters field)))) = _
  rw [map_sub, map_sub, toroidalPartCore_conjugate, angularCore_conjugate, neg_zero,
    toroidalPartCore_conjugate, coreConjugation_complex_smul, angularCore_conjugate, neg_zero,
    derivativeDotCore_conjugate, planarTransfer_conjugate, planarPartCore_conjugate]
  simp only [map_inv₀, Complex.conj_ofReal]
  rfl

/-- Literal N18 commutes with real physical conjugation and cell reversal. -/
theorem seedTransfer_conjugate (parameters : PhaseParameters)
    (first : Seed.Parameters) (insideFirst : first ∈ Seed.parameterDomain)
    (second : Seed.Parameters) (insideSecond : second ∈ Seed.parameterDomain)
    (field : ACore parameters 3) :
    cartesianCoreConjugation parameters (seedTransfer parameters first insideFirst second insideSecond field) =
      seedTransfer parameters first insideFirst second insideSecond (cartesianCoreConjugation parameters field) := by
  change cartesianCoreConjugation parameters
    (planarInclusionCore parameters
      (planarTransfer parameters first insideFirst second insideSecond (planarPartCore parameters field)) +
      toroidalInclusionCore parameters (transferToroidalComponent parameters first insideFirst second insideSecond field)) = _
  rw [map_add, planarInclusionCore_conjugate, planarTransfer_conjugate, planarPartCore_conjugate,
    toroidalInclusionCore_conjugate, transferToroidalComponent_conjugate]
  rfl

end Grad.ConstrainedTransfer
