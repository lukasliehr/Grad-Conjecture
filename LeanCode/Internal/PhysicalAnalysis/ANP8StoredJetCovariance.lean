import ANP7ActualSourceProjection

noncomputable section
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology ContDiff Interval BigOperators
namespace Grad.RawCircularSectors
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope

theorem storedJet_splitting (field : ClosedJet 3) :
    valueMapJet planarInclusionMap (valueMapJet planarPartMap field) +
      valueMapJet toroidalInclusionMap (valueMapJet toroidalPartMap field) = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [closedJet_value_add, ContinuousMap.add_apply, valueMapJet_value]
  exact congrArg (fun mapping : ComplexEuclidean 3 →L[ℂ] ComplexEuclidean 3 => mapping (field.value point))
    splitting_reconstruction

theorem storedJet_joint_injective {first second : ClosedJet 3}
    (planar : valueMapJet planarPartMap first = valueMapJet planarPartMap second)
    (scalar : valueMapJet toroidalPartMap first = valueMapJet toroidalPartMap second) : first = second :=
  (storedJet_splitting first).symm.trans
    ((congrArg₂ (fun first second : ClosedJet 3 => first + second)
      (congrArg (valueMapJet planarInclusionMap) planar)
      (congrArg (valueMapJet toroidalInclusionMap) scalar)).trans (storedJet_splitting second))

def rawStoredJetLinear (mode : ℤ) : ClosedJet 3 →ₗ[ℂ] ClosedJet 3 :=
  (valueMapJetLinear 2 3 planarInclusionMap).comp
    ((rawVectorJetLinear mode).comp (valueMapJetLinear 3 2 planarPartMap)) +
  (valueMapJetLinear 1 3 toroidalInclusionMap).comp
    ((angularClosedJetLinear 1 mode).comp (valueMapJetLinear 3 1 toroidalPartMap))

def rawStoredJet (mode : ℤ) (field : ClosedJet 3) : ClosedJet 3 := rawStoredJetLinear mode field

theorem rawStoredJet_eq (mode : ℤ) (field : ClosedJet 3) :
    rawStoredJet mode field =
      valueMapJet planarInclusionMap (rawVectorJet mode (valueMapJet planarPartMap field)) +
        valueMapJet toroidalInclusionMap (angularClosedJet mode (valueMapJet toroidalPartMap field)) := rfl

theorem rawStoredJet_planar (mode : ℤ) (field : ClosedJet 3) :
    valueMapJet planarPartMap (rawStoredJet mode field) = rawVectorJet mode (valueMapJet planarPartMap field) := by
  rw [rawStoredJet_eq, valueMapJet_add, valueMapJet_comp, valueMapJet_comp,
    planarPart_planarInclusion, planarPart_toroidalInclusion, valueMapJet_zero, add_zero, valueMapJet_id]

theorem rawStoredJet_scalar (mode : ℤ) (field : ClosedJet 3) :
    valueMapJet toroidalPartMap (rawStoredJet mode field) = angularClosedJet mode (valueMapJet toroidalPartMap field) := by
  rw [rawStoredJet_eq, valueMapJet_add, valueMapJet_comp, valueMapJet_comp,
    toroidalPart_planarInclusion, toroidalPart_toroidalInclusion, valueMapJet_zero, zero_add, valueMapJet_id]

theorem scalarCovariantJet (frequency : ℂ) (field : ClosedJet 1) :
    valueMapJet toroidalPartMap (covariantJet frequency field) = frequency • field := by
  rw [covariantJet, valueMapJet_add]
  change valueMapJet toroidalPartMap (valueMapJet planarInclusionMap (gradientJet field)) +
    (valueMapJetLinear 3 1 toroidalPartMap) (frequency • valueMapJet toroidalInclusionMap field) = _
  rw [map_smul]
  change valueMapJet toroidalPartMap (valueMapJet planarInclusionMap (gradientJet field)) +
    frequency • valueMapJet toroidalPartMap (valueMapJet toroidalInclusionMap field) = _
  rw [valueMapJet_comp, valueMapJet_comp,
    toroidalPart_planarInclusion, toroidalPart_toroidalInclusion, valueMapJet_zero, zero_add, valueMapJet_id]

/-- Raw projections commute with the exact compensated covariant gradient,
for every cell frequency, including zero. -/
theorem rawStoredJet_covariant (mode : ℤ) (frequency : ℂ) (field : ClosedJet 1) :
    rawStoredJet mode (covariantJet frequency field) = covariantJet frequency (angularClosedJet mode field) := by
  apply storedJet_joint_injective
  · rw [rawStoredJet_planar, planarCovariantJet, planarCovariantJet, gradientJet_angular]
  · rw [rawStoredJet_scalar, scalarCovariantJet, scalarCovariantJet, angularClosedJet_smul]

theorem angularClosedJet_commute {dimension : ℕ} (first second : ℤ) (field : ClosedJet dimension) :
    angularClosedJet first (angularClosedJet second field) = angularClosedJet second (angularClosedJet first field) := by
  rw [angularClosedJet_projection, angularClosedJet_projection]
  by_cases same : first = second
  · subst second
    rfl
  · rw [if_neg same, if_neg (Ne.symm same)]

theorem rawStoredJet_complement (mode : ℤ) (field : ClosedJet 3) :
    rawStoredJet mode (fixedComplementJet field) = fixedComplementJet (rawStoredJet mode field) := by
  apply storedJet_joint_injective
  · rw [rawStoredJet_planar, planarComplement_jet, planarComplement_jet, rawStoredJet_planar,
      rawVectorJet_tangential]
  · rw [rawStoredJet_scalar, scalarComplement_jet, scalarComplement_jet, rawStoredJet_scalar,
      angularClosedJet_commute]

theorem rawStoredJet_firstJet_zero (mode : ℤ) (field : ClosedJet 3) (zero : ClosedFirstJetZero field) :
    ClosedFirstJetZero (rawStoredJet mode field) :=
  closedFirstJetZero_add _ _
    (closedFirstJetZero_valueMap planarInclusionMap _
      (rawVectorJet_firstJet_zero mode _ (closedFirstJetZero_valueMap planarPartMap field zero)))
    (closedFirstJetZero_valueMap toroidalInclusionMap _
      (closedFirstJetZero_angular _ (closedFirstJetZero_valueMap toroidalPartMap field zero) mode))

end Grad.RawCircularSectors
