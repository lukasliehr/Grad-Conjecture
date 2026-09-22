import AKG2EndpointRestrictionIdentities

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
namespace Grad.AnnularRestriction
open Grad.ClosedJets Grad.CartesianState Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.SourceCollarDivision Grad.AnnularSourceGraph Grad.AnnularCurrentSource
open Grad.AnnularForwardTraces Grad.AnnularStrongOrbit Grad.AnnularLowEnergy
open Grad.AnnularForwardDatum Grad.AnnularCrossMaps Grad.AnnularCoupledInverse Grad.AnnularSmoothCore
open Grad.GaugeCoefficients.Physical.WeightedTrace
attribute [local instance] traceOriginalRealNormed traceOriginalRealModule
  forwardSourcesRealNormed forwardSourcesRealModule forwardFiveRealNormed forwardFiveRealModule

variable (parameters : PhaseParameters) (lower upper length : ℝ)
    (lowerPositive : 0 < lower) (upperPositive : 0 < upper) (upperBounded : upper < 1)
    (lengthPositive : 0 < length) (included : lower ≤ upper)

theorem coupledEndpointRestriction_xi_base (field : CoupledSpace lower length lowerPositive lengthPositive)
    (radius : Icc upper (1 : ℝ)) (mode : ℤ × ℤ) :
    sameCoupledXiCoefficient parameters upper length upperPositive upperBounded lengthPositive
      (coupledEndpointRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field) 0 radius mode =
    sameCoupledXiCoefficient parameters lower length lowerPositive (included.trans_lt upperBounded) lengthPositive field 0
      ⟨radius.val,included.trans radius.property.1,radius.property.2⟩ mode := by
  unfold sameCoupledXiCoefficient
  split_ifs with large small
  · simp only [pow_zero,Complex.ofReal_one,one_smul]
    exact highEnergyRestriction_physical lower upper length lowerPositive upperPositive upperBounded included parameters field.ofLp.1.ofLp.1 ⟨mode,large⟩ radius
  · simp only [pow_zero,Complex.ofReal_one,one_smul]
    exact lowEnergyRestriction_physical parameters lower upper length included lowerPositive upperPositive upperBounded field.ofLp.2 (0,⟨mode,small⟩) radius
  · rfl

theorem coupledEndpointRestriction_x_base (field : CoupledSpace lower length lowerPositive lengthPositive)
    (radius : Icc upper (1 : ℝ)) (mode : ℤ × ℤ) :
    sameCoupledXCoefficient parameters upper length upperPositive upperBounded lengthPositive
      (coupledEndpointRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field) 0 radius mode =
    sameCoupledXCoefficient parameters lower length lowerPositive (included.trans_lt upperBounded) lengthPositive field 0
      ⟨radius.val,included.trans radius.property.1,radius.property.2⟩ mode := by
  unfold sameCoupledXCoefficient
  split_ifs with large small
  · simp only [pow_zero,Complex.ofReal_one,one_smul]
    exact highOmegaRestriction_physical lower upper length lowerPositive upperPositive upperBounded lengthPositive included parameters field.ofLp.1.ofLp.2 ⟨mode,large⟩ radius
  · simp only [pow_zero,Complex.ofReal_one,one_smul]
    exact lowEnergyRestriction_physical parameters lower upper length included lowerPositive upperPositive upperBounded field.ofLp.2 (1,⟨mode,small⟩) radius
  · rfl

/-- Every actual physical xi coefficient at every inserted grade is the
SAME coefficient, including the new incoming endpoint and the original outer endpoint. -/
theorem coupledEndpointRestriction_xi (field : CoupledSpace lower length lowerPositive lengthPositive)
    (grade : ℕ) (radius : Icc upper (1 : ℝ)) (mode : ℤ × ℤ) :
    sameCoupledXiCoefficient parameters upper length upperPositive upperBounded lengthPositive
      (coupledEndpointRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field) grade radius mode =
    sameCoupledXiCoefficient parameters lower length lowerPositive (included.trans_lt upperBounded) lengthPositive field grade
      ⟨radius.val,included.trans radius.property.1,radius.property.2⟩ mode := by
  rw [sameCoupledXiCoefficient_grade parameters upper length upperPositive upperBounded lengthPositive _ grade,
    sameCoupledXiCoefficient_grade parameters lower length lowerPositive (included.trans_lt upperBounded) lengthPositive field grade,
    coupledEndpointRestriction_xi_base parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included]

/-- Exact SAME physical x at all full Fourier modes and grades. The zero
angular complement stays zero; no coefficient is newly discarded. -/
theorem coupledEndpointRestriction_x (field : CoupledSpace lower length lowerPositive lengthPositive)
    (grade : ℕ) (radius : Icc upper (1 : ℝ)) (mode : ℤ × ℤ) :
    sameCoupledXCoefficient parameters upper length upperPositive upperBounded lengthPositive
      (coupledEndpointRestriction lower upper length lowerPositive upperPositive upperBounded lengthPositive included field) grade radius mode =
    sameCoupledXCoefficient parameters lower length lowerPositive (included.trans_lt upperBounded) lengthPositive field grade
      ⟨radius.val,included.trans radius.property.1,radius.property.2⟩ mode := by
  rw [sameCoupledXCoefficient_grade parameters upper length upperPositive upperBounded lengthPositive _ grade,
    sameCoupledXCoefficient_grade parameters lower length lowerPositive (included.trans_lt upperBounded) lengthPositive field grade,
    coupledEndpointRestriction_x_base parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included]

theorem originalRetainedRestriction_xi (field : OriginalCoupledSpace lower length lowerPositive)
    (grade : ℕ) (radius : Icc upper (1 : ℝ)) (mode : ℤ × ℤ) :
    sameCoupledXiCoefficient parameters upper length upperPositive upperBounded lengthPositive
      (originalCoupledEquivalence parameters upper length upperPositive upperBounded.le lengthPositive
        (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included field)) grade radius mode =
    sameCoupledXiCoefficient parameters lower length lowerPositive (included.trans_lt upperBounded) lengthPositive
      (originalCoupledEquivalence parameters lower length lowerPositive (included.trans upperBounded.le) lengthPositive field) grade
      ⟨radius.val,included.trans radius.property.1,radius.property.2⟩ mode := by
  rw [originalRetainedRestriction_weighted]
  exact coupledEndpointRestriction_xi parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included _ grade radius mode

theorem originalRetainedRestriction_x (field : OriginalCoupledSpace lower length lowerPositive)
    (grade : ℕ) (radius : Icc upper (1 : ℝ)) (mode : ℤ × ℤ) :
    sameCoupledXCoefficient parameters upper length upperPositive upperBounded lengthPositive
      (originalCoupledEquivalence parameters upper length upperPositive upperBounded.le lengthPositive
        (originalRetainedRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included field)) grade radius mode =
    sameCoupledXCoefficient parameters lower length lowerPositive (included.trans_lt upperBounded) lengthPositive
      (originalCoupledEquivalence parameters lower length lowerPositive (included.trans upperBounded.le) lengthPositive field) grade
      ⟨radius.val,included.trans radius.property.1,radius.property.2⟩ mode := by
  rw [originalRetainedRestriction_weighted]
  exact coupledEndpointRestriction_x parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included _ grade radius mode

/-- Both copied source graphs represent the SAME physical sources on the
smaller collar, with the original F0 angular order and original F2 order. -/
theorem originalFiveBlockRestriction_sourcePhysical (field : ForwardFiveBlocks parameters lower length lowerPositive) :
    let output := originalFiveBlockRestriction parameters lower upper length lowerPositive upperPositive upperBounded lengthPositive included field
    ∀ᵐ radius ∂volume.restrict (Icc upper 1), ∀ mode : ℤ × ℤ,
      totalSourceCoefficient parameters 1 upper upperPositive upperBounded.le 1 0 0 output.ofLp.2.ofLp.1.ofLp.1 mode radius =
        totalSourceCoefficient parameters 1 lower lowerPositive (included.trans upperBounded.le) 1 0 0 field.ofLp.2.ofLp.1.ofLp.1 mode radius ∧
      totalSourceCoefficient parameters 1 upper upperPositive upperBounded.le 0 0 0 output.ofLp.2.ofLp.1.ofLp.2 mode radius =
        totalSourceCoefficient parameters 1 lower lowerPositive (included.trans upperBounded.le) 0 0 0 field.ofLp.2.ofLp.1.ofLp.2 mode radius :=
  originalFullSourceRestriction_sourcePhysical parameters lower upper included lowerPositive upperPositive upperBounded.le field.ofLp.2

end Grad.AnnularRestriction
