import AJI23SamePhysicalUnknownPacket

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
open Set Filter MeasureTheory
namespace Grad.AnnularSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.SourceCollarCoefficients Grad.AnnularVariational Grad.AnnularSourceGraph Grad.AnnularReconstruction
open Grad.AnnularLowEnergy Grad.AnnularOmegaGraph Grad.AnnularFluxTrace Grad.AnnularCurrentLow
open Grad.AnnularHighGenerators Grad.AnnularCoupledInverse Grad.AnnularHighTilt Grad.AnnularTiltedReference
open Grad.AnnularCrossMaps Grad.AnnularStrongSolution Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.WeightedTrace

/-- The stored free high/low packet is exactly the physical packet of the
same sections, with the original common storage factor. -/
theorem homogeneousCoupledSevenInput_sameSections (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CoupledSpace lower length positive lengthPositive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      homogeneousCoupledSevenInput parameters length lower lengthPositive positive field mode radius =
        (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ) •
          rawPhysicalSevenVector radius mode
            (sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0 (radialClamp lower bounded.le radius) mode)
            (sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 (radialClamp lower bounded.le radius) mode) := by
  rw [ae_all_iff]
  intro mode
  let high := highCrossSevenInput lower length positive lengthPositive field.ofLp.1
  let low := lowNormalizedSevenInput parameters lower length lengthPositive positive (field.ofLp.2.val 0)
  have sum : homogeneousCoupledSevenInput parameters length lower lengthPositive positive field mode = high mode + low mode := rfl
  rw [sum]
  by_cases large : 3 ≤ |mode.1|
  · have notSmall : ¬ (|mode.1| = 1 ∨ |mode.1| = 2) := by omega
    have lowZero : low mode = 0 := lowNormalizedSevenInput_outside parameters lower length lengthPositive positive _ mode notSmall
    filter_upwards [Lp.coeFn_add (high mode) (low mode),
      highCrossSevenInput_originalSections parameters lower length positive bounded lengthPositive field.ofLp.1 ⟨mode,large⟩,
      Lp.coeFn_zero (ComplexEuclidean 7) 2 (volume.restrict (Icc lower 1)), ae_restrict_mem measurableSet_Icc]
      with radius added original zero inside
    rw [added]
    simp only [Pi.add_apply]
    rw [lowZero, zero, Pi.zero_apply, add_zero]
    simpa only [sameCoupledXCoefficient, sameCoupledXiCoefficient, dif_pos large,
      pow_zero, Complex.ofReal_one, one_smul, radialClamp_eq lower bounded.le radius inside] using original
  · have highZero : high mode = 0 := highCrossSevenInput_outside lower length positive lengthPositive _ mode large
    by_cases small : |mode.1| = 1 ∨ |mode.1| = 2
    · filter_upwards [Lp.coeFn_add (high mode) (low mode),
        lowNormalizedSevenInput_original parameters lower length lengthPositive positive bounded field.ofLp.2,
        Lp.coeFn_zero (ComplexEuclidean 7) 2 (volume.restrict (Icc lower 1))]
        with radius added original zero
      rw [added]
      simp only [Pi.add_apply]
      rw [highZero, zero, Pi.zero_apply, zero_add]
      rw [original mode]
      simp only [sameCoupledXCoefficient, sameCoupledXiCoefficient, dif_neg large, dif_pos small,
        pow_zero, Complex.ofReal_one, one_smul, rawPhysicalSevenVector_low radius ⟨mode,small⟩,
        lowOriginalSevenCoefficient, radialSectionExtension]
      rfl
    · have lowZero : low mode = 0 := lowNormalizedSevenInput_outside parameters lower length lengthPositive positive _ mode small
      filter_upwards [Lp.coeFn_add (high mode) (low mode),
        Lp.coeFn_zero (ComplexEuclidean 7) 2 (volume.restrict (Icc lower 1))] with radius added zero
      rw [added]
      simp only [Pi.add_apply]
      rw [highZero, lowZero, zero, Pi.zero_apply, add_zero]
      simp only [sameCoupledXCoefficient, sameCoupledXiCoefficient, dif_neg large, dif_neg small,
        rawPhysicalSevenVector, map_zero, smul_zero, add_zero]

end Grad.AnnularSmoothCore
