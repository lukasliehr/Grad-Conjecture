import AIY14OriginalStrongDataIsomorphism

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option synthInstance.maxHeartbeats 400000
open Set MeasureTheory Filter
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularStrongData
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision
open Grad.AnnularSourceGraph Grad.AnnularVariational Grad.AnnularCurrentEnergy
open Grad.AnnularCurrentSource Grad.AnnularHighTilt Grad.AnnularLowEnergy Grad.AnnularCrossMaps
open Grad.AnnularKnownLow Grad.ActualBoundaryPrimitives

/-- Exact original strengthened angular norm, whose single stored coordinate
is equivalent to the BF4 Hilbert pair g,Rg. -/
theorem strengthenedG_literal_norm_sq (lower : ℝ) (g rg : DivisionRow 1 lower)
    (relation : ∀ mode : ℤ × ℤ, rg mode = (Complex.I * (mode.1 : ℂ)) • g mode) :
    ‖strengthenedG lower g rg‖ ^ 2 =
      ∑' mode : ℤ × ℤ, (1 + |(mode.1 : ℝ)|) ^ 2 * ‖g mode‖ ^ 2 := by
  have normFormula := lp.norm_rpow_eq_tsum (p := 2) (by norm_num) (strengthenedG lower g rg)
  norm_num only [ENNReal.toReal_ofNat, Real.rpow_ofNat] at normFormula
  rw [normFormula]
  apply tsum_congr
  intro mode
  rw [strengthenedG_mode lower g rg relation, norm_smul, Complex.norm_real,
    Real.norm_of_nonneg (by positivity), mul_pow]

/-- The fixed BF5 constants precede every collar and datum. The original
analytic width and phase are untouched, and no physical state is selected. -/
theorem originalStrongBF5_uniform (parameters : PhaseParameters) (length : ℝ) (lengthPositive : 0 < length) :
    ∃ originalConstant weightedConstant : ℝ, 0 < originalConstant ∧ 0 < weightedConstant ∧
      ∀ (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (angular cell : ℕ),
      let equivalence := originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive angular cell
      (∀ data : OriginalStrongCarrier parameters lower angular cell,
        ‖equivalence data‖ ≤ (weightedConstant * lower ^ (-9 / 4 : ℝ)) * ‖data‖) ∧
      (∀ data : StrongDataCarrier parameters lower positive bounded angular cell,
        ‖equivalence.symm data‖ ≤ originalConstant * ‖data‖) := by
  refine ⟨7 + 2 * lowOuterFrequencyConstant length,
    10 + originalLowIncomingConstant parameters length, ?_, ?_, ?_⟩
  · have := lowOuterFrequencyConstant_two_le length lengthPositive
    linarith
  · have := lowOuterFrequencyConstant_two_le length lengthPositive
    have : 1 ≤ lowBalanceConstant length parameters.gamma := le_max_left _ _
    unfold originalLowIncomingConstant
    positivity
  · intro lower positive bounded angular cell
    exact ⟨originalStrongWeightEquivalence_bound parameters lower length positive bounded lengthPositive angular cell,
      originalStrongWeightEquivalence_inverse_bound parameters lower length positive bounded lengthPositive angular cell⟩

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (angular cell : ℕ)

/-- Exact single-source diagonal consumer: AIS and AIR receive the identical
F0/RF0/F2 rows. High f/g are projected once; the full low f/g stay unchanged.
The only source graphs are the shared original pair. -/
theorem sharedStrongData_exact_consumer
    (data : StrongDataCarrier parameters lower positive bounded angular cell) :
    let high := ActualHighKnownCarrier.toGraphKnownData parameters lower positive bounded angular cell
      (strongToHigh parameters lower positive bounded angular cell data)
    let low := strongToLow parameters lower positive bounded angular cell data
    high.weighted 0 = low.ofLp.1.ofLp.1 0 ∧
    high.weighted 1 = low.ofLp.1.ofLp.1 1 ∧
    high.weighted 2 = low.ofLp.1.ofLp.1 2 ∧
    high.weighted 3 = highRowProjection lower (low.ofLp.1.ofLp.1 3) ∧
    high.auxiliary 0 = highRowProjection lower low.ofLp.1.ofLp.2 ∧
    high.auxiliary 1 = 0 ∧ high.auxiliary 2 = 0 ∧
    high.graphs = (data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.1,data.val.ofLp.1.ofLp.2.ofLp.1.ofLp.2) ∧
    high.datum = data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.1 ∧
    high.innerValue = data.val.ofLp.1.ofLp.2.ofLp.2.ofLp.2 ∧
    low.ofLp.2 = data.val.ofLp.2 ∧
    ‖strongToHigh parameters lower positive bounded angular cell data‖ ≤ ‖data‖ ∧
    ‖low‖ ≤ ‖data‖ := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
    strongToHigh_bound parameters lower positive bounded angular cell data,
    strongToLow_bound parameters lower positive bounded angular cell data⟩

variable (length : ℝ) (lengthPositive : 0 < length)

/-- Both genuine data identities, on the independently prescribed original
strong carrier and on the complete shared BF4 carrier. -/
theorem originalStrongBF5_both_identities :
    (∀ data : OriginalStrongCarrier parameters lower angular cell,
      (originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive angular cell).symm
        (originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive angular cell data) = data) ∧
    (∀ data : StrongDataCarrier parameters lower positive bounded angular cell,
      originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive angular cell
        ((originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive angular cell).symm data) = data) :=
  ⟨(originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive angular cell).symm_apply_apply,
    (originalStrongWeightEquivalence parameters lower length positive bounded lengthPositive angular cell).apply_symm_apply⟩

end Grad.AnnularStrongData
