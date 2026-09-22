import AKI14ComputedThirdResidual

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularStrongOrbit Grad.AnnularStrongData Grad.AnnularStrongSolution
open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularSourceGraph
open Grad.AnnularVariational Grad.ActualBoundaryPrimitives
open Grad.AnnularHighTilt Grad.SourceBoundaryTrace Grad.BoundaryKernelAction

/-- Original stored full F1, with the exact physical high/rho decoding. -/
def originalF1Coefficient (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (source : DivisionRow 1 lower) (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  lowRhoPhysicalCoefficient parameters lower positive (divisionHighWeight lower positive bounded source) radius mode

/-- The original G3 is decoded from its strengthened angular source norm. -/
def originalG3Coefficient (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (source : DivisionRow 1 lower) (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  originalF1Coefficient parameters lower positive bounded (originalAngularDecode lower source) radius mode

theorem lowRhoPhysicalCoefficient_meanFree (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (field : DivisionRow 1 lower) (mean : ∀ mode : ℤ × ℤ, mode.1 = 0 → field mode = 0) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      (if mode.1 = 0 then (0 : ℂ) else 1) • lowRhoPhysicalCoefficient parameters lower positive field radius mode =
        lowRhoPhysicalCoefficient parameters lower positive field radius mode := by
  filter_upwards [Lp.coeFn_zero (ComplexEuclidean 1) 2 (volume.restrict (Icc lower 1))] with radius zero
  intro mode
  by_cases angular : mode.1 = 0
  · have zeroValue : (0 : RadialL2 1 lower) radius = 0 := zero
    simp only [if_pos angular, zero_smul, lowRhoPhysicalCoefficient]
    rw [mean mode angular, zeroValue, smul_zero]
  · simp [angular]

theorem originalF1Coefficient_meanFree (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (source : DivisionRow 1 lower)
    (mean : ∀ mode : ℤ × ℤ, mode.1 = 0 → source mode = 0) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      (if mode.1 = 0 then (0 : ℂ) else 1) • originalF1Coefficient parameters lower positive bounded source radius mode =
        originalF1Coefficient parameters lower positive bounded source radius mode :=
  lowRhoPhysicalCoefficient_meanFree parameters lower positive _
    (fun mode zero => divisionHighWeight_zero_mode lower positive bounded source mode (mean mode zero))

theorem originalG3Coefficient_meanFree (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (source : DivisionRow 1 lower)
    (mean : ∀ mode : ℤ × ℤ, mode.1 = 0 → source mode = 0) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      (if mode.1 = 0 then (0 : ℂ) else 1) • originalG3Coefficient parameters lower positive bounded source radius mode =
        originalG3Coefficient parameters lower positive bounded source radius mode := by
  apply originalF1Coefficient_meanFree
  intro mode zero
  change (((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ) • source mode = 0
  rw [mean mode zero, smul_zero]

variable (parameters : PhaseParameters) (length lower : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length) (core : OriginalSmoothSourceCore parameters)

private theorem originalStrongF1Decode (source : OriginalStrongCarrier parameters lower 0 0)
    (radius : ℝ) (mode : ℤ × ℤ) :
    lowRhoPhysicalCoefficient parameters lower positive
      (strongKnownBulk parameters lower positive bounded.le
        (originalToStrong parameters lower length positive bounded.le lengthPositive 0 0 source) 3) radius mode =
      originalF1Coefficient parameters lower positive bounded.le source.val.ofLp.1.ofLp.2.ofLp.1 radius mode := rfl

private theorem originalStrongG3Decode (source : OriginalStrongCarrier parameters lower 0 0)
    (radius : ℝ) (mode : ℤ × ℤ) :
    lowRhoPhysicalCoefficient parameters lower positive
      ((strongToLow parameters lower positive bounded.le 0 0
        (originalToStrong parameters lower length positive bounded.le lengthPositive 0 0 source)).ofLp.1.ofLp.2) radius mode =
      originalG3Coefficient parameters lower positive bounded.le source.val.ofLp.1.ofLp.2.ofLp.2 radius mode := rfl

theorem actualOriginalIndependentF_original (radius : ℝ) (mode : ℤ × ℤ) :
    actualOriginalIndependentF parameters length lower positive bounded lengthPositive core radius mode =
      originalF1Coefficient parameters lower positive bounded.le
        (originalSmoothStrongData parameters lower positive bounded.le core).val.ofLp.1.ofLp.2.ofLp.1 radius mode := by
  have dataSame : (strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core =
      originalToStrong parameters lower length positive bounded.le lengthPositive 0 0
        (originalSmoothStrongData parameters lower positive bounded.le core) :=
    strongSmoothDenseMap_actual parameters lower length positive bounded.le lengthPositive core
  have rowSame := congrArg (fun data : StrongDataCarrier parameters lower positive bounded.le 0 0 =>
    strongKnownBulk parameters lower positive bounded.le data 3) dataSame
  have physical := congrArg (fun row : DivisionRow 1 lower => lowRhoPhysicalCoefficient parameters lower positive row radius mode) rowSame
  exact physical.trans (originalStrongF1Decode parameters length lower positive bounded lengthPositive
    (originalSmoothStrongData parameters lower positive bounded.le core) radius mode)

theorem actualOriginalIndependentG_original (radius : ℝ) (mode : ℤ × ℤ) :
    actualOriginalIndependentG parameters length lower positive bounded lengthPositive core radius mode =
      originalG3Coefficient parameters lower positive bounded.le
        (originalSmoothStrongData parameters lower positive bounded.le core).val.ofLp.1.ofLp.2.ofLp.2 radius mode := by
  have dataSame : (strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core =
      originalToStrong parameters lower length positive bounded.le lengthPositive 0 0
        (originalSmoothStrongData parameters lower positive bounded.le core) :=
    strongSmoothDenseMap_actual parameters lower length positive bounded.le lengthPositive core
  have rowSame := congrArg (fun data : StrongDataCarrier parameters lower positive bounded.le 0 0 =>
    (strongToLow parameters lower positive bounded.le 0 0 data).ofLp.1.ofLp.2) dataSame
  have physical := congrArg (fun row : DivisionRow 1 lower => lowRhoPhysicalCoefficient parameters lower positive row radius mode) rowSame
  exact physical.trans (originalStrongG3Decode parameters length lower positive bounded lengthPositive
    (originalSmoothStrongData parameters lower positive bounded.le core) radius mode)

/-- Multiplication by the original angular factor recovers the full
strengthened G3 coordinate, not merely its angular derivative. -/
theorem originalG3Coefficient_strengthened (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower)
    (bounded : lower ≤ 1) (source : DivisionRow 1 lower) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) • originalG3Coefficient parameters lower positive bounded source radius mode =
        originalF1Coefficient parameters lower positive bounded source radius mode := by
  rw [ae_all_iff]
  intro mode
  have stored : divisionHighWeight lower positive bounded (originalAngularDecode lower source) mode =
      (((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ) • divisionHighWeight lower positive bounded source mode := by
    rw [divisionHighWeight_mode, divisionHighWeight_mode]
    exact map_smul (scalarRadialMap lower (highPowerCurve lower (-highTiltExponent) positive)
      (lower ^ (-highTiltExponent)) (fun radius inside => highNegativePower_bound lower positive bounded radius inside))
      (((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ) (source mode)
  filter_upwards [Lp.coeFn_smul (((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ)
    (divisionHighWeight lower positive bounded source mode)] with radius scaled
  unfold originalG3Coefficient originalF1Coefficient lowRhoPhysicalCoefficient
  rw [stored, scaled]
  change ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) • ((lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ •
    ((((1 + |(mode.1 : ℝ)|)⁻¹ : ℝ) : ℂ) • divisionHighWeight lower positive bounded source mode radius)) =
      (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ • divisionHighWeight lower positive bounded source mode radius
  have realNonzero : (1 + |(mode.1 : ℝ)| : ℝ) ≠ 0 := by positivity
  have nonzero : ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr realNonzero
  rw [Complex.ofReal_inv, smul_comm ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ),
    smul_smul ((1 + |(mode.1 : ℝ)| : ℝ) : ℂ), mul_inv_cancel₀ nonzero, one_smul]

end Grad.AnnularOriginalSmoothCore
