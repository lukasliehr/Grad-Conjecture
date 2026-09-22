import AJI22ActualHighSectionStorage
import AJC3OnceOnlyPhysicalInput

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

theorem rawPhysicalSevenVector_cross (radius : ℝ) (mode : ℤ × ℤ) (x xi : ComplexEuclidean 1) :
    rawPhysicalSevenVector radius mode x xi = crossSevenSymbol radius mode xi x := by
  apply PiLp.ext
  intro slot
  fin_cases slot <;> simp [rawPhysicalSevenVector, crossSevenSymbol, matrixUnit_apply,
    operatorBasis, frequencyNumerator]
  all_goals first | trivial | ring

theorem rawPhysicalSevenVector_low (radius : ℝ) (mode : LowAnnularMode) (x xi : ComplexEuclidean 1) :
    rawPhysicalSevenVector radius mode.val x xi = lowPhysicalSevenSymbol radius mode (xi 0) (x 0) := by
  rw [rawPhysicalSevenVector_cross]
  have angular : Complex.I * (((mode.val.1 : ℝ) / radius : ℝ) : ℂ) =
      Complex.I * (mode.val.1 : ℂ) * ((radius⁻¹ : ℝ) : ℂ) := by
    push_cast
    rw [div_eq_mul_inv]
    ring
  unfold crossSevenSymbol lowPhysicalSevenSymbol
  rw [angular]

theorem highCrossSevenInput_originalSections (parameters : PhaseParameters) (lower length : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (field : CrossHighSpace lower length positive lengthPositive) (mode : HighAnnularMode) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1),
      highCrossSevenInput lower length positive lengthPositive field mode.val radius =
        (lowRhoPhysicalWeight parameters lower positive radius mode.val : ℂ) •
          rawPhysicalSevenVector radius mode.val
            (highPowerCurve lower highTiltExponent positive radius •
              actualFluxPhysicalSection lower positive bounded parameters
                (annularOmegaIntoNu lower length positive lengthPositive field.ofLp.2) mode (radialClamp lower bounded.le radius))
            (highPowerCurve lower highTiltExponent positive radius •
              annularPhysicalValueSection parameters lower length positive bounded mode
                (bEnergyDecode lower length positive field.ofLp.1) (radialClamp lower bounded.le radius)) := by
  filter_upwards [highCrossSevenInput_ae lower length positive lengthPositive field mode,
    actualHighXiSection_stored parameters lower length positive bounded
      (bEnergyDecode lower length positive field.ofLp.1) mode,
    actualHighXSection_stored parameters lower positive bounded
      (annularOmegaIntoNu lower length positive lengthPositive field.ofLp.2) mode]
    with radius packet xi x
  rw [packet, rawPhysicalSevenVector_cross, ← crossSevenSymbol_smul, xi]
  change crossSevenSymbol radius mode.val _ (crossHighX lower length positive lengthPositive field mode radius) =
    crossSevenSymbol radius mode.val _ ((lowRhoPhysicalWeight parameters lower positive radius mode.val : ℂ) • _)
  exact congrArg (crossSevenSymbol radius mode.val _) x.symm

end Grad.AnnularSmoothCore
