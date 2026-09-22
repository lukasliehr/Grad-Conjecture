import AIX11ActualBoundaryOrbitDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace Grad.AnnularKernelOrbit
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceBoundaryTrace
open Grad.BoundaryKernelAction Grad.AnnularKernelL2 Grad.AnnularReconstruction Grad.AnnularKernelContinuity

variable {src tgt : ℕ} {parameters : PhaseParameters}

theorem kernelOrbitJet_zero (tau : OrbitParameter) (kernel : FullTwoFrequencyKernel parameters src tgt) :
    kernelOrbitJet tau 0 0 kernel = kernelOrbit tau kernel := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift input
  simp only [kernelOrbitJet, kernelOrbit, displacementKernel_entry, orbitJetFactor, pow_zero, one_mul]

theorem orbitJetFactor_zeroShift (tau : OrbitParameter) (angular cell : ℕ) (positive : 0 < angular + cell) :
    orbitJetFactor tau angular cell (0, 0) = 0 := by
  by_cases first : angular = 0
  · have second : cell ≠ 0 := by omega
    simp [orbitJetFactor, first, zero_pow second]
  · simp [orbitJetFactor, zero_pow first]

theorem kernelOrbit_diagonal (tau : OrbitParameter) (reference : FullTwoFrequencyKernel parameters src tgt)
    (diagonal : ZeroShiftKernel reference) : kernelOrbit tau reference = reference := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift input
  by_cases zero : shift = (0, 0)
  · subst shift
    simp [kernelOrbit, orbitCharacter, orbitAngle]
  · change orbitCharacter tau shift • reference.entry shift input = _
    rw [diagonal shift zero input]
    module

/-- A positive orbital jet of the actual kernel is exactly the jet of its
circular difference; no constant reference contribution enters a one-high estimate. -/
theorem kernelOrbitJet_referenceDifference (tau : OrbitParameter) (angular cell : ℕ)
    (positive : 0 < angular + cell) (actual reference : FullTwoFrequencyKernel parameters src tgt)
    (diagonal : ZeroShiftKernel reference) :
    kernelOrbitJet tau angular cell actual = kernelOrbitJet tau angular cell (fullKernelSub actual reference) := by
  apply FullTwoFrequencyKernel.ext_entry
  intro shift input
  change orbitJetFactor tau angular cell shift • actual.entry shift input =
    orbitJetFactor tau angular cell shift • (actual.entry shift input - reference.entry shift input)
  by_cases zero : shift = (0, 0)
  · subst shift
    rw [orbitJetFactor_zeroShift tau angular cell positive]
    module
  · rw [diagonal shift zero input, sub_zero]

theorem radialOrbitJetAction_referenceMoment_bound (parameters : PhaseParameters)
    (kernel reference : (r : RadialPoint) → RadialKernel parameters r src tgt)
    (regular : RegularKernelFamily kernel)
    (errorRegular : RegularKernelFamily (fun r => fullKernelSub (kernel r) (reference r)))
    (diagonal : ∀ r, ZeroShiftKernel (reference r))
    (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1)
    (tau : OrbitParameter) (angular cell : ℕ) (orderPositive : 0 < angular + cell)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (moment : ∀ r, fullKernelMoment (radialKernelParameters parameters r) (power + (angular + cell))
      (fullKernelSub (kernel r) (reference r)) ≤ constant) :
    ‖radialOrbitJetAction parameters kernel regular power lower positive bounded tau angular cell‖ ≤ constant := by
  have same : radialOrbitJetAction parameters kernel regular power lower positive bounded tau angular cell =
      radialOrbitJetAction parameters (fun r => fullKernelSub (kernel r) (reference r)) errorRegular
        power lower positive bounded tau angular cell :=
    regularRadialBulkAction_congr parameters power lower positive bounded _ _ _ _
      (fun radius => kernelOrbitJet_referenceDifference tau angular cell orderPositive _ _ (diagonal radius))
  rw [same]
  exact radialOrbitJetAction_norm_le parameters _ errorRegular power lower positive bounded tau angular cell
    constant nonnegative moment

theorem radialOrbitJetAction_zero (parameters : PhaseParameters)
    (kernel : (r : RadialPoint) → RadialKernel parameters r src tgt) (regular : RegularKernelFamily kernel)
    (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (tau : OrbitParameter) :
    radialOrbitJetAction parameters kernel regular power lower positive bounded tau 0 0 =
      radialOrbitAction parameters kernel regular power lower positive bounded tau :=
  regularRadialBulkAction_congr parameters power lower positive bounded _ _ _ _
    (fun radius => kernelOrbitJet_zero tau (kernel radius))

/-- The actual unitarily conjugated completed bulk orbit has the displayed
operator derivative; this identifies mixed jets with genuine orbit derivatives. -/
theorem radialOrbitAction_hasFDerivAt (parameters : PhaseParameters)
    (kernel : (r : RadialPoint) → RadialKernel parameters r src tgt) (regular : RegularKernelFamily kernel)
    (power : ℕ) (lower : ℝ) (positive : 0 < lower) (bounded : lower ≤ 1) (tau : OrbitParameter) :
    HasFDerivAt (radialOrbitAction parameters kernel regular power lower positive bounded)
      (orbitDifferential
        (radialOrbitJetAction parameters kernel regular power lower positive bounded tau 1 0)
        (radialOrbitJetAction parameters kernel regular power lower positive bounded tau 0 1)) tau := by
  have derivative := radialOrbitJetAction_hasFDerivAt parameters kernel regular power lower positive bounded tau 0 0
  simpa only [radialOrbitJetAction_zero, zero_add] using derivative

end Grad.AnnularKernelOrbit
