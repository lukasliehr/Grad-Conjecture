import AKBL9ExactMatrixPhaseAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers Grad.CartesianState
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.BoundaryTrace Grad.SourceBoundaryTrace Grad.SourceCollarFullSource Grad.SourceCollarCoefficients
open Grad.SourceCollarAngular

/-- The literal completed matrix coefficient acts on every continuous axial
circle by its full Fourier convolution. This needs no spatial regularity of
the input circle and keeps all input cells before any projection. -/
theorem startupMatrix_originalProduct_hasSum {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (coefficient : Coefficient L sigma gamma ell 0 inputDimension outputDimension)
    (point : ClosedDisk) (source : ℝ → PhysicalValue inputDimension)
    (continuousSource : Continuous source) (output : ℤ) :
    HasSum (fun input : ℤ => coefficientDerivative coefficient (output-input) zeroDerivativeIndex point
      (angularCoefficient source input))
      (angularCoefficient (fun angle => coefficientPhysicalValue coefficient angle point (source angle)) output) := by
  let entry := fun shift : ℤ => coefficientDerivative coefficient shift zeroDerivativeIndex point
  have norms : Summable (fun shift : ℤ => ‖entry shift‖) :=
    coefficientValue_point_norm_summable admissible coefficient point
  obtain ⟨bound,dominated⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (s := Icc (-Real.pi) Real.pi) continuousSource.continuousOn
  let fields := fun shift angle => cellExponential shift angle • entry shift (source angle)
  have series (angle : ℝ) :
      HasSum (fun shift : ℤ => fields shift angle)
        (coefficientPhysicalValue coefficient angle point (source angle)) := by
    have operatorSeries := (cMapCoefficient_point_summable admissible coefficient angle point).hasSum
    have applied := (ContinuousLinearMap.apply ℂ (PhysicalValue outputDimension) (source angle)).hasSum operatorSeries
    exact applied
  have integrated := angularCoefficient_hasSum fields
    (fun angle => coefficientPhysicalValue coefficient angle point (source angle))
    (fun shift => (cellExponential_smooth shift).continuous.smul ((entry shift).continuous.comp continuousSource))
    (fun shift => ‖entry shift‖ * bound) (norms.mul_right bound)
    (fun shift angle inside => by
      simp only [fields,norm_smul,cellExponential_norm,one_mul]
      exact ((entry shift).le_opNorm (source angle)).trans
        (mul_le_mul_of_nonneg_left (dominated angle inside) (norm_nonneg _)))
    (fun angle _ => series angle) output
  have coefficients (shift : ℤ) : angularCoefficient (fields shift) output =
      entry shift (angularCoefficient source (output-shift)) := by
    change angularCoefficient (fun angle => cellExponential shift angle • entry shift (source angle)) output = _
    rw [angularCoefficient_character_mul,angularCoefficient_valueMap _ _ continuousSource]
  have convolution : HasSum (fun shift : ℤ => entry shift (angularCoefficient source (output-shift)))
      (angularCoefficient (fun angle => coefficientPhysicalValue coefficient angle point (source angle)) output) :=
    integrated.congr_fun (fun shift => (coefficients shift).symm)
  have reindexed := (Equiv.subLeft output).hasSum_iff.mpr convolution
  simpa only [entry,Function.comp_def,Equiv.subLeft_apply,sub_sub_cancel] using reindexed

end Grad.CartesianStartup
