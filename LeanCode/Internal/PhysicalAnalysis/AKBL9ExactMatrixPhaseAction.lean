import AKBL8SameInfiniteCellKernel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 900000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.CartesianStartup
open Grad.PDEBootstrap Grad.ClosedJets Grad.GenericCarriers
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.Compensated Grad.AnalyticWeights.Calculus Grad.AnalyticWeights.Higher

 theorem startupMatrixCoefficient_zero {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (input output : ℤ) (point : ClosedDisk) :
    startupDerivativeCoefficient admissible family coherent zeroDerivativeIndex input (output-input) point =
      (weightRatio sigma gamma ell output input point.val : ℂ) •
        coefficientDerivative (family 0) (output-input) zeroDerivativeIndex point := by
  have literal := actualCoefficientJet_coherent admissible family coherent (output-input) zeroDerivativeIndex point
  change smoothOperatorDerivative (actualCoefficientJet admissible family coherent (output-input)) (0,0) point = _ at literal
  rw [smoothOperator_zero] at literal
  change (((scaledCellWeight L ell input ^ (0-1) : ℝ) : ℂ)⁻¹) •
    smoothOperatorDerivative (startupConjugatedCoefficientJet admissible family coherent input (output-input)) (0,0) point = _
  simp only [Nat.zero_sub,pow_zero,Complex.ofReal_one,inv_one,one_smul,smoothOperator_zero]
  rw [startupConjugatedCoefficientJet_value,literal,show input+(output-input)=output by omega]

 theorem startupMatrixCoefficient_weighted {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (input output : ℤ) (point : Spatial) (inside : point ∈ openUnitDisk)
    (value : PhysicalValue inputDimension) :
    closedDiskLift (startupDerivativeCoefficient admissible family coherent zeroDerivativeIndex input (output-input)) point
      (physicalWeight sigma gamma ell input point • value) =
      physicalWeight sigma gamma ell output point •
        closedDiskLift (coefficientDerivative (family 0) (output-input) zeroDerivativeIndex) point value := by
  simp only [closedDiskLift,dif_pos (openDiskMembershipClosed point inside)]
  rw [startupMatrixCoefficient_zero]
  simp only [smul_apply,RCLike.real_smul_eq_coe_smul (K := ℂ),map_smul,weightRatio,inverseWeight,
    Complex.ofReal_mul,Complex.ofReal_inv,smul_smul]
  congr 1
  change (physicalWeight sigma gamma ell input point : ℂ) *
    ((physicalWeight sigma gamma ell output point : ℂ) * (physicalWeight sigma gamma ell input point : ℂ)⁻¹) =
    (physicalWeight sigma gamma ell output point : ℂ)
  have nonzero : (physicalWeight sigma gamma ell input point : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero (physicalPhase sigma gamma ell input point))
  field_simp [nonzero]

/-- Exact full-cell conjugation of an actual matrix product. The caller
provides the literal unconjugated Fourier product series; the accepted Schur
kernel and exact original phase prove its weighted L2 realization. -/
 theorem startupMatrix_weighted_same {L sigma gamma ell : ℝ}
    (admissible : Admissible L sigma gamma ell) {inputDimension outputDimension : ℕ}
    (family : CoefficientFamily L sigma gamma ell inputDimension outputDimension)
    (coherent : FamilyCoherent family) (field : StartupL2 inputDimension)
    (raw : ℤ → Spatial → PhysicalValue inputDimension) (product : ℤ → Spatial → PhysicalValue outputDimension)
    (same : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ input : ℤ,
      field point input = physicalWeight sigma gamma ell input point • raw input point)
    (productSeries : ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ output : ℤ,
      HasSum (fun input : ℤ => closedDiskLift
        (coefficientDerivative (family 0) (output-input) zeroDerivativeIndex) point (raw input point))
        (product output point)) :
    ∀ᵐ point ∂volume.restrict openUnitDisk, ∀ output : ℤ,
      originalMatrixKernel admissible family coherent field point output =
        physicalWeight sigma gamma ell output point • product output point := by
  filter_upwards [startupMatrix_allCell_hasSum_ae admissible family coherent field,same,productSeries,
    ae_restrict_mem openUnitDisk_isOpen.measurableSet] with point kernel source actual inside
  intro output
  have weighted := (actual output).const_smul (physicalWeight sigma gamma ell output point)
  apply (kernel output).unique
  apply weighted.congr_fun
  intro input
  rw [source input,startupMatrixCoefficient_weighted admissible family coherent input output point inside]

end Grad.CartesianStartup
