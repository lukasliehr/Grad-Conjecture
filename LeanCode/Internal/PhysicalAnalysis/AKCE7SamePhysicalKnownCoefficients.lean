import AKCE5KnownGraphBulkRepresentatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1700000
open Set Filter MeasureTheory
open scoped Topology ContDiff
namespace Grad.OriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.AnnularCurrentLow Grad.ActualSmoothPhysicalField Grad.ActualPolarEquations
open Grad.AnnularPhysicalFourier Grad.AnnularRegularity Grad.GaugeCoefficients.Physical.Ledger
open Grad.AnnularSourceGraph Grad.AnnularGeneralSourceRegularity Grad.AnnularReconstruction
open Grad.AnnularStrongSolution Grad.AnnularStrongData Grad.AnnularCoupledInverse Grad.AnnularKnownLow
open Grad.AnnularSmoothCore Grad.AnnularWeightedSmoothCore Grad.AnnularHighGenerators Grad.AnnularCurrentSource Grad.AnnularLowEnergy

 theorem fullStrongSevenInput_known_physical (parameters : PhaseParameters) (lower length : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (data : StrongDataCarrier parameters lower positive bounded.le 0 0)
    (field : CoupledSpace lower length positive lengthPositive) :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode : ℤ×ℤ,∀ slot : Fin 3,
      matrixUnit (0 : Fin 1) (⟨slot.val+4,by omega⟩ : Fin 7)
        (lowRhoPhysicalCoefficient parameters lower positive
          (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le data field) radius mode)=
      (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ •
        strongKnownBulk parameters lower positive bounded.le data (slot.castLE (by omega : 3≤4)) mode radius := by
  let unknown := homogeneousCoupledSevenInput parameters length lower lengthPositive positive field
  let known := knownLowSevenPacket lower (strongKnownBulk parameters lower positive bounded.le data)
  filter_upwards [lowRhoPhysicalCoefficient_add_ae parameters lower positive unknown known,
    homogeneousCoupledSevenInput_sameSections parameters lower length positive bounded lengthPositive field,
    knownLowSevenPacket_ae lower (strongKnownBulk parameters lower positive bounded.le data)] with radius added original sources
  intro mode slot
  have unknownSame : lowRhoPhysicalCoefficient parameters lower positive unknown radius mode=
      rawPhysicalSevenVector radius mode
        (sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0 (radialClamp lower bounded.le radius) mode)
        (sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive field 0 (radialClamp lower bounded.le radius) mode) := by
    unfold lowRhoPhysicalCoefficient
    rw [original mode,inv_smul_smul₀ (Complex.ofReal_ne_zero.mpr (lowRhoPhysicalWeight_pos parameters lower positive radius mode).ne')]
  change matrixUnit (0 : Fin 1) (⟨slot.val+4,by omega⟩ : Fin 7)
    (lowRhoPhysicalCoefficient parameters lower positive (unknown+known) radius mode)=_
  rw [added mode,map_add,unknownSame]
  unfold lowRhoPhysicalCoefficient
  rw [sources mode]
  apply PiLp.ext
  intro component
  fin_cases component
  fin_cases slot <;> simp [rawPhysicalSevenVector,matrixUnit_apply,operatorBasis]

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)

def knownGraphPhysicalSection (angular : ℕ) (graph : AnnularTotalSourceH1 parameters 1 lower angular 0 0)
    (mode : ℤ×ℤ) (radius : ℝ) : ComplexEuclidean 1 :=
  (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)⁻¹ •
    ((lowPowerCurve lower (-9/4 : ℝ) positive radius : ℂ) •
      (Real.sqrt radius • radialSectionExtension 1 lower bounded.le
        (totalConjugatedSection parameters 1 lower positive bounded angular 0 0 graph mode) radius))

 theorem knownGraphPhysicalSection_continuous (angular : ℕ) (graph : AnnularTotalSourceH1 parameters 1 lower angular 0 0)
    (mode : ℤ×ℤ) : Continuous (knownGraphPhysicalSection parameters lower positive bounded angular graph mode) := by
  have weight : Continuous (fun radius => (lowRhoPhysicalWeight parameters lower positive radius mode : ℂ)) :=
    Complex.continuous_ofReal.comp ((lowStorageWeight lower positive).continuous.mul
      (Real.continuous_exp.comp (radialPhase_smooth parameters mode.2).continuous))
  exact (weight.inv₀ (fun radius => Complex.ofReal_ne_zero.mpr (lowRhoPhysicalWeight_pos parameters lower positive radius mode).ne')).smul
    ((Complex.continuous_ofReal.comp (lowPowerCurve lower (-9/4 : ℝ) positive).continuous).smul
      (Real.continuous_sqrt.smul (radialSectionExtension 1 lower bounded.le
        (totalConjugatedSection parameters 1 lower positive bounded angular 0 0 graph mode)).continuous))

 theorem knownGraphPhysicalSection_outer (angular : ℕ) (graph : AnnularTotalSourceH1 parameters 1 lower angular 0 0)
    (mode : ℤ×ℤ) : knownGraphPhysicalSection parameters lower positive bounded angular graph mode 1=
      (Real.exp (Grad.PhaseAlgebra.radialPhase parameters 1 mode.2))⁻¹ •
        totalConjugatedSection parameters 1 lower positive bounded angular 0 0 graph mode ⟨1,bounded.le,le_rfl⟩ := by
  unfold knownGraphPhysicalSection lowRhoPhysicalWeight lowStorageWeight lowPowerCurve
  simp only [ContinuousMap.coe_mk,max_eq_right bounded.le,Real.one_rpow,one_mul,Complex.ofReal_one,
    Real.sqrt_one,one_smul,← Complex.ofReal_inv,Complex.coe_smul]
  congr 1
  exact congrArg (totalConjugatedSection parameters 1 lower positive bounded angular 0 0 graph mode)
    (radialClamp_eq lower bounded.le 1 ⟨bounded.le,le_rfl⟩)

end Grad.OriginalCoreRealization
