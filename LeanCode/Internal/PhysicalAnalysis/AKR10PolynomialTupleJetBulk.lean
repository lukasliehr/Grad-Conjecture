import AKR8ExactHighEnergyTupleCoordinates

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
open scoped ContDiff ENNReal
namespace Grad.AnnularOriginalCoreRealization
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.SourceBoundaryTrace Grad.BoundaryKernelAction Grad.AnnularSourceGraph Grad.AnnularPhysicalFourier
open Grad.AnnularOriginalSmoothCore
open Grad.GaugeCoefficients.Physical.WeightedTrace

variable (parameters : PhaseParameters) (lower : ℝ) (positive : 0 < lower) (bounded : lower < 1)
    (tuple : OriginalSmoothTuple parameters lower) (slot : Fin 4)

/-- Polynomial Fourier factors of genuine radial jets remain square
summable at the SAME analytic width. -/
theorem tuplePolynomialJet_summable {Index : Type*} (modes : Index → ℤ × ℤ)
    (injective : Function.Injective modes) (order grade : ℕ) (coefficient : Index → ℂ)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (growth : ∀ index, ‖coefficient index‖ ≤ constant * annularFrequency (modes index).1 (modes index).2 ^ grade) :
    Summable (fun index => ‖coefficient index • tupleConjugatedJetL2 parameters lower positive bounded tuple slot order (modes index)‖) := by
  have sum := ((tupleConjugatedJet_summable parameters lower bounded tuple slot order grade).mul_left constant).comp_injective injective
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ sum
  intro index
  rw [norm_smul]
  have normBound : ‖tupleConjugatedJetL2 parameters lower positive bounded tuple slot order (modes index)‖ ≤
      ‖tupleConjugatedJetSection parameters lower bounded tuple slot order (modes index)‖ := by
    exact (radialSectionL2Linear_bound 1 lower positive bounded.le _).trans_eq (one_mul _)
  have bound := mul_le_mul (growth index) normBound (norm_nonneg _)
    (mul_nonneg nonnegative (pow_nonneg (Grad.SourceBoundaryTrace.annularFrequency_pos (modes index)).le _))
  simpa only [Function.comp_apply,mul_assoc] using bound

def tuplePolynomialJetBulk {Index : Type*} (modes : Index → ℤ × ℤ)
    (injective : Function.Injective modes) (order grade : ℕ) (coefficient : Index → ℂ)
    (constant : ℝ) (nonnegative : 0 ≤ constant)
    (growth : ∀ index, ‖coefficient index‖ ≤ constant * annularFrequency (modes index).1 (modes index).2 ^ grade) :
    lp (fun _ : Index => CollarL2 (ComplexEuclidean 1) lower) 2 :=
  ⟨fun index => coefficient index • tupleConjugatedJetL2 parameters lower positive bounded tuple slot order (modes index), by
    have one : Memℓp (fun index => coefficient index •
        tupleConjugatedJetL2 parameters lower positive bounded tuple slot order (modes index)) 1 := by
      apply memℓp_gen
      simpa only [ENNReal.toReal_one,Real.rpow_one] using tuplePolynomialJet_summable parameters lower positive bounded tuple slot
        modes injective order grade coefficient constant nonnegative growth
    exact one.of_exponent_ge (by norm_num)⟩

end Grad.AnnularOriginalCoreRealization
