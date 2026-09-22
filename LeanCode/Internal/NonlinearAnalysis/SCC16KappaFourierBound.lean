import SCC15KappaLaurent

noncomputable section
open scoped BigOperators

namespace Grad.SourceCollarCoefficients
open Grad.ClosedJets Grad.CartesianState Grad.GenericCarriers
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.Allocation
open Grad.SourceCollarAngular

def kappaFourierTerm (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (slot : Fin 2 × Fin 2) (radial : ℕ) (radius : ℝ) :
    ℤ × ℤ → ComplexEuclidean 1 :=
  coefficientPolarFourier parameters
    (mappedCofactorFamily parameters L epsilon field (scalarRowMapping (tangentialLaurentVector slot.1)))
    (mappedCofactorFamily_coherent parameters L rho epsilon field _ low)
    (kappaLaurentRight component slot.2) radial radius ∘
      angularModeTranslation (kappaLaurentFrequency component slot)

/-- Literal finite Laurent contractions of the actual signed-cofactor
deviation. Their pointwise and derivative correspondence is proved downstream. -/
def kappaFourier (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (component : Fin 3) (radial : ℕ) (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  ∑ slot, kappaFourierTerm parameters L rho epsilon field low component slot radial radius mode

def kappaFourierTermConstant (parameters : PhaseParameters) (L : ℝ) (tangential radial : ℕ)
    (component : Fin 3) (slot : Fin 2 × Fin 2) : ℝ :=
  (1 + |(kappaLaurentFrequency component slot : ℝ)|) ^ tangential *
    (coefficientFourierConstant tangential radial *
      mappedCofactorConstant parameters L (scalarRowMapping (tangentialLaurentVector slot.1))
        (tangential + radial + 1) * ‖kappaLaurentRight component slot.2‖)

def kappaFourierConstant (parameters : PhaseParameters) (L : ℝ) (tangential radial : ℕ) : ℝ :=
  1 + ∑ component : Fin 3, ∑ slot : Fin 2 × Fin 2,
    |kappaFourierTermConstant parameters L tangential radial component slot|

theorem kappaFourierConstant_pos (parameters : PhaseParameters) (L : ℝ) (tangential radial : ℕ) :
    0 < kappaFourierConstant parameters L tangential radial := by
  unfold kappaFourierConstant
  positivity

theorem kappaFourierTerm_summable (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (tangential radial : ℕ) (component : Fin 3) (slot : Fin 2 × Fin 2)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (polarFourierMass parameters tangential radius
      (kappaFourierTerm parameters L rho epsilon field low component slot radial radius)) :=
  polarFourierMass_shift_summable parameters tangential radius _
    (coefficient_fourier_summable parameters _
      (mappedCofactorFamily_coherent parameters L rho epsilon field _ low)
      (kappaLaurentRight component slot.2) tangential radial radius nonnegative bounded) _

theorem kappaFourierTerm_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (tangential radial : ℕ) (component : Fin 3) (slot : Fin 2 × Fin 2)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ∑' mode, polarFourierMass parameters tangential radius
        (kappaFourierTerm parameters L rho epsilon field low component slot radial radius) mode ≤
      kappaFourierTermConstant parameters L tangential radial component slot *
        physicalBudget parameters field rho epsilon (tangential + radial + 5) := by
  have summable := coefficient_fourier_summable parameters _
    (mappedCofactorFamily_coherent parameters L rho epsilon field
      (scalarRowMapping (tangentialLaurentVector slot.1)) low)
    (kappaLaurentRight component slot.2) tangential radial radius nonnegative bounded
  have shifted := polarFourierMass_shift_bound parameters tangential radius _ summable
    (kappaLaurentFrequency component slot)
  have original := mappedCofactor_fourier_bound parameters L rho epsilon field
    (scalarRowMapping (tangentialLaurentVector slot.1)) (kappaLaurentRight component slot.2)
    low tangential radial radius nonnegative bounded
  have bound := mul_le_mul_of_nonneg_left original
    (by positivity : 0 ≤ (1 + |(kappaLaurentFrequency component slot : ℝ)|) ^ tangential)
  exact shifted.trans (bound.trans_eq (by unfold kappaFourierTermConstant; ring))

theorem kappaFourier_summable (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (tangential radial : ℕ) (component : Fin 3)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    Summable (polarFourierMass parameters tangential radius
      (kappaFourier parameters L rho epsilon field low component radial radius)) :=
  polarFourierMass_sum_summable parameters tangential radius _
    (fun slot => kappaFourierTerm_summable parameters L rho epsilon field low
      tangential radial component slot radius nonnegative bounded)

/-- Exact BS40 bound including every angular and axial displacement, all
radial orders, original analytic width and one B6 ball chosen before t,k. -/
theorem kappaFourier_bound (parameters : PhaseParameters) (L rho epsilon : ℝ)
    (field : ACore parameters 3)
    (low : physicalBudget parameters field rho epsilon 6 ≤ originalCoefficientLowRadius parameters L)
    (tangential radial : ℕ) (component : Fin 3)
    (radius : ℝ) (nonnegative : 0 ≤ radius) (bounded : radius ≤ 1) :
    ∑' mode, polarFourierMass parameters tangential radius
        (kappaFourier parameters L rho epsilon field low component radial radius) mode ≤
      kappaFourierConstant parameters L tangential radial *
        physicalBudget parameters field rho epsilon (tangential + radial + 5) := by
  have total := polarFourierMass_sum_bound parameters tangential radius _
    (fun slot => kappaFourierTerm_summable parameters L rho epsilon field low
      tangential radial component slot radius nonnegative bounded)
  have terms := Finset.sum_le_sum (s := Finset.univ) (fun slot _ =>
    kappaFourierTerm_bound parameters L rho epsilon field low tangential radial component slot
      radius nonnegative bounded)
  rw [← Finset.sum_mul] at terms
  have componentBound : (∑ slot, kappaFourierTermConstant parameters L tangential radial component slot) ≤
      kappaFourierConstant parameters L tangential radial := by
    have absolute := Finset.sum_le_sum (s := Finset.univ) (fun slot _ =>
      le_abs_self (kappaFourierTermConstant parameters L tangential radial component slot))
    have componentSum := Finset.single_le_sum
      (f := fun component : Fin 3 => ∑ slot : Fin 2 × Fin 2,
        |kappaFourierTermConstant parameters L tangential radial component slot|)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ component)
    exact absolute.trans (componentSum.trans (by unfold kappaFourierConstant; linarith))
  exact total.trans (terms.trans (mul_le_mul_of_nonneg_right componentBound
    (physicalBudget_nonnegative parameters field rho epsilon _)))

end Grad.SourceCollarCoefficients
