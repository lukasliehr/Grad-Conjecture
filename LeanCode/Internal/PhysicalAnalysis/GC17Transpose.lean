import GC17FiniteSums

noncomputable section

set_option maxHeartbeats 1400000

open scoped BigOperators

namespace Grad.GaugeCoefficients.Physical.Ledger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame

theorem matrixTranspose_single_formula {input output : ℕ} (matrix : Matrix (Fin output) (Fin input) ℂ) :
    (∑ pair : Fin input × Fin output,
      Matrix.single pair.1 pair.2 (1 : ℂ) * (matrix * Matrix.single pair.1 pair.2 (1 : ℂ))) = matrix.transpose := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Matrix.mul_assoc, Matrix.single_mul_mul_single, one_mul, mul_one]
  exact Matrix.sum_sum_single matrix.transpose

def transposeFamily {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (family : CoefficientFamily L sigma gamma ell input output) :
    CoefficientFamily L sigma gamma ell output input :=
  fun grade => ∑ pair : Fin input × Fin output,
    coefficientComposition admissible grade
      (constantFamily L sigma gamma ell (matrixUnit pair.1 pair.2) grade)
      (coefficientComposition admissible grade (family grade)
        (constantFamily L sigma gamma ell (matrixUnit pair.1 pair.2) grade))

theorem transposeFamily_coherent {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family) :
    FamilyCoherent (transposeFamily admissible family) :=
  familyCoherent_sum _ (fun pair => (constantFamily_coherent L sigma gamma ell (matrixUnit pair.1 pair.2)).comp
    admissible (coherent.comp admissible (constantFamily_coherent L sigma gamma ell (matrixUnit pair.1 pair.2))))

def transposeProfile (offset input output : ℕ) (profile : EstimateProfile) : EstimateProfile :=
  EstimateProfile.sum (fun pair : Fin input × Fin output =>
    (constantProfile (matrixUnit pair.1 pair.2)).comp offset
      (profile.comp offset (constantProfile (matrixUnit pair.1 pair.2))))

theorem transposeFamily_estimate {L ell : ℝ} {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {offset input output : ℕ} {profile : EstimateProfile}
    {actual reference : CoefficientFamily L parameters.sigma0 parameters.gamma ell input output}
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (low : physicalBudget parameters field rho epsilon offset ≤ 1)
    (estimate : FamilyEstimate parameters field rho epsilon offset profile actual reference) :
    FamilyEstimate parameters field rho epsilon offset (transposeProfile offset input output profile)
      (transposeFamily admissible actual) (transposeFamily admissible reference) :=
  familyEstimate_sum _ _ _ (fun pair => FamilyEstimate.comp admissible low
    (constantFamily_estimate parameters admissible field rho epsilon offset (matrixUnit pair.1 pair.2))
    (FamilyEstimate.comp admissible low estimate
      (constantFamily_estimate parameters admissible field rho epsilon offset (matrixUnit pair.1 pair.2))))

theorem transposeFamily_physicalValue {L sigma gamma ell : ℝ} (admissible : Admissible L sigma gamma ell)
    {input output : ℕ} (family : CoefficientFamily L sigma gamma ell input output) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    operatorMatrix (coefficientPhysicalValue (transposeFamily admissible family grade) angle point) =
      (operatorMatrix (coefficientPhysicalValue (family grade) angle point)).transpose := by
  let fixed (pair : Fin input × Fin output) := constantFamily L sigma gamma ell (matrixUnit pair.1 pair.2)
  have fixedCoherent (pair : Fin input × Fin output) : FamilyCoherent (fixed pair) :=
    constantFamily_coherent L sigma gamma ell (matrixUnit pair.1 pair.2)
  have termCoherent (pair : Fin input × Fin output) : FamilyCoherent (fun order =>
      coefficientComposition admissible order (fixed pair order)
        (coefficientComposition admissible order (family order) (fixed pair order))) :=
    (fixedCoherent pair).comp admissible (coherent.comp admissible (fixedCoherent pair))
  change operatorMatrix (coefficientPhysicalValue (∑ pair : Fin input × Fin output,
    coefficientComposition admissible grade (fixed pair grade)
      (coefficientComposition admissible grade (family grade) (fixed pair grade))) angle point) = _
  rw [family_physicalValue_sum admissible _ termCoherent, operatorMatrix_sum]
  calc
    _ = ∑ pair : Fin input × Fin output,
        Matrix.single pair.1 pair.2 (1 : ℂ) *
          (operatorMatrix (coefficientPhysicalValue (family grade) angle point) * Matrix.single pair.1 pair.2 (1 : ℂ)) := by
      apply Finset.sum_congr rfl
      intro pair _
      rw [family_physicalValue_comp admissible _ _ (fixedCoherent pair)
          (coherent.comp admissible (fixedCoherent pair)),
        family_physicalValue_comp admissible _ _ coherent (fixedCoherent pair)]
      change operatorMatrix ((coefficientPhysicalValue (constantFamily L sigma gamma ell (matrixUnit pair.1 pair.2) grade)
          angle point).comp ((coefficientPhysicalValue (family grade) angle point).comp
            (coefficientPhysicalValue (constantFamily L sigma gamma ell (matrixUnit pair.1 pair.2) grade) angle point))) = _
      rw [constantFamily_physicalValue admissible, operatorMatrix_comp, operatorMatrix_comp,
        operatorMatrix_matrixUnit]
    _ = _ := matrixTranspose_single_formula _

end Grad.GaugeCoefficients.Physical.Ledger
