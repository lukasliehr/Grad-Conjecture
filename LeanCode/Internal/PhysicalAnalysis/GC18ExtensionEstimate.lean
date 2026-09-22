import GC18ExtensionAlgebra

noncomputable section

set_option maxHeartbeats 2200000

namespace Grad.GaugeCoefficients.Physical.RadialLedger

open Grad.ClosedJets Grad.CartesianState Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Radial
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

def adjugateProfile (gauge : ℕ → ℝ) : EstimateProfile :=
  let diagonal := ((liftedEntryProfile 6 0 0 (unitProfile (deltaConstant gauge))).add
    (liftedEntryProfile 6 1 1 (unitProfile (deltaConstant gauge)))).add
      (liftedEntryProfile 6 2 2 (unitProfile (muConstant gauge)))
  let firstCross := (fixedProfile tangentColumnConstant).comp 6 ((zeroProfile (etaConstant gauge)).comp 6
    (constantProfile (matrixUnit (input := 3) (output := 1) 0 2)))
  let secondCross := (constantProfile (matrixUnit (input := 1) (output := 3) 2 0)).comp 6
    ((zeroProfile (nuConstant gauge)).comp 6 (fixedProfile tangentRowConstant))
  (diagonal.add (firstCross.smul (-1))).add (secondCross.smul (-1))

theorem adjugate_estimate {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters field rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + 4)) :
    FamilyEstimate parameters field rho epsilon 6 (adjugateProfile constants)
      (adjugateFamily admissible gauge) (identityFamily L parameters.sigma0 parameters.gamma ell 3) := by
  have muEstimate := unitPerturbation_estimate parameters field rho epsilon 6 1 _
    (muDeviation_coherent admissible gauge coherent) (muConstant constants) (muConstant_nonnegative nonnegative)
    (muDeviation_bound parameters admissible field rho epsilon gauge constants bound)
  have deltaEstimate := unitPerturbation_estimate parameters field rho epsilon 6 1 _
    (deltaDeviation_coherent admissible gauge coherent) (deltaConstant constants) (deltaConstant_nonnegative nonnegative)
    (deltaDeviation_bound parameters admissible field rho epsilon gauge constants nonnegative bound)
  have etaEstimate := zeroReference_estimate parameters field rho epsilon 6 _
    (etaCoefficient_coherent admissible gauge coherent) (etaConstant constants) (etaConstant_nonnegative nonnegative)
    (etaCoefficient_bound parameters admissible field rho epsilon gauge constants bound)
  have nuEstimate := zeroReference_estimate parameters field rho epsilon 6 _
    (nuCoefficient_coherent admissible gauge coherent) (nuConstant constants) (nuConstant_nonnegative nonnegative)
    (nuCoefficient_bound parameters admissible field rho epsilon gauge constants bound)
  have tangentColumnEstimate := fixedFamily_estimate parameters field rho epsilon 6 _
    (tangentColumn_coherent L parameters.sigma0 parameters.gamma ell) tangentColumnConstant tangentColumnConstant_nonnegative
    (tangentColumn_bound L parameters.sigma0 parameters.gamma ell)
  have tangentRowEstimate := fixedFamily_estimate parameters field rho epsilon 6 _
    (tangentRow_coherent L parameters.sigma0 parameters.gamma ell) tangentRowConstant tangentRowConstant_nonnegative
    (tangentRow_bound L parameters.sigma0 parameters.gamma ell)
  have scalarColumnEstimate := constantFamily_estimate parameters admissible field rho epsilon 6
    (matrixUnit (input := 1) (output := 3) 2 0)
  have scalarRowEstimate := constantFamily_estimate parameters admissible field rho epsilon 6
    (matrixUnit (input := 3) (output := 1) 0 2)
  have diagonal := ((liftedEntry_estimate admissible low 0 0 deltaEstimate).add
    (liftedEntry_estimate admissible low 1 1 deltaEstimate)).add (liftedEntry_estimate admissible low 2 2 muEstimate)
  have firstCross := tangentColumnEstimate.comp admissible low (etaEstimate.comp admissible low scalarRowEstimate)
  have secondCross := scalarColumnEstimate.comp admissible low (nuEstimate.comp admissible low tangentRowEstimate)
  have result := (diagonal.add (firstCross.smul (-1))).add (secondCross.smul (-1))
  change FamilyEstimate parameters field rho epsilon 6 (adjugateProfile constants)
    (fun grade => ((liftedEntry admissible 0 0 (deltaCoefficient admissible gauge) grade +
      liftedEntry admissible 1 1 (deltaCoefficient admissible gauge) grade +
      liftedEntry admissible 2 2 (muCoefficient admissible gauge) grade) +
      (-1 : ℂ) • composeFamily admissible (tangentColumnFamily L parameters.sigma0 parameters.gamma ell)
        (composeFamily admissible (etaCoefficient admissible gauge) (scalarRowFamily L parameters.sigma0 parameters.gamma ell)) grade) +
      (-1 : ℂ) • composeFamily admissible (scalarColumnFamily L parameters.sigma0 parameters.gamma ell)
        (composeFamily admissible (nuCoefficient admissible gauge) (tangentRowFamily L parameters.sigma0 parameters.gamma ell)) grade)
    (fun grade => ((liftedEntry admissible 0 0 (identityFamily L parameters.sigma0 parameters.gamma ell 1) grade +
      liftedEntry admissible 1 1 (identityFamily L parameters.sigma0 parameters.gamma ell 1) grade +
      liftedEntry admissible 2 2 (identityFamily L parameters.sigma0 parameters.gamma ell 1) grade) +
      (-1 : ℂ) • composeFamily admissible (tangentColumnFamily L parameters.sigma0 parameters.gamma ell)
        (composeFamily admissible (zeroFamily L parameters.sigma0 parameters.gamma ell 1 1)
          (scalarRowFamily L parameters.sigma0 parameters.gamma ell)) grade) +
      (-1 : ℂ) • composeFamily admissible (scalarColumnFamily L parameters.sigma0 parameters.gamma ell)
        (composeFamily admissible (zeroFamily L parameters.sigma0 parameters.gamma ell 1 1)
          (tangentRowFamily L parameters.sigma0 parameters.gamma ell)) grade) at result
  simp only [composeFamily_zero_left, composeFamily_zero_right, zeroFamily, smul_zero, add_zero] at result
  rw [liftedDiagonal_identity admissible] at result
  change FamilyEstimate parameters field rho epsilon 6 (adjugateProfile constants)
    (fun grade => (liftedEntry admissible 0 0 (deltaCoefficient admissible gauge) grade +
      liftedEntry admissible 1 1 (deltaCoefficient admissible gauge) grade +
      liftedEntry admissible 2 2 (muCoefficient admissible gauge) grade) -
      composeFamily admissible (tangentColumnFamily L parameters.sigma0 parameters.gamma ell)
        (composeFamily admissible (etaCoefficient admissible gauge) (scalarRowFamily L parameters.sigma0 parameters.gamma ell)) grade -
      composeFamily admissible (scalarColumnFamily L parameters.sigma0 parameters.gamma ell)
        (composeFamily admissible (nuCoefficient admissible gauge) (tangentRowFamily L parameters.sigma0 parameters.gamma ell)) grade)
    (identityFamily L parameters.sigma0 parameters.gamma ell 3)
  simpa only [neg_one_smul, ← sub_eq_add_neg] using result

def complementExtensionProfile (gauge : ℕ → ℝ) : EstimateProfile :=
  (scalarLiftThreeProfile 6 (unitProfile (determinantInverseConstant gauge))).comp 6 (adjugateProfile gauge)

def complementExtensionConstant (gauge : ℕ → ℝ) (grade : ℕ) : ℝ :=
  |(complementExtensionProfile gauge).deviation grade|

theorem complementExtension_estimate {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters field rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + 4))
    (small : physicalBudget parameters field rho epsilon 6 ≤ determinantLowRadius constants) :
    FamilyEstimate parameters field rho epsilon 6 (complementExtensionProfile constants)
      (complementExtensionFamily admissible gauge) (identityFamily L parameters.sigma0 parameters.gamma ell 3) := by
  have inverseEstimate := determinantInverse_estimate parameters admissible field rho epsilon gauge coherent constants nonnegative low bound small
  have adjugateEstimate := adjugate_estimate parameters admissible field rho epsilon gauge coherent constants nonnegative low bound
  have result := (scalarLiftThree_estimate admissible low inverseEstimate).comp admissible low adjugateEstimate
  change FamilyEstimate parameters field rho epsilon 6 (complementExtensionProfile constants)
    (complementExtensionFamily admissible gauge)
    (composeFamily admissible (scalarLiftFamily admissible 3 (identityFamily L parameters.sigma0 parameters.gamma ell 1))
      (identityFamily L parameters.sigma0 parameters.gamma ell 3)) at result
  rw [scalarLift_three_identity, composeFamily_identity_identity] at result
  exact result

theorem complementExtension_deviation_bound {L ell : ℝ} (parameters : PhaseParameters)
    (admissible : Admissible L parameters.sigma0 parameters.gamma ell)
    (field : ACore parameters 3) (rho epsilon : ℝ)
    (gauge : CoefficientFamily L parameters.sigma0 parameters.gamma ell 3 3)
    (coherent : FamilyCoherent gauge) (constants : ℕ → ℝ) (nonnegative : ∀ grade, 0 ≤ constants grade)
    (low : physicalBudget parameters field rho epsilon 6 ≤ 1)
    (bound : ∀ grade, ‖gauge grade‖ ≤ constants grade * physicalBudget parameters field rho epsilon (grade + 4))
    (small : physicalBudget parameters field rho epsilon 6 ≤ determinantLowRadius constants) (grade : ℕ) :
    ‖complementExtensionFamily admissible gauge grade - identityFamily L parameters.sigma0 parameters.gamma ell 3 grade‖ ≤
      complementExtensionConstant constants grade * physicalBudget parameters field rho epsilon (grade + 6) :=
  (complementExtension_estimate parameters admissible field rho epsilon gauge coherent constants nonnegative low bound small).absoluteBound grade

end Grad.GaugeCoefficients.Physical.RadialLedger
