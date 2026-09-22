import AKQ16CubicMatrixEntryRecipe

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open scoped BigOperators
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Frame Grad.GaugeCoefficients.Physical.Ledger

def cubicEntryTermFamily {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    (family : CoefficientFamily 1 sigma gamma 1 2 2) (term : CubicEntryTerm) : CoefficientFamily 1 sigma gamma 1 2 2 :=
  composeFamily admissible
    (constantFamily 1 sigma gamma 1 (matrixUnit term.targetRow term.sourceRow))
    (composeFamily admissible family (constantFamily 1 sigma gamma 1 (matrixUnit term.sourceColumn term.targetColumn)))

def cubicEntryTermProfile (profile : EstimateProfile) (term : CubicEntryTerm) : EstimateProfile :=
  (constantProfile (matrixUnit term.targetRow term.sourceRow)).comp 4
    (profile.comp 4 (constantProfile (matrixUnit term.sourceColumn term.targetColumn)))

def cubicMatrixFamily {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    (family : CoefficientFamily 1 sigma gamma 1 2 2) : CoefficientFamily 1 sigma gamma 1 2 2 :=
  fun grade => ∑ index : Fin 8, (cubicEntryTerms index).scalar • cubicEntryTermFamily admissible family (cubicEntryTerms index) grade

def cubicMatrixProfile (profile : EstimateProfile) : EstimateProfile :=
  EstimateProfile.sum (fun index : Fin 8 => (cubicEntryTermProfile profile (cubicEntryTerms index)).smul (cubicEntryTerms index).scalar)

theorem cubicEntryTermFamily_coherent {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    (family : CoefficientFamily 1 sigma gamma 1 2 2) (coherent : FamilyCoherent family) (term : CubicEntryTerm) :
    FamilyCoherent (cubicEntryTermFamily admissible family term) :=
  (constantFamily_coherent 1 sigma gamma 1 (matrixUnit term.targetRow term.sourceRow)).comp admissible
    (coherent.comp admissible (constantFamily_coherent 1 sigma gamma 1 (matrixUnit term.sourceColumn term.targetColumn)))

theorem cubicMatrixFamily_coherent {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    (family : CoefficientFamily 1 sigma gamma 1 2 2) (coherent : FamilyCoherent family) :
    FamilyCoherent (cubicMatrixFamily admissible family) :=
  familyCoherent_sum _ (fun index =>
    (cubicEntryTermFamily_coherent admissible family coherent (cubicEntryTerms index)).smul (cubicEntryTerms index).scalar)

theorem cubicMatrixFamily_estimate {parameters : PhaseParameters} {field : ACore parameters 3}
    {rho epsilon : ℝ} {profile : EstimateProfile}
    {actual reference : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 2 2}
    (low : physicalBudget parameters field rho epsilon 4 ≤ 1)
    (estimate : FamilyEstimate parameters field rho epsilon 4 profile actual reference) :
    FamilyEstimate parameters field rho epsilon 4 (cubicMatrixProfile profile)
      (cubicMatrixFamily (Grad.SourceCollarCoefficients.unitDiskAdmissible parameters) actual)
      (cubicMatrixFamily (Grad.SourceCollarCoefficients.unitDiskAdmissible parameters) reference) :=
  familyEstimate_sum _ _ _ (fun index =>
    (FamilyEstimate.comp (Grad.SourceCollarCoefficients.unitDiskAdmissible parameters) low
      (constantFamily_estimate parameters (Grad.SourceCollarCoefficients.unitDiskAdmissible parameters) field rho epsilon 4
        (matrixUnit (cubicEntryTerms index).targetRow (cubicEntryTerms index).sourceRow))
      (FamilyEstimate.comp (Grad.SourceCollarCoefficients.unitDiskAdmissible parameters) low estimate
        (constantFamily_estimate parameters (Grad.SourceCollarCoefficients.unitDiskAdmissible parameters) field rho epsilon 4
          (matrixUnit (cubicEntryTerms index).sourceColumn (cubicEntryTerms index).targetColumn)))).smul (cubicEntryTerms index).scalar)

theorem cubicEntryTermFamily_matrix {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    (family : CoefficientFamily 1 sigma gamma 1 2 2) (coherent : FamilyCoherent family) (term : CubicEntryTerm)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (cubicEntryTermFamily admissible family term) grade angle point =
      Matrix.single term.targetRow term.sourceRow 1 *
        (familyMatrix family grade angle point * Matrix.single term.sourceColumn term.targetColumn 1) := by
  have left := constantFamily_coherent 1 sigma gamma 1 (matrixUnit term.targetRow term.sourceRow)
  have right := constantFamily_coherent 1 sigma gamma 1 (matrixUnit term.sourceColumn term.targetColumn)
  have product : FamilyCoherent (composeFamily admissible family
      (constantFamily 1 sigma gamma 1 (matrixUnit term.sourceColumn term.targetColumn))) := coherent.comp admissible right
  rw [cubicEntryTermFamily,familyMatrix_comp admissible _ _ left product,
    familyMatrix_comp admissible _ _ coherent right]
  unfold familyMatrix
  rw [constantFamily_physicalValue admissible,constantFamily_physicalValue admissible,
    operatorMatrix_matrixUnit,operatorMatrix_matrixUnit]

theorem cubicMatrixFamily_matrix {sigma gamma : ℝ} (admissible : Admissible 1 sigma gamma 1)
    (family : CoefficientFamily 1 sigma gamma 1 2 2) (coherent : FamilyCoherent family)
    (grade : ℕ) (angle : ℝ) (point : ClosedDisk) :
    familyMatrix (cubicMatrixFamily admissible family) grade angle point =
      cubicMatrixEntryRecipe (familyMatrix family grade angle point) := by
  unfold familyMatrix cubicMatrixFamily
  rw [family_physicalValue_sum admissible _ (fun index =>
    (cubicEntryTermFamily_coherent admissible family coherent (cubicEntryTerms index)).smul (cubicEntryTerms index).scalar),operatorMatrix_sum]
  have each (index : Fin 8) :
      operatorMatrix (coefficientPhysicalValue ((cubicEntryTerms index).scalar • cubicEntryTermFamily admissible family (cubicEntryTerms index) grade) angle point) =
        (cubicEntryTerms index).scalar • (Matrix.single (cubicEntryTerms index).targetRow (cubicEntryTerms index).sourceRow 1 *
          (familyMatrix family grade angle point * Matrix.single (cubicEntryTerms index).sourceColumn (cubicEntryTerms index).targetColumn 1)) := by
    rw [family_physicalValue_smul admissible _ (cubicEntryTermFamily_coherent admissible family coherent (cubicEntryTerms index)),operatorMatrix_smul]
    exact congrArg (fun matrix : Matrix (Fin 2) (Fin 2) ℂ => (cubicEntryTerms index).scalar • matrix)
      (cubicEntryTermFamily_matrix admissible family coherent (cubicEntryTerms index) grade angle point)
  simp_rw [each]
  exact cubicMatrixEntryRecipe_finite _

end Grad.FinitePhysicalJetLift
