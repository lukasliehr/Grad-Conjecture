import AIB1GeneralPhysicalSpectral
import AIM6ExactLocalizationConsumer
import APF3ActualFourierForward
import APR5ActualInteriorH2

noncomputable section
namespace Grad.OrdinaryInteriorBootstrap
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.Constraints
open Grad.InteriorPeriodization Grad.InteriorLocalization Grad.CircularHighRegularity
open Grad.PDEBootstrap Grad.InteriorFourier Grad.FourierGrade Grad.COR12Extension
open Grad.OrdinaryDiskCalculus Grad.OrdinaryDiskForward Grad.OrdinaryDiskReconstruction

theorem ordinaryFourier_coefficient (parameters : PhaseParameters) (grade : ℕ)
    (field : unitDiskSobolev grade) (mode : FourierMode) :
    coefficient grade (ordinaryFourier parameters grade field) mode =
      coefficient 0 (diskFourier parameters (unitDiskBulk grade field)) mode := by
  have identity := congrArg (fun values : JGrade (ComplexEuclidean 1) 0 => coefficient 0 values mode)
    (ordinaryFourier_zero_coherent parameters grade field)
  exact (inclusion_coefficient grade 0 (Nat.zero_le grade) (ordinaryFourier parameters grade field) mode).symm.trans identity

private theorem localizedMass_coefficient (parameters : PhaseParameters) (grade : ℕ)
    (state : unitDiskSobolev (grade + 1)) (mode : FourierMode) :
    coefficient grade (ordinaryFourier parameters grade (unitLocalizedField grade state)) mode =
      coefficient 0 (diskFourier parameters
        (diskScalar interiorCutoff.toFun interiorCutoff.smooth (diskBulk (unitToH1 grade state)))) mode :=
  (ordinaryFourier_coefficient parameters grade _ mode).trans
    (congrArg (fun field : DiskL2 1 => coefficient 0 (diskFourier parameters field) mode)
      (unitLocalizedField_bulk grade state))

private theorem localizedLaplacian_coefficient (parameters : PhaseParameters) (grade : ℕ)
    (state : unitDiskSobolev (grade + 1)) (laplacian : unitDiskSobolev grade) (mode : FourierMode) :
    coefficient grade (ordinaryFourier parameters grade (unitLocalizedLaplacian grade state laplacian)) mode =
      coefficient 0 (diskFourier parameters
        (localizedDiskLaplacian (unitToH1 grade state) (unitDiskBulk grade laplacian))) mode :=
  (ordinaryFourier_coefficient parameters grade _ mode).trans
    (congrArg (fun field : DiskL2 1 => coefficient 0 (diskFourier parameters field) mode)
      (unitLocalizedLaplacian_bulk grade state laplacian))

theorem ordinaryGain_from_spectral (parameters : PhaseParameters) (grade : ℕ)
    (value : DiskL2 1) (forcing mass : unitDiskSobolev grade)
    (spectral : ∀ mode : FourierMode, (frequencyWeight mode : ℂ) ^ 2 •
      coefficient 0 (diskFourier parameters value) mode =
      coefficient grade (ordinaryFourier parameters grade mass) mode -
        coefficient grade (ordinaryFourier parameters grade forcing) mode) :
    ∃ regular : unitDiskSobolev (grade + 2),
      unitDiskBulk (grade + 2) regular = value ∧
      ‖regular‖ ≤ (sameGradeConstant (grade + 2) * sameGradeConstant grade) * (‖forcing‖ + ‖mass‖) := by
  have existence : ∃ higher : JGrade (ComplexEuclidean 1) (grade + 2),
      inclusion (grade + 2) 0 (by omega) higher = diskFourier parameters value ∧
      ‖higher‖ ≤ ‖ordinaryFourier parameters grade forcing‖ + ‖ordinaryFourier parameters grade mass‖ :=
    gainTwo_from_spectralEquation (Value := ComplexEuclidean 1) grade (diskFourier parameters value)
      (ordinaryFourier parameters grade forcing) (ordinaryFourier parameters grade mass) spectral
  obtain ⟨higher, same, bound⟩ := existence
  refine ⟨fourierDisk parameters (grade + 2) higher,
    fourierDisk_actualL2 parameters (grade + 2) higher value same, ?_⟩
  have lowerBound := (add_le_add (ordinaryFourier_bound parameters grade forcing)
    (ordinaryFourier_bound parameters grade mass)).trans_eq (mul_add _ _ _).symm
  exact (fourierDisk_bound parameters (grade + 2) higher).trans
    ((mul_le_mul_of_nonneg_left (bound.trans lowerBound) (sameGradeConstant_nonnegative (grade + 2))).trans_eq
      (mul_assoc _ _ _).symm)

/-- Two additional derivatives are constructed for the actual localized
ordinary disk field at every q. The weak equation is unchanged, and no
higher regularity of the localized solution is assumed. -/
theorem ordinaryInterior_gainTwo (parameters : PhaseParameters) (grade : ℕ)
    (state : unitDiskSobolev (grade + 1)) (laplacian : unitDiskSobolev grade)
    (equation : HasDiskWeakLaplacian (unitDiskBulk (grade + 1) state) (unitDiskBulk grade laplacian)) :
    ∃ regular : unitDiskSobolev (grade + 2),
      unitDiskBulk (grade + 2) regular =
        diskScalar interiorCutoff.toFun interiorCutoff.smooth (unitDiskBulk (grade + 1) state) ∧
      ‖regular‖ ≤ (sameGradeConstant (grade + 2) * sameGradeConstant grade) *
        (‖unitLocalizedLaplacian grade state laplacian‖ + ‖unitLocalizedField grade state‖) := by
  have h1Equation : HasDiskWeakLaplacian (diskBulk (unitToH1 grade state)) (unitDiskBulk grade laplacian) :=
    (congrArg (fun field => HasDiskWeakLaplacian field (unitDiskBulk grade laplacian))
      (unitToH1_bulk grade state)).mpr equation
  have spectral (mode : FourierMode) :
      (frequencyWeight mode : ℂ) ^ 2 • coefficient 0
        (diskFourier parameters (diskScalar interiorCutoff.toFun interiorCutoff.smooth (diskBulk (unitToH1 grade state)))) mode =
      coefficient grade (ordinaryFourier parameters grade (unitLocalizedField grade state)) mode -
        coefficient grade (ordinaryFourier parameters grade (unitLocalizedLaplacian grade state laplacian)) mode :=
    (localizedDiskFourier_spectral parameters (unitToH1 grade state) (unitDiskBulk grade laplacian) h1Equation mode).trans
      (congrArg₂ (fun first second : ComplexEuclidean 1 => first - second)
        (localizedMass_coefficient parameters grade state mode).symm
        (localizedLaplacian_coefficient parameters grade state laplacian mode).symm)
  have existence : ∃ regular : unitDiskSobolev (grade + 2),
      unitDiskBulk (grade + 2) regular = diskScalar interiorCutoff.toFun interiorCutoff.smooth (diskBulk (unitToH1 grade state)) ∧
      ‖regular‖ ≤ (sameGradeConstant (grade + 2) * sameGradeConstant grade) *
        (‖unitLocalizedLaplacian grade state laplacian‖ + ‖unitLocalizedField grade state‖) :=
    ordinaryGain_from_spectral parameters grade
      (diskScalar interiorCutoff.toFun interiorCutoff.smooth (diskBulk (unitToH1 grade state)))
      (unitLocalizedLaplacian grade state laplacian) (unitLocalizedField grade state) spectral
  obtain ⟨regular, same, bound⟩ := existence
  exact ⟨regular, same.trans
    (congrArg (diskScalar interiorCutoff.toFun interiorCutoff.smooth) (unitToH1_bulk grade state)), bound⟩

end Grad.OrdinaryInteriorBootstrap
