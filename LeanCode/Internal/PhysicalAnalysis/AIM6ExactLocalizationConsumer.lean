import AIM5LocalizedLaplacian
import AIC10DiskCutoffLaplacian

noncomputable section
namespace Grad.OrdinaryDiskCalculus
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.InteriorLocalization Grad.PDEBootstrap
attribute [local instance] unitNormedSpace

def unitLocalizedField (grade : ℕ) (state : unitDiskSobolev (grade + 1)) : unitDiskSobolev grade :=
  unitScalar grade interiorCutoff.toFun interiorCutoff.smooth (unitLower (Nat.le_succ grade) state)

theorem unitLocalizedField_bulk (grade : ℕ) (state : unitDiskSobolev (grade + 1)) :
    unitDiskBulk grade (unitLocalizedField grade state) =
      diskScalar interiorCutoff.toFun interiorCutoff.smooth (diskBulk (unitToH1 grade state)) :=
  (unitScalar_bulk grade _ _ _).trans
    (congrArg (diskScalar interiorCutoff.toFun interiorCutoff.smooth)
      ((unitLower_bulk (Nat.le_succ grade) state).trans (unitToH1_bulk grade state).symm))

theorem unitLocalizedField_bound (grade : ℕ) (state : unitDiskSobolev (grade + 1)) :
    ‖unitLocalizedField grade state‖ ≤ unitCutoffSourceConstant grade * apLoweringConstant grade * ‖state‖ :=
  (unitScalar_bound grade _ _ _).trans
    ((mul_le_mul_of_nonneg_left (unitLower_bound (Nat.le_succ grade) state)
      (unitProductConstant_nonnegative grade _)).trans_eq (mul_assoc _ _ _).symm)

/-- Actual higher-grade cutoff calculus: the constructed localized bulk
and constructed Laplacian belong to the claimed ordinary disk grade and
satisfy the same full-disk weak PDE, without assuming regularity of its solution. -/
theorem unitLocalized_weak (grade : ℕ) (state : unitDiskSobolev (grade + 1))
    (laplacian : unitDiskSobolev grade)
    (equation : HasDiskWeakLaplacian (unitDiskBulk (grade + 1) state) (unitDiskBulk grade laplacian)) :
    HasDiskWeakLaplacian (unitDiskBulk grade (unitLocalizedField grade state))
      (unitDiskBulk grade (unitLocalizedLaplacian grade state laplacian)) := by
  have h1Equation : HasDiskWeakLaplacian (diskBulk (unitToH1 grade state)) (unitDiskBulk grade laplacian) :=
    (congrArg (fun field => HasDiskWeakLaplacian field (unitDiskBulk grade laplacian))
      (unitToH1_bulk grade state)).mpr equation
  intro vector test smooth compact _supported
  exact (congrArg (fun field => diskIntegral field vector test)
    (unitLocalizedLaplacian_bulk grade state laplacian)).trans
      ((localizedDiskLaplacian_weak (unitToH1 grade state) (unitDiskBulk grade laplacian)
        h1Equation vector test smooth compact).trans
          (congrArg (fun field => diskIntegral field vector (testLaplacian test))
            (unitLocalizedField_bulk grade state).symm))

theorem ordinaryLocalization_consumer (grade : ℕ) (state : unitDiskSobolev (grade + 1))
    (laplacian : unitDiskSobolev grade)
    (equation : HasDiskWeakLaplacian (unitDiskBulk (grade + 1) state) (unitDiskBulk grade laplacian)) :
    ∃ localized forcing : unitDiskSobolev grade,
      unitDiskBulk grade localized = diskScalar interiorCutoff.toFun interiorCutoff.smooth (diskBulk (unitToH1 grade state)) ∧
      unitDiskBulk grade forcing = localizedDiskLaplacian (unitToH1 grade state) (unitDiskBulk grade laplacian) ∧
      HasDiskWeakLaplacian (unitDiskBulk grade localized) (unitDiskBulk grade forcing) ∧
      ‖localized‖ ≤ unitCutoffSourceConstant grade * apLoweringConstant grade * ‖state‖ ∧
      ‖forcing‖ ≤ unitCutoffSourceConstant grade * ‖laplacian‖ + unitCutoffStateConstant grade * ‖state‖ :=
  ⟨unitLocalizedField grade state, unitLocalizedLaplacian grade state laplacian,
    unitLocalizedField_bulk grade state, unitLocalizedLaplacian_bulk grade state laplacian,
    unitLocalized_weak grade state laplacian equation,
    unitLocalizedField_bound grade state, unitLocalizedLaplacian_bound grade state laplacian⟩

end Grad.OrdinaryDiskCalculus
