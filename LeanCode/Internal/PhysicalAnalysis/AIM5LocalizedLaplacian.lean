import AIM4ActualWeakDerivatives

noncomputable section
open scoped ContDiff
namespace Grad.OrdinaryDiskCalculus
open Grad.ClosedJets Grad.CartesianState Grad.CircularHighWeak Grad.CircularHighRegularity
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Physical.RadialLedger
open Grad.InteriorLocalization Grad.PDEBootstrap
attribute [local instance] unitNormedSpace

def unitCutoffState (grade : ℕ) : unitDiskSobolev (grade + 1) →L[ℂ] unitDiskSobolev grade :=
  (2 : ℂ) • (unitScalar grade (firstTestDerivative 0 interiorCutoff.toFun)
    (firstTestDerivative_smooth 0 _ interiorCutoff.smooth)).comp (unitPartial grade 0) +
  (2 : ℂ) • (unitScalar grade (firstTestDerivative 1 interiorCutoff.toFun)
    (firstTestDerivative_smooth 1 _ interiorCutoff.smooth)).comp (unitPartial grade 1) +
  (unitScalar grade (secondTestDerivative 0 interiorCutoff.toFun)
    (secondTestDerivative_smooth 0 _ interiorCutoff.smooth)).comp (unitLower (Nat.le_succ grade)) +
  (unitScalar grade (secondTestDerivative 1 interiorCutoff.toFun)
    (secondTestDerivative_smooth 1 _ interiorCutoff.smooth)).comp (unitLower (Nat.le_succ grade))

def unitLocalizedLaplacian (grade : ℕ) (state : unitDiskSobolev (grade + 1))
    (laplacian : unitDiskSobolev grade) : unitDiskSobolev grade :=
  unitScalar grade interiorCutoff.toFun interiorCutoff.smooth laplacian + unitCutoffState grade state

private theorem scalarPartial_bulk (grade : ℕ) (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (direction : Fin 2) (field : unitDiskSobolev (grade + 1)) :
    unitDiskBulk grade (unitScalar grade scalar smooth (unitPartial grade direction field)) =
      diskScalar scalar smooth (diskPartial direction (unitToH1 grade field)) :=
  (unitScalar_bulk grade scalar smooth _).trans
    (congrArg (diskScalar scalar smooth) (unitPartial_bulk grade direction field))

private theorem scalarLower_bulk (grade : ℕ) (scalar : Spatial → ℝ) (smooth : ContDiff ℝ ∞ scalar)
    (field : unitDiskSobolev (grade + 1)) :
    unitDiskBulk grade (unitScalar grade scalar smooth (unitLower (Nat.le_succ grade) field)) =
      diskScalar scalar smooth (diskBulk (unitToH1 grade field)) :=
  (unitScalar_bulk grade scalar smooth _).trans
    (congrArg (diskScalar scalar smooth) ((unitLower_bulk (Nat.le_succ grade) field).trans (unitToH1_bulk grade field).symm))

private theorem linearFive {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] (mapping : E →L[ℂ] F)
    (a b c d e : E) (A B C D E' : F)
    (ha : mapping a = A) (hb : mapping b = B) (hc : mapping c = C)
    (hd : mapping d = D) (he : mapping e = E') :
    mapping (a + ((2 : ℂ) • b + (2 : ℂ) • c + d + e)) =
      A + (2 : ℂ) • B + (2 : ℂ) • C + D + E' := by
  simp only [map_add, map_smul, ha, hb, hc, hd, he]
  abel

/-- Every product-rule term is an actual ordinary H^q element. Its bulk is
exactly the earlier weak-solution localization formula, with the same H1
field and no assumed second derivative. -/
theorem unitLocalizedLaplacian_bulk (grade : ℕ) (state : unitDiskSobolev (grade + 1))
    (laplacian : unitDiskSobolev grade) :
    unitDiskBulk grade (unitLocalizedLaplacian grade state laplacian) =
      localizedDiskLaplacian (unitToH1 grade state) (unitDiskBulk grade laplacian) := by
  exact @linearFive (unitDiskSobolev grade) (DiskL2 1)
    (inferInstance : NormedAddCommGroup (unitDiskSobolev grade)) (unitNormedSpace grade)
    inferInstance inferInstance (unitDiskBulk grade) _ _ _ _ _ _ _ _ _ _
    (unitScalar_bulk grade interiorCutoff.toFun interiorCutoff.smooth laplacian)
    (scalarPartial_bulk grade _ _ 0 state) (scalarPartial_bulk grade _ _ 1 state)
    (scalarLower_bulk grade _ _ state) (scalarLower_bulk grade _ _ state)

def unitCutoffSourceConstant (grade : ℕ) : ℝ :=
  unitProductConstant grade (apScalarOperatorJet 1 interiorCutoff.toFun interiorCutoff.smooth)

def unitCutoffStateConstant (grade : ℕ) : ℝ := ‖unitCutoffState grade‖

theorem unitLocalizedLaplacian_bound (grade : ℕ) (state : unitDiskSobolev (grade + 1))
    (laplacian : unitDiskSobolev grade) :
    ‖unitLocalizedLaplacian grade state laplacian‖ ≤
      unitCutoffSourceConstant grade * ‖laplacian‖ + unitCutoffStateConstant grade * ‖state‖ :=
  (norm_add_le _ _).trans (add_le_add
    (unitScalar_bound grade interiorCutoff.toFun interiorCutoff.smooth laplacian)
    (@ContinuousLinearMap.le_opNorm ℂ ℂ (unitDiskSobolev (grade + 1)) (unitDiskSobolev grade)
      (inferInstance : NormedAddCommGroup (unitDiskSobolev (grade + 1))).toSeminormedAddCommGroup
      (inferInstance : NormedAddCommGroup (unitDiskSobolev grade)).toSeminormedAddCommGroup
      _ _ (unitNormedSpace (grade + 1)) (unitNormedSpace grade) (RingHom.id ℂ) _
      (unitCutoffState grade) state))

end Grad.OrdinaryDiskCalculus
