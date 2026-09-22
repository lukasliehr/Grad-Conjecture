import AKI10GenuineOriginalScalarDerivatives

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularSmoothCore
open Grad.AnnularStrongOrbit Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse
open Grad.AnnularCurrentLow Grad.AnnularKnownLow Grad.AnnularSourceGraph

theorem rawFullRHS_add (length radius : ℝ) (mode : ℤ × ℤ)
    (x j0 c0 v0 j1 c1 v1 f g : ComplexEuclidean 1) :
    rawOriginalUnknownRHS length radius mode x j0 c0 v0 + rawOriginalSourceRHS length radius mode j1 c1 v1 f g =
      ((-((radius : ℂ)⁻¹)) • x - (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • (c0+c1)) -
        (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode • (v0+v1)) +
        frequencyNumerator (some false) mode • g,
        (if mode.1 = 0 then (0 : ℂ) else 1) • (j0+j1+f)) := by
  simp only [rawOriginalUnknownRHS, rawOriginalSourceRHS, Prod.mk_add_mk, smul_add, neg_smul]
  congr 1 <;> abel

variable (parameters : PhaseParameters) (length compact lower : ℝ) (positive : 0 < lower)
    (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (field : CoupledSpace lower length positive lengthPositive) (core : OriginalSmoothSourceCore parameters)

def actualOriginalFullRow (row : Fin 3) (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  lowRhoPhysicalCoefficient parameters lower positive
    (lowPhysicalRowAction parameters length compact lower positive bounded.le state row
      (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le
        ((strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core) field)) radius mode

def actualOriginalIndependentF (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  lowRhoPhysicalCoefficient parameters lower positive
    (strongKnownBulk parameters lower positive bounded.le
      ((strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core) 3) radius mode

def actualOriginalIndependentG (radius : ℝ) (mode : ℤ × ℤ) : ComplexEuclidean 1 :=
  lowRhoPhysicalCoefficient parameters lower positive
    ((strongToLow parameters lower positive bounded.le 0 0
      ((strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core)).ofLp.1.ofLp.2) radius mode

/-- The actual full PDE has the SAME three full original rows and the two
independent original source terms. In particular, Rg has its positive sign. -/
theorem actualOriginalFullRHS_fullRows :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ mode,
      actualOriginalFullRHS parameters length compact lower positive bounded lengthPositive state field core radius mode =
      ((-((radius : ℂ)⁻¹)) •
        sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0 (radialClamp lower bounded.le radius) mode -
        (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode •
          actualOriginalFullRow parameters length compact lower positive bounded lengthPositive state field core 1 radius mode) -
        (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode •
          actualOriginalFullRow parameters length compact lower positive bounded lengthPositive state field core 2 radius mode) +
        frequencyNumerator (some false) mode • actualOriginalIndependentG parameters length lower positive bounded lengthPositive core radius mode,
        (if mode.1 = 0 then (0 : ℂ) else 1) •
          (actualOriginalFullRow parameters length compact lower positive bounded lengthPositive state field core 0 radius mode +
            actualOriginalIndependentF parameters length lower positive bounded lengthPositive core radius mode)) := by
  filter_upwards [fullStrongPhysicalCoefficient_split parameters length compact lower lengthPositive positive bounded.le state
      ((strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core) field 0,
    fullStrongPhysicalCoefficient_split parameters length compact lower lengthPositive positive bounded.le state
      ((strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core) field 1,
    fullStrongPhysicalCoefficient_split parameters length compact lower lengthPositive positive bounded.le state
      ((strongSmoothDenseMap parameters lower length positive bounded.le lengthPositive).mapping core) field 2] with radius row0 row1 row2
  intro mode
  have first := row0 mode
  have second := row1 mode
  have third := row2 mode
  change actualOriginalFullRow parameters length compact lower positive bounded lengthPositive state field core 0 radius mode = _ at first
  change actualOriginalFullRow parameters length compact lower positive bounded lengthPositive state field core 1 radius mode = _ at second
  change actualOriginalFullRow parameters length compact lower positive bounded lengthPositive state field core 2 radius mode = _ at third
  let x := sameCoupledXCoefficient parameters lower length positive bounded lengthPositive field 0 (radialClamp lower bounded.le radius) mode
  let f := actualOriginalIndependentF parameters length lower positive bounded lengthPositive core radius mode
  let g := actualOriginalIndependentG parameters length lower positive bounded lengthPositive core radius mode
  let assemble : (ComplexEuclidean 1 × (ComplexEuclidean 1 × ComplexEuclidean 1)) → ComplexEuclidean 1 × ComplexEuclidean 1 :=
    fun rows => ((-((radius : ℂ)⁻¹)) • x - (length : ℂ)⁻¹ • (frequencyNumerator (some true) mode • rows.2.1) -
      (radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode • rows.2.2) + frequencyNumerator (some false) mode • g,
      (if mode.1 = 0 then (0 : ℂ) else 1) • (rows.1 + f))
  have pairSame := congrArg₂ (fun (a b : ComplexEuclidean 1) => (a, b)) second.symm third.symm
  have tripleSame := congrArg₂ (fun (a : ComplexEuclidean 1) (b : ComplexEuclidean 1 × ComplexEuclidean 1) => (a, b)) first.symm pairSame
  have same := congrArg assemble tripleSame
  exact (rawFullRHS_add length radius mode x _ _ _ _ _ _ f g).trans same

end Grad.AnnularOriginalSmoothCore
