import AKI21ClosedClassicalWeakDerivative

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
open Set Filter MeasureTheory
namespace Grad.AnnularOriginalSmoothCore
open Grad.ClosedJets Grad.CartesianState Grad.SourceCollarDivision Grad.SourceCollarCoefficients
open Grad.AnnularReconstruction Grad.BoundaryKernelAction Grad.AnnularSmoothCore
open Grad.AnnularStrongData Grad.AnnularStrongSolution Grad.AnnularCoupledInverse Grad.AnnularFullGraph
open Grad.AnnularCurrentLow Grad.AnnularCurrentSource Grad.AnnularSourceGraph Grad.AnnularPhysicalReconstruction
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Physical.Ledger

variable (parameters : PhaseParameters) (length compact lower : ℝ)
    (positive : 0 < lower) (bounded : lower < 1) (lengthPositive : 0 < length)
    (state : RetainedInverseState parameters length compact)
    (data : OriginalStrongCarrier parameters lower 0 0) (candidate : OriginalCoupledSpace lower length positive)
    (tuple : OriginalSmoothTuple parameters lower)
    (represented : OriginalTupleObservation parameters length compact lower positive bounded lengthPositive state tuple
      (originalFiveBlockObservation parameters lower length positive (data,candidate)))

private abbrev field := originalCoupledEquivalence parameters lower length positive bounded.le lengthPositive candidate
private abbrev weighted := originalToStrong parameters lower length positive bounded.le lengthPositive 0 0 data

include represented

/-- The literal pressure reconstructs the retained X, including its excluded
angular zero mode. This holds for arbitrary represented candidates. -/
theorem OriginalTupleObservation.pressure_R (radius : Icc lower (1 : ℝ)) (mode : ℤ × ℤ) :
    frequencyNumerator (some false) mode • originalPhysicalCoefficient (tuple.val 0) radius.val mode =
      sameCoupledXCoefficient parameters lower length positive bounded lengthPositive
        (field parameters length lower positive bounded lengthPositive candidate) 0 radius mode := by
  have algebra (index : ℤ × ℤ) (value : ComplexEuclidean 1)
      (mean : index.1 = 0 → value = 0) :
      frequencyNumerator (some false) index • (angularInverseMultiplier index • value) = value := by
    by_cases zero : index.1 = 0
    · rw [mean zero]
      simp
    · rw [angularInverseMultiplier,if_neg zero,smul_smul]
      change (Complex.I * (index.1 : ℂ) * (Complex.I * (index.1 : ℂ))⁻¹) • _ = _
      rw [mul_inv_cancel₀ (mul_ne_zero Complex.I_ne_zero (Int.cast_ne_zero.mpr zero)),one_smul]
  apply (congrArg (fun value : ComplexEuclidean 1 => frequencyNumerator (some false) mode • value)
    (represented.pressure radius mode)).trans
  apply algebra
  intro zero
  rcases mode with ⟨angular,cell⟩
  change angular = 0 at zero
  subst angular
  exact sameCoupledXCoefficient_meanZero parameters lower length positive bounded lengthPositive
    (field parameters length lower positive bounded lengthPositive candidate) 0 radius cell

/-- Arbitrary literal tuple input equals the actual seven-slot packet in
original storage. F0 appears once, with its genuine R derivative. -/
theorem OriginalTupleObservation.fullPacket :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ mode,
      originalTupleNormalizedCoefficient parameters lower tuple ⟨radius,inside⟩ mode =
        lowRhoPhysicalCoefficient parameters lower positive
          (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le
            (weighted parameters length lower positive bounded lengthPositive data)
            (field parameters length lower positive bounded lengthPositive candidate)) radius mode := by
  filter_upwards [fullPacket_physical_ae parameters length lower lengthPositive positive bounded
      (weighted parameters length lower positive bounded lengthPositive data)
      (field parameters length lower positive bounded lengthPositive candidate),
    represented.sourceZero, represented.sourceTwo,
    strongKnownBulk_genuineAngular parameters lower positive bounded.le
      (weighted parameters length lower positive bounded lengthPositive data)] with radius packet f0 f2 rf0
  intro inside mode
  rw [packet mode,radialClamp_eq lower bounded.le radius inside]
  have f0Same : originalPhysicalCoefficient (tuple.val 2) radius mode =
      lowRhoPhysicalCoefficient parameters lower positive
        (strongKnownBulk parameters lower positive bounded.le
          (weighted parameters length lower positive bounded lengthPositive data) 0) radius mode := f0 mode
  have f2Same : originalPhysicalCoefficient (tuple.val 3) radius mode =
      lowRhoPhysicalCoefficient parameters lower positive
        (strongKnownBulk parameters lower positive bounded.le
          (weighted parameters length lower positive bounded lengthPositive data) 2) radius mode := f2 mode
  have rf0Same : lowRhoPhysicalCoefficient parameters lower positive
      (strongKnownBulk parameters lower positive bounded.le
        (weighted parameters length lower positive bounded lengthPositive data) 1) radius mode =
      frequencyNumerator (some false) mode • lowRhoPhysicalCoefficient parameters lower positive
        (strongKnownBulk parameters lower positive bounded.le
          (weighted parameters length lower positive bounded lengthPositive data) 0) radius mode := by
    unfold lowRhoPhysicalCoefficient
    rw [rf0 mode]
    exact smul_comm _ _ _
  have pSame := represented.pressure_R parameters length compact lower positive bounded lengthPositive state data candidate tuple ⟨radius,inside⟩ mode
  have xiSame := represented.scalar ⟨radius,inside⟩ mode
  let assemble : (ComplexEuclidean 1 × ComplexEuclidean 1 × ComplexEuclidean 1 × ComplexEuclidean 1 × ComplexEuclidean 1) → ComplexEuclidean 7 :=
    fun values => WithLp.toLp 2 ![values.1 0,
      ((radius : ℂ)⁻¹ • (frequencyNumerator (some false) mode • values.2.1)) 0,
      (frequencyNumerator (some true) mode • values.2.1) 0,
      ((radius : ℂ)⁻¹ • values.2.1) 0, values.2.2.1 0, values.2.2.2.1 0, values.2.2.2.2 0]
  have angularSame := (congrArg (fun value : ComplexEuclidean 1 => frequencyNumerator (some false) mode • value) f0Same).trans rf0Same.symm
  have valuesSame :
      (frequencyNumerator (some false) mode • originalPhysicalCoefficient (tuple.val 0) radius mode,
        originalPhysicalCoefficient (tuple.val 1) radius mode, originalPhysicalCoefficient (tuple.val 2) radius mode,
        frequencyNumerator (some false) mode • originalPhysicalCoefficient (tuple.val 2) radius mode,
        originalPhysicalCoefficient (tuple.val 3) radius mode) =
      (sameCoupledXCoefficient parameters lower length positive bounded lengthPositive
        (field parameters length lower positive bounded lengthPositive candidate) 0 ⟨radius,inside⟩ mode,
       sameCoupledXiCoefficient parameters lower length positive bounded lengthPositive
        (field parameters length lower positive bounded lengthPositive candidate) 0 ⟨radius,inside⟩ mode,
       lowRhoPhysicalCoefficient parameters lower positive (strongKnownBulk parameters lower positive bounded.le
        (weighted parameters length lower positive bounded lengthPositive data) 0) radius mode,
       lowRhoPhysicalCoefficient parameters lower positive (strongKnownBulk parameters lower positive bounded.le
        (weighted parameters length lower positive bounded lengthPositive data) 1) radius mode,
       lowRhoPhysicalCoefficient parameters lower positive (strongKnownBulk parameters lower positive bounded.le
        (weighted parameters length lower positive bounded lengthPositive data) 2) radius mode) :=
      Prod.ext pSame (Prod.ext xiSame (Prod.ext f0Same (Prod.ext angularSame f2Same)))
  have vectorSame := congrArg assemble valuesSame
  have algebra (x xi first derivative second : ComplexEuclidean 1) :
      assemble (x,xi,first,derivative,second) =
        rawPhysicalSevenVector radius mode x xi + rawOriginalKnownSevenVector first derivative second := by
    ext slot
    fin_cases slot <;> simp [assemble,rawPhysicalSevenVector,rawOriginalKnownSevenVector,matrixUnit_apply,operatorBasis]
  exact vectorSame.trans (algebra _ _ _ _ _)

/-- The SAME arbitrary candidate's completed j/c/rV kernels agree with the
literal AH20/AH23 tuple reconstruction. -/
theorem OriginalTupleObservation.physicalRows :
    ∀ᵐ radius ∂volume.restrict (Icc lower 1), ∀ inside : radius ∈ Icc lower 1, ∀ row : Fin 3, ∀ mode,
      negativeTraceCoefficient (radialKernelParameters parameters (tupleRadius lower positive ⟨radius,inside⟩)) 0 0
        (tuplePhysicalRowTrace parameters length compact lower positive state tuple ⟨radius,inside⟩ row) mode =
        lowRhoPhysicalCoefficient parameters lower positive
          (lowPhysicalRowAction parameters length compact lower positive bounded.le state row
            (fullStrongSevenInput parameters length lower lengthPositive positive bounded.le
              (weighted parameters length lower positive bounded lengthPositive data)
              (field parameters length lower positive bounded lengthPositive candidate))) radius mode := by
  have rows (row : Fin 3) := tuplePhysicalRows_of_packet parameters length compact lower positive bounded.le state tuple _
    (represented.fullPacket parameters length compact lower positive bounded lengthPositive state data candidate tuple) row
  have allRows := (ae_all_iff).mpr rows
  filter_upwards [allRows] with radius same
  exact fun inside row mode => same row inside mode

end Grad.AnnularOriginalSmoothCore
