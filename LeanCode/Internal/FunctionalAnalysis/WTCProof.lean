import WTCSmooth

noncomputable section

open MeasureTheory Grad.PDEBootstrap
open scoped ContDiff

namespace Grad.WeakTesting.Commutation

theorem signedDerivativePairing_apply (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Grad.GenericCarriers.PhysicalValue dimension) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test)
    (rank : ℕ) (word : Fin rank → Fin 2) (field : Grad.GenericCarriers.FieldL2 dimension domain) :
    signedDerivativePairing dimension domain cell vector test smoothness compactSupport rank word
        field = ((-1 : ℂ) ^ rank) *
      ∫ point in domain, orderedTestDerivative rank word test point •
        inner ℂ vector (field point cell) := by
  change ((-1 : ℂ) ^ rank) *
    orderedDerivativePairing dimension domain cell vector test smoothness compactSupport rank word
      field = _
  rw [orderedDerivativePairing_apply]

theorem hasWeakOrderedDerivative_iff_integral (dimension : ℕ) (domain : Set Spatial) (rank : ℕ)
    (word : Fin rank → Fin 2) (field derivative : Grad.GenericCarriers.FieldL2 dimension domain) :
    HasWeakOrderedDerivative dimension domain rank word field derivative ↔
      ∀ (cell : ℤ) (vector : Grad.GenericCarriers.PhysicalValue dimension) (test : Spatial → ℝ),
        ContDiff ℝ ∞ test → HasCompactSupport test → tsupport test ⊆ domain →
          (∫ point in domain, test point • inner ℂ vector (derivative point cell)) =
            ((-1 : ℂ) ^ rank) * ∫ point in domain,
              orderedTestDerivative rank word test point • inner ℂ vector (field point cell) := by
  simp only [HasWeakOrderedDerivative, compactPairing_apply, signedDerivativePairing_apply]

theorem pairing : PairingGoal := by
  intro dimension domain cell vector test smoothness compactSupport rank first second same
  apply ContinuousLinearMap.ext
  intro field
  rw [signedDerivativePairing_apply, signedDerivativePairing_apply,
    orderedTestDerivative_sameCounts rank first second same test smoothness]

theorem signedDerivativePairing_permutation (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Grad.GenericCarriers.PhysicalValue dimension) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test)
    (rank : ℕ) (word : Fin rank → Fin 2) (permutation : Equiv.Perm (Fin rank)) :
    signedDerivativePairing dimension domain cell vector test smoothness compactSupport rank
        (word ∘ permutation) =
      signedDerivativePairing dimension domain cell vector test smoothness compactSupport rank word :=
  pairing dimension domain cell vector test smoothness compactSupport rank _ _
    (sameCounts_permutation word permutation)

theorem transport : TransportGoal := by
  intro dimension domain rank first second same field derivative
  constructor
  · intro weak cell vector test smoothness compactSupport supported
    rw [← pairing dimension domain cell vector test smoothness compactSupport rank first second same]
    exact weak cell vector test smoothness compactSupport supported
  · intro weak cell vector test smoothness compactSupport supported
    rw [pairing dimension domain cell vector test smoothness compactSupport rank first second same]
    exact weak cell vector test smoothness compactSupport supported

theorem weakDerivative_permutation (dimension : ℕ) (domain : Set Spatial) (rank : ℕ)
    (word : Fin rank → Fin 2) (permutation : Equiv.Perm (Fin rank))
    (field derivative : Grad.GenericCarriers.FieldL2 dimension domain) :
    HasWeakOrderedDerivative dimension domain rank (word ∘ permutation) field derivative ↔
      HasWeakOrderedDerivative dimension domain rank word field derivative :=
  transport dimension domain rank _ _ (sameCounts_permutation word permutation) field derivative

theorem weakEquality : WeakEqualityGoal := by
  intro dimension domain openDomain rank first second same field firstDerivative secondDerivative
    firstWeak secondWeak
  apply Separation.equality dimension domain openDomain firstDerivative secondDerivative
  intro cell vector test smoothness compactSupport supported
  rw [firstWeak cell vector test smoothness compactSupport supported,
    secondWeak cell vector test smoothness compactSupport supported,
    pairing dimension domain cell vector test smoothness compactSupport rank first second same]

theorem weakDerivative_eq_of_permutation (dimension : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (rank : ℕ) (word : Fin rank → Fin 2)
    (permutation : Equiv.Perm (Fin rank))
    (field firstDerivative secondDerivative : Grad.GenericCarriers.FieldL2 dimension domain)
    (firstWeak : HasWeakOrderedDerivative dimension domain rank word field firstDerivative)
    (secondWeak : HasWeakOrderedDerivative dimension domain rank (word ∘ permutation)
      field secondDerivative) : firstDerivative = secondDerivative :=
  weakEquality dimension domain openDomain rank _ _
    (sameCounts_symm (sameCounts_permutation word permutation)) field firstDerivative secondDerivative
      firstWeak secondWeak

theorem representatives : RepresentativeGoal := by
  intro dimension domain openDomain rank firstWord secondWord same field first second
    firstMembership secondMembership firstWeak secondWeak
  have fieldsEqual := weakEquality dimension domain openDomain rank firstWord secondWord same field
    (firstMembership.toLp first) (secondMembership.toLp second) firstWeak secondWeak
  filter_upwards [firstMembership.coeFn_toLp, secondMembership.coeFn_toLp]
    with point firstRepresentative secondRepresentative
  exact firstRepresentative.symm.trans
    ((congrArg (fun derivative : Grad.GenericCarriers.FieldL2 dimension domain => derivative point)
      fieldsEqual).trans secondRepresentative)

theorem weakDerivative_canonical (dimension : ℕ) (domain : Set Spatial) (zeros ones : ℕ)
    (word : Fin (zeros + ones) → Fin 2) (zeroCount : directionCount word 0 = zeros)
    (oneCount : directionCount word 1 = ones)
    (field derivative : Grad.GenericCarriers.FieldL2 dimension domain) :
    HasWeakOrderedDerivative dimension domain (zeros + ones) word field derivative ↔
      HasWeakOrderedDerivative dimension domain (zeros + ones) (canonicalWord zeros ones)
        field derivative :=
  transport dimension domain _ _ _ (sameCounts_canonical zeros ones word zeroCount oneCount)
    field derivative

theorem weakDerivative_eq_canonical (dimension : ℕ) (domain : Set Spatial)
    (openDomain : IsOpen domain) (zeros ones : ℕ) (word : Fin (zeros + ones) → Fin 2)
    (zeroCount : directionCount word 0 = zeros) (oneCount : directionCount word 1 = ones)
    (field derivative canonicalDerivative : Grad.GenericCarriers.FieldL2 dimension domain)
    (weak : HasWeakOrderedDerivative dimension domain (zeros + ones) word field derivative)
    (canonicalWeak : HasWeakOrderedDerivative dimension domain (zeros + ones)
      (canonicalWord zeros ones) field canonicalDerivative) : derivative = canonicalDerivative :=
  weakEquality dimension domain openDomain _ _ _
    (sameCounts_canonical zeros ones word zeroCount oneCount) field derivative canonicalDerivative
      weak canonicalWeak

theorem signedDerivativePairing_zero (dimension : ℕ) (domain : Set Spatial) (cell : ℤ)
    (vector : Grad.GenericCarriers.PhysicalValue dimension) (test : Spatial → ℝ)
    (smoothness : ContDiff ℝ ∞ test) (compactSupport : HasCompactSupport test)
    (word : Fin 0 → Fin 2) :
    signedDerivativePairing dimension domain cell vector test smoothness compactSupport 0 word =
      compactPairing dimension domain cell vector test smoothness compactSupport := by
  rw [signedDerivativePairing, pow_zero, one_smul, orderedDerivativePairing_zero]

theorem zero : ZeroGoal := by
  intro dimension domain openDomain word field derivative
  constructor
  · intro weak
    apply Separation.equality dimension domain openDomain derivative field
    intro cell vector test smoothness compactSupport supported
    simpa only [signedDerivativePairing_zero] using
      weak cell vector test smoothness compactSupport supported
  · rintro rfl cell vector test smoothness compactSupport _supported
    rw [signedDerivativePairing_zero]

theorem block : BlockGoal :=
  ⟨wordPermutation, smooth, pairing, transport, weakEquality, representatives, canonical, zero⟩

end Grad.WeakTesting.Commutation
