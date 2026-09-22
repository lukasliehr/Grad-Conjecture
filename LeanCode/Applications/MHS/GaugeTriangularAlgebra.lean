import GaugeSeedPhysical

noncomputable section

namespace Grad.Constraints.Gauges

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- The written order is essential: the reverse cross-composition need not vanish. -/
def triangularProjection (poloidal toroidal : E →ₗ[ℂ] E) : E →ₗ[ℂ] E :=
  (LinearMap.id - toroidal).comp (LinearMap.id - poloidal)

theorem triangularProjection_kills_poloidal (poloidal toroidal : E →ₗ[ℂ] E)
    (poloidalSquare : ∀ value, poloidal (poloidal value) = poloidal value)
    (crossZero : ∀ value, poloidal (toroidal value) = 0) (value : E) :
    poloidal (triangularProjection poloidal toroidal value) = 0 := by
  change poloidal ((value - poloidal value) - toroidal (value - poloidal value)) = 0
  rw [map_sub, crossZero, sub_zero, map_sub, poloidalSquare, sub_self]

theorem triangularProjection_kills_toroidal (poloidal toroidal : E →ₗ[ℂ] E)
    (toroidalSquare : ∀ value, toroidal (toroidal value) = toroidal value) (value : E) :
    toroidal (triangularProjection poloidal toroidal value) = 0 := by
  change toroidal ((value - poloidal value) - toroidal (value - poloidal value)) = 0
  rw [map_sub, toroidalSquare, sub_self]

theorem triangularProjection_fixes_kernel (poloidal toroidal : E →ₗ[ℂ] E)
    (value : E) (poloidalZero : poloidal value = 0) (toroidalZero : toroidal value = 0) :
    triangularProjection poloidal toroidal value = value := by
  change (value - poloidal value) - toroidal (value - poloidal value) = value
  rw [poloidalZero, sub_zero, toroidalZero, sub_zero]

theorem triangularProjection_idempotent (poloidal toroidal : E →ₗ[ℂ] E)
    (poloidalSquare : ∀ value, poloidal (poloidal value) = poloidal value)
    (toroidalSquare : ∀ value, toroidal (toroidal value) = toroidal value)
    (crossZero : ∀ value, poloidal (toroidal value) = 0) (value : E) :
    triangularProjection poloidal toroidal (triangularProjection poloidal toroidal value) =
      triangularProjection poloidal toroidal value :=
  triangularProjection_fixes_kernel poloidal toroidal _
    (triangularProjection_kills_poloidal poloidal toroidal poloidalSquare crossZero value)
    (triangularProjection_kills_toroidal poloidal toroidal toroidalSquare value)

theorem triangularProjection_range (poloidal toroidal : E →ₗ[ℂ] E)
    (poloidalSquare : ∀ value, poloidal (poloidal value) = poloidal value)
    (toroidalSquare : ∀ value, toroidal (toroidal value) = toroidal value)
    (crossZero : ∀ value, poloidal (toroidal value) = 0) :
    LinearMap.range (triangularProjection poloidal toroidal) = poloidal.ker ⊓ toroidal.ker := by
  ext value
  constructor
  · rintro ⟨source, rfl⟩
    exact ⟨triangularProjection_kills_poloidal poloidal toroidal poloidalSquare crossZero source,
      triangularProjection_kills_toroidal poloidal toroidal toroidalSquare source⟩
  · intro inside
    exact ⟨value, triangularProjection_fixes_kernel poloidal toroidal value inside.1 inside.2⟩

end Grad.Constraints.Gauges
