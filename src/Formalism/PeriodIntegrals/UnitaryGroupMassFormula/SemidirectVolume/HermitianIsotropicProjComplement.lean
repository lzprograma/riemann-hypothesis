module

public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.ProjGen

@[expose] public section

noncomputable section

namespace PI.VolSemiDirect.W.PG

open Formalism.UG

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

namespace Dat

def Uni (D : Dat A n r) (S : (n → A) →ₗ[A] (n → A)) : Prop := ∀ x y, D.h (S x) (S y) = D.h x y

variable {D : Dat A n r}

theorem pX_mem_span (u : n → A) : D.pX u ∈ Submodule.span A (Set.range D.e) := by
  simp only [Dat.pX.eq_1, LinearMap.sum_apply, LinearMap.smulRight_apply]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end Dat

end PI.VolSemiDirect.W.PG
