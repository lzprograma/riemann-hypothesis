module

public import GroundTheory.ArithmeticGeometry.SchemeCohomology.CechNaturality.Linear
public import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.Tactic.Lemma

@[expose] public section

set_option maxSynthPendingDepth 1

open CategoryTheory AlgebraicGeometry Order Topology

universe u

namespace GroundTheory.Arith.SchemeCoh

section Scalars

variable {k : Type u} [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]

noncomputable def scalarRingHom : k →+* Γ(X, ⊤) :=
  @algebraMap k Γ(X, ⊤) _ _ (overAlgebra (.of k))

noncomputable instance stalkAlgebra (x : X) : Algebra k (X.presheaf.stalk x) :=
  ((X.presheaf.germ ⊤ x trivial).hom.comp (scalarRingHom X)).toAlgebra

lemma algebraMap_stalk (x : X) (c : k) :
    algebraMap k (X.presheaf.stalk x) c = X.presheaf.germ ⊤ x trivial (scalarRingHom X c) := rfl

variable [IsIntegral X]

instance : Nonempty (⊤ : X.Opens) := ⟨⟨(inferInstance : Nonempty X).some, trivial⟩⟩

noncomputable instance functionFieldAlgebra : Algebra k X.functionField :=
  ((X.germToFunctionField ⊤).hom.comp (scalarRingHom X)).toAlgebra

lemma algebraMap_functionField (c : k) :
    algebraMap k X.functionField c = X.germToFunctionField ⊤ (scalarRingHom X c) := rfl

instance (x : X) : IsScalarTower k (X.presheaf.stalk x) X.functionField := by
  refine IsScalarTower.of_algebraMap_eq fun c => ?_
  rw [algebraMap_functionField, algebraMap_stalk,
    ← Scheme.algebraMap_germ_eq_germToFunctionField (X := X) (show x ∈ (⊤ : X.Opens) from trivial)]

end Scalars

end GroundTheory.Arith.SchemeCoh
