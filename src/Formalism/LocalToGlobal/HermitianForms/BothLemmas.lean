module

public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel

@[expose] public section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG

namespace Formalism.L2.Forms

theorem reGL_rfl {a : ℕ} (R : Type) [CommRing R] (x : GL (Fin a) R) : reGL rfl R x = x := by
  apply Units.ext
  ext i j
  simp [reGL]

theorem reV_rfl {a : ℕ} (E : Type) [Field E] (x : Fin a → E) : reV rfl E x = x := by
  ext i
  simp [reV]

theorem reL_rfl {a : ℕ} {E : Type} [Field E] [NumberField E] (L : Submodule (𝓞 E) (Fin a → E)) : reL rfl L = L := by
  ext z
  simp [reL, reV_rfl]

end Formalism.L2.Forms
