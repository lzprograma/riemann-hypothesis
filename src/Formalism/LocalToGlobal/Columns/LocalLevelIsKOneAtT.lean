module

public import Formalism.LocalToGlobal.Columns.TiedCls
public import Formalism.LocalToGlobal.HermitianForms.RankEqFirstLevel
import Formalism.LocalToGlobal.Columns.BaseLemmas
public import Formalism.LocalToGlobal.HermitianForms.BothLemmas

@[expose] public section

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

structure HCrd {X : Fields} (Pr : Primes X) (n : ℕ) {cls : Type} (L : cls → Submodule (𝓞 X.E) (Fin n → X.E)) where
  n' : ℕ
  hn : n' = n
  J : Matrix (Fin n') (Fin n') X.E
  hJ : J = 1
  f : ℕ
  hf : f = X.f
  bad : Set (HeightOneSpectrum (𝓞 X.F))
  hbad : bad = plUnder X.F Pr.vGs
  lat : cls → Submodule (𝓞 X.E) (Fin n' → X.E)
  hlat : ∀ c, lat c = Formalism.L2.Forms.reL hn.symm (L c)

structure LevPack {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (hc : CMData F E) (n : ℕ)
    (J : Matrix (Fin n) (Fin n) E) (gp : Fin 2 → ℕ) (T f : ℕ) (bad : Set (HeightOneSpectrum (𝓞 F))) {cls : Type} (stab : cls → Type)
    [∀ c, Group (stab c)] (lat : cls → Submodule (𝓞 E) (Fin n → E)) where
  lev : Formalism.L2.Forms.StepLevel F E hc.sig J T f bad
  cls : RecCls hc J lev.Lb lev.U stab lat
  bad_iff : ∀ v : HeightOneSpectrum (𝓞 F), v ∈ bad ↔ ((gp 0 : 𝓞 F) ∈ v.asIdeal ∨ (gp 1 : 𝓞 F) ∈ v.asIdeal)
  Uloc_g : ∀ (i : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp i : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F),
    (x ∈ levelVL hc.sig J v lev.Lb ∧ ∀ y ∈ Formalism.L2.Herm.locL v lev.Lb, ∃ z ∈ Formalism.L2.Herm.locL v lev.Lb,
      (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = (gp i : E ⊗[F] v.adicCompletion F) • z) → x ∈ lev.Uloc v
  UlocAlt : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x : GL (Fin n) (E ⊗[F] v.adicCompletion F), x ∈ lev.Uloc v ↔
    (x ∈ levelVL hc.sig J v lev.Lb ∧
      ∀ y ∈ Formalism.L2.Herm.locL v (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J lev.Lb)),
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ Formalism.L2.Herm.locL v lev.Lb)

section Gen

variable {X : Fields} {Pr : Primes X} (hc : CMData X.F X.E) (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (u : Pr.Word)
  {n : ℕ} [NeZero n] (Λ : LevFam X.E X.K n Pr.vGs)

def LocalLevelIsKOneAtT : Prop :=
  ∀ v : HeightOneSpectrum (𝓞 X.F), (Pr.T u : 𝓞 X.F) ∈ v.asIdeal → ∀ x : GL (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F),
    x ∈ levLoc hc n (Pr.vT u) Pr.vGs Λ.grp v ↔
    (x ∈ levelVL hc.sig (1 : Matrix (Fin n) (Fin n) X.E) v (baseLb X.E n (Pr.vT u)) ∧
      ∀ y ∈ Formalism.L2.Herm.locL v (Submodule.span (𝓞 X.E)
          (dualSet (hc.sig : X.E →+* X.E) (1 : Matrix (Fin n) (Fin n) X.E) (baseLb X.E n (Pr.vT u)))),
        (x : Matrix (Fin n) (Fin n) (X.E ⊗[X.F] v.adicCompletion X.F)) *ᵥ y - y ∈ Formalism.L2.Herm.locL v (baseLb X.E n (Pr.vT u)))


variable (c₀ : DiaG (E := X.E) (ST := Pr.vT u)) (s : DecoCl n (Pr.vT u) Pr.vGs Λ.grp → DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs))

end Gen

section Repack

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {hc : CMData F E}
  {S : HSpace E} {gp : Fin 2 → ℕ} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} {cls : Type} {stab : cls → Type}
  [∀ c, Group (stab c)] {lat : cls → Submodule (𝓞 E) S.V}

end Repack

end Formalism.L2.Col
