module

public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.KernelLattices.XiIndCClass

@[expose] public section

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Fr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.SameOn (B : Finset (HeightOneSpectrum (𝓞 E))) (d d' : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) : Prop := ∀ P ∈ B, d'.1.at P = d.1.at P


theorem DecoSet.sameOn_up {B : Finset (HeightOneSpectrum (𝓞 E))} (d : DecoSet (E := E) (n := n) (ST := ST) (SG := SG)) (P : ST) (hne : conjPrime₂ P.1 ≠ P.1)
    (hB : ∀ P' ∈ B, P' ≠ P.1 ∧ P' ≠ conjPrime₂ P.1) (q : 𝓞 E) {x : Sp E n} (hx : x ∈ d.1.N) : DecoSet.SameOn B d (d.up P q x) := by
  intro P' hP'
  unfold DecoSet.up
  split_ifs with hok
  · show localization₂ P'.asIdeal (upN P.1.asIdeal d.1.N x) = localization₂ P'.asIdeal d.1.N
    exact ((upN_spec d.2.lat d.2.uni P.1 hne hx).2.2.1 P' (hB P' hP').1 (hB P' hP').2).localization_eq
  · rfl

end Fr

section Yb

variable {X : Fields} {Pr : Primes X} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

end Yb

end Formalism.L2.Col
