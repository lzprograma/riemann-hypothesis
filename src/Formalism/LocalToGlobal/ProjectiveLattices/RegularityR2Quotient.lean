module

public import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  (Xo : Moduli Dw l) (c : Coeff l)

def trivCls : ∀ (T : CDVR) (ι : c.F →+* T.Fr), IntFr Xo c T ι → Prop :=
  fun T ι _ => ∀ a : c.F, a ≠ 0 → ∃ u : T.Vˣ, algebraMap T.V T.Fr (u : T.V) = ι a

structure QPt where
  T : CDVR
  ι : c.F →+* T.Fr
  y : IntFr Xo c T ι
  triv : trivCls Xo c T ι y

def ordQ (q : QPt Xo c) (f : Rul Xo c) : EReal := nval q.T.V 1 (evI q.y f)

def RegularityR1Quotient (C : ((E →+* ℂ) × ℕ → ℕ) → ℕ → Submodule c.F (Rul Xo c)) : Prop :=
  ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), ∀ f ∈ C a n,
    (∃ la : HeightOneSpectrum (𝓞 c.F), ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f) →
      ∀ q : QPt Xo c, 0 ≤ ordQ Xo c q f

end Formalism.L2.Pj
