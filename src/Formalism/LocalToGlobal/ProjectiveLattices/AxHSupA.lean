module

import Formalism.LocalToGlobal.ProjectiveLattices.PtOfSPf
public import Formalism.LocalToGlobal.ProjectiveLattices.AxHSup
public import Formalism.LocalToGlobal.ProjectiveLattices.HasDataCondition
public import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
public import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts

@[expose] public section

noncomputable section

namespace Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem evR_frMap (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z)) (f : Rul Xo c)
    (hf : IsNatural (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) f)
    {K₁ K₂ : Type} [CommRing K₁] [Algebra c.F K₁] [CommRing K₂] [Algebra c.F K₂] (φ : K₁ →ₐ[c.F] K₂)
    (y₁ : FrPt Xo c K₁) (hT1 : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y₁)
    (y₂ : FrPt Xo c K₂) (hm : FrMap φ y₁ y₂) : evR Xo c f y₂ = φ (evR Xo c f y₁) := by
  apply _root_.Formalism.L2.Pj.pos_evR <;> assumption

end Gen

section Rec

open Formalism.BasicNotions Formalism.MainNotions

variable {D : D7} {T : Top D} (hL : LawsP T) (j : ℕ) [IsCMField D.host.E] [Fintype (Comp (T.Q.Xo j) T.Q.c)]

def SupRLeRec (fn : ∀ σ : T.Q.c.F →+* ℂ, FrPt (T.Q.Xo j) T.Q.c (CAt σ) → Ix (T.Q.Dw j) → ℝ) (i : ℕ)
    (η : (recB hL.toLawsCore).Cusp j (wEt D j i)) : Prop :=
  ∀ sg, supR (T.Q.Xo j) T.Q.c fn sg (wtA (wEt D j i)) (wEt D j i).n η.1 ≤ (recB hL.toLawsCore).supN j _ sg η

end Rec

end Formalism.L2.Pj
