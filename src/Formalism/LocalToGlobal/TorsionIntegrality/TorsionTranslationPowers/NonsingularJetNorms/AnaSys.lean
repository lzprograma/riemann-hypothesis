module

public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementA
public import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.AnaSysW
public import Formalism.LocalToGlobal.TorsionIntegrality.FrobeniusFibreCurves.FinalB
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.ChordEquation
public import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.CubeThreeR

@[expose] public section

open PowerSeries

noncomputable section

namespace Formalism.L2.Th1.E

namespace AnaSys

open Formalism.L2.Th1

variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])

theorem unif_curveL : Unif l L ι (curveL l L ι) :=
  ⟨(A.shortInv ℂ_[l] (ι L.g₂) (ι L.g₃)).2.1, (A.shortInv ℂ_[l] (ι L.g₂) (ι L.g₃)).2.2.1⟩

theorem cc_phL : constantCoeff (phL l L ι) = 0 :=
  AnaSysW.cc_phW l L ι (curveL l L ι)

theorem gT_mem (t : ℂ) (ht : t ∈ L.lattice) : ∃ ε : ℂ_[l], ‖ε‖ = 1 ∧ gT l L ι t = C ε * X :=
  AnaSysW.gW_mem l L ι (curveL l L ι) t ht

theorem nonsing (t : ℂ) (ht : t ∉ L.lattice) :
    (curveL l L ι).toAffine.Nonsingular (ι (L.weierstrassP t)) (ι (L.derivWeierstrassP t) / 2) := by
  have h := AnaSysW.nonsing (unif_curveL l L ι) t ht
  have hb : (curveL l L ι).b₂ = 0 := (A.shortInv ℂ_[l] _ _).1
  have ha₁ : (curveL l L ι).a₁ = 0 := rfl
  have ha₃ : (curveL l L ι).a₃ = 0 := rfl
  simpa only [AnaSysW.xc, AnaSysW.yc, hb, ha₁, ha₃, zero_div, sub_zero, zero_mul] using h

theorem ptOf_notMem (t : ℂ) (ht : t ∉ L.lattice) :
    ptOf l L ι t = .some _ _ (nonsing l L ι t ht) := by
  simp [ptOf, ht, nonsing l L ι t ht]

theorem ptOf_eq_ptW (t : ℂ) : ptOf l L ι t = ptW l L ι (curveL l L ι) t := by
  by_cases ht : t ∈ L.lattice
  · simp [ptOf, ht, AnaSysW.ptW_mem l L ι (curveL l L ι) t ht]
  · rw [ptOf_notMem l L ι t ht, AnaSysW.ptW_notMem (unif_curveL l L ι) t ht,
      WeierstrassCurve.Affine.Point.some.injEq]
    have hb : (curveL l L ι).b₂ = 0 := (A.shortInv ℂ_[l] _ _).1
    have ha₁ : (curveL l L ι).a₁ = 0 := rfl
    have ha₃ : (curveL l L ι).a₃ = 0 := rfl
    simp [AnaSysW.xc, AnaSysW.yc, hb, ha₁, ha₃]

theorem px_ptOf (t : ℂ) (ht : t ∉ L.lattice) :
    px (curveL l L ι) (ptOf l L ι t) = ι (L.weierstrassP t) := by
  rw [ptOf_notMem l L ι t ht]
  rfl

theorem wpBridge : WpBridge := fun l _ L ι =>
  AnaSysW.wpBridge (unif_curveL l L ι)

theorem transWpBridge : TransWpBridge := by
  intro l _ L ι t ht
  have h := AnaSysW.transW (unif_curveL l L ι) t ht
  have hb : (curveL l L ι).b₂ = 0 := (A.shortInv ℂ_[l] _ _).1
  have hb0 : (AnaSysW.W0 l ι (curveL l L ι)).b₂ = 0 := by
    simp [AnaSysW.W0, hb]
  have hxf : AnaSysW.xf L (AnaSysW.W0 l ι (curveL l L ι)) t = fun z => L.weierstrassP (z + t) := by
    funext z
    simp [AnaSysW.xf, hb0]
  rw [hxf, ← ptOf_eq_ptW l L ι t] at h
  exact h

end AnaSys

theorem PtOfZero_of : PtOfZero := fun l _ L ι t => by
  rw [AnaSys.ptOf_eq_ptW]
  exact AnaSysW.ptW_zero_iff (AnaSys.unif_curveL l L ι) t

theorem AnalyticSys_of : AnalyticSys := fun l _ L ι π hπ =>
  analytic_translate_system_model l L ι (curveL l L ι) (AnaSys.unif_curveL l L ι) π
    (fun t => (hπ t).trans (AnaSys.ptOf_eq_ptW l L ι t))

end Formalism.L2.Th1.E
