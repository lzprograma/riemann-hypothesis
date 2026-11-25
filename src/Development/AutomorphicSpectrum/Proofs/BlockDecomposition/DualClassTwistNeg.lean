module

public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SmoothContragredientIrreducibleAndReflexive
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitarisableOfSquareIntegrable
import Mathlib.Tactic.Linter.Style

@[expose] public section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc

noncomputable section

namespace GlobalTheory.CompanionTheory.ZcDual

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isIrreducible_contra (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible) : (contra π).IsIrreducible := by
  exact GlobalTheory.ContraRefl.contra_isIrreducible (GlobalTheory.SqIntUnit.compactOpen_basis k n) (hA k n V π hs hi) hi

theorem dualCl_eq (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) :
    dualCl x = IrrGL.of (contra x.rep) (isSmooth_contra _) (isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr) := by
  unfold dualCl
  rw [dite_eq_left (isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr)]

theorem nonempty_equiv_contra_twist (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {n : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    {χ χ' : kˣ →* ℂˣ} (hχ : IsSmoothChar χ) (hχ' : IsSmoothChar χ') (h : χ * χ' = 1) :
    Nonempty ((twist (contra π) (detChar (Fin n) χ')).Equiv (contra (twist π (detChar (Fin n) χ)))) := by
  have hψ : IsSmoothChar (detChar (Fin n) χ) := hχ.detChar
  have hinv : ∀ g : GL (Fin n) k,
      ((detChar (Fin n) χ' g : ℂˣ) : ℂ) = ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) := by
    intro g
    have h1 : χ (Matrix.GeneralLinearGroup.det g) * χ' (Matrix.GeneralLinearGroup.det g) = 1 := by
      rw [← MonoidHom.mul_apply, h, MonoidHom.one_apply]
    have h2 : χ' (Matrix.GeneralLinearGroup.det g) = (χ (Matrix.GeneralLinearGroup.det g))⁻¹ :=
      eq_inv_of_mul_eq_one_right h1
    show ((χ' (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ) =
      ((χ (Matrix.GeneralLinearGroup.det g⁻¹) : ℂˣ) : ℂ)
    rw [h2, map_inv, map_inv]
  have hdual : ∀ (g : GL (Fin n) k) (l : Module.Dual ℂ V),
      (twist π (detChar (Fin n) χ)).dual g l = ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) • π.dual g l := by
    intro g l
    apply LinearMap.ext
    intro v
    show l (((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) • π g⁻¹ v) = ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) • l (π g⁻¹ v)
    exact map_smul l _ _
  have hker : ∀ g : GL (Fin n) k, g ∈ (detChar (Fin n) χ).ker →
      ((detChar (Fin n) χ g⁻¹ : ℂˣ) : ℂ) = 1 := by
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    rw [map_inv, hg, inv_one, Units.val_one]
  have hkn : ((detChar (Fin n) χ).ker : Set (GL (Fin n) k)) ∈ nhds (1 : GL (Fin n) k) :=
    IsOpen.mem_nhds hψ (Subgroup.one_mem _)
  have heq : smoothPart π.dual = smoothPart (twist π (detChar (Fin n) χ)).dual := by
    ext l
    constructor
    · intro hl
      apply mem_smoothPart_of_nhds
      refine Filter.mem_of_superset (Filter.inter_mem (IsOpen.mem_nhds hl (by
        show π.dual 1 l = l
        rw [map_one]
        rfl)) hkn) ?_
      rintro g ⟨hg1, hg2⟩
      have h3 : π.dual g l = l := hg1
      show (twist π (detChar (Fin n) χ)).dual g l = l
      rw [hdual, hker g hg2, one_smul]
      exact h3
    · intro hl
      apply mem_smoothPart_of_nhds
      refine Filter.mem_of_superset (Filter.inter_mem (IsOpen.mem_nhds hl (by
        show (twist π (detChar (Fin n) χ)).dual 1 l = l
        rw [map_one]
        rfl)) hkn) ?_
      rintro g ⟨hg1, hg2⟩
      have h3 : (twist π (detChar (Fin n) χ)).dual g l = l := hg1
      rw [hdual, hker g hg2, one_smul] at h3
      show π.dual g l = l
      exact h3
  have htw : ∀ (g : GL (Fin n) k) (l : smoothPart π.dual),
      ((twist (contra π) (detChar (Fin n) χ') g l : smoothPart π.dual) : Module.Dual ℂ V) =
        ((detChar (Fin n) χ' g : ℂˣ) : ℂ) • ((contra π g l : smoothPart π.dual) : Module.Dual ℂ V) :=
    fun _ _ => rfl
  have htw2 : ∀ (g : GL (Fin n) k) (v : V),
      (twist π (detChar (Fin n) χ)) g v = ((detChar (Fin n) χ g : ℂˣ) : ℂ) • π g v :=
    fun _ _ => rfl
  exact ⟨{ toLinearEquiv := LinearEquiv.ofEq _ _ heq
           isIntertwining' := fun g => by
             apply LinearMap.ext
             intro l
             apply Subtype.ext
             apply LinearMap.ext
             intro v
             simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_ofEq_apply, htw,
               LinearMap.smul_apply, contra_apply, htw2, map_smul, smul_eq_mul, hinv] }⟩

theorem dualCl_nu : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (_ : GlobalTheory.Published.IrreducibleAdmissibleGL) (x : IrrGL (k := k)) (s : ℂ), dualCl (x.nu s) = (dualCl x).nu (-s) := by
  intro k _ _ _ _ hA x s
  have hs' : IsSmoothChar (absPow k s) := isSmoothChar_of_isUnram (isUnram_absPow k s)
  have hn' : IsSmoothChar (absPow k (-s)) := isSmoothChar_of_isUnram (isUnram_absPow k (-s))
  have hmul : absPow k s * absPow k (-s) = 1 := by
    rw [absPow_neg, mul_inv_cancel]
  have hψ : IsSmoothChar (detChar (Fin x.fst) (absPow k s)) := hs'.detChar
  have hψn : IsSmoothChar (detChar (Fin x.fst) (absPow k (-s))) := hn'.detChar
  obtain ⟨e1⟩ : Nonempty ((x.nu s).rep.Equiv (twist x.rep (detChar (Fin x.fst) (absPow k s)))) :=
    IrrRep.nonempty_equiv_rep (irrTwist x.snd.rep (detChar (Fin x.fst) (absPow k s)) hψ)
  let e2 := GlobalTheory.ContraRefl.contraEquiv e1
  obtain ⟨e3⟩ := nonempty_equiv_contra_twist hA x.rep x.2.rep.smooth x.2.rep.irr hs' hn' hmul
  have hc := isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr
  obtain ⟨e4⟩ := IrrRep.nonempty_equiv_rep
    (⟨_, contra x.rep, isSmooth_contra _, hc⟩ : IrrRep (GL (Fin x.fst) k))
  have e5 := twistEquiv e4 (detChar (Fin x.fst) (absPow k (-s)))
  rw [dualCl_eq hA, dualCl_eq hA]
  refine Sigma.ext ?_ ?_
  · rfl
  apply heq_of_eq
  exact IrrRep.cl_eq_iff.mpr ⟨(e2.symm.trans e3.symm).trans e5.symm⟩

end GlobalTheory.CompanionTheory.ZcDual

end
