module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.PairDefs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.EllFacts
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.ExpOfDeriv
import Mathlib.Tactic.Linter.Style

@[expose] public section

open UpperTheory.V.Lit.Geo
open NumberField Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

private def levSub {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    (U : Subgroup (GL (Fin a) (Af E))) (Ξ : AlgRep E a) : Submodule ℂ (Sm E a) where
  carrier := {φ | IsLevelFn U Ξ φ}
  zero_mem' := ⟨fun _ _ => rfl, fun u _ => map_zero _, fun m _ => by simp⟩
  add_mem' := fun {φ ψ} h h' => ⟨fun γ g => congrArg₂ (· + ·) (h.1 γ g) (h'.1 γ g),
    fun u hu => by rw [map_add (f := _), h.2.1 u hu, h'.2.1 u hu],
    fun m hm => by rw [map_add (f := _), h.2.2 m hm, h'.2.2 m hm, smul_add]⟩
  smul_mem' := fun c φ h => ⟨fun γ g => congrArg (c • ·) (h.1 γ g),
    fun u hu => by rw [map_smul, h.2.1 u hu],
    fun m hm => by rw [map_smul, h.2.2 m hm, smul_comm]⟩

theorem UpperTheory.V.Lit.Geo.Pf.levInv :
    UpperTheory.V.Lit.Geo.Pf.LevInv := by
  intro E _ _ _ a ha U hU Ξ r χ h1 hχ q α hα X j
  have hφ : IsLevelFn U Ξ (cmp j (α X)) :=
    mem_tens.1 (span_le_tens (N := levSub U Ξ) (fun φ h => h) (hα.val X)) j
  generalize cmp j (α X) = φ at hφ
  refine ⟨fun γ g => ?_, fun t g => ?_, ?_⟩
  · rw [mulChi_apply, mulChi_apply, map_mul, chiDet_ratGL, one_mul, hφ.1]
  · have hz : lie E a (oneL E a) (mulChi a χ φ) = (0 : ℂ) • mulChi a χ φ := by
      rw [hχ.2, hφ.2.2 _ h1, (ellFacts E a).1 ha, mul_one, ← add_smul, neg_add_cancel, zero_smul, map_zero, zero_smul]
    rw [aInv E a _ _ hz t g, zero_mul, Complex.exp_zero, one_mul]
  · change IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ}
    refine isOpen_stab_of_mem_nhds (finRep E a) _ (Filter.mem_of_superset
      ((hU.inter (isOpen_ker_chiDet (a := a) χ)).mem_nhds ⟨U.one_mem, by simp⟩) ?_)
    rintro k ⟨hk, h2⟩
    have h1' : rt E a (finGL E a k) φ = φ := hφ.2.1 k hk
    have h2' : chiDet a χ (finGL E a k) = 1 := h2
    change rt E a (finGL E a k) (mulChi a χ φ) = _
    rw [rt_mulChi, h1', h2']
    simp
