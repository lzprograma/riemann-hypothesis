module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SqUniq
import Mathlib.RepresentationTheory.Stabilizer
import Mathlib.Tactic.Linter.Style

@[expose] public section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

theorem UpperTheory.V.Lit.Bor.sqMem :
    UpperTheory.V.Lit.Bor.SqMem := by
  intro E _ _ _ a ha μ _ r χ hχ φ hφ
  change IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ} ∧ _
  induction hφ using Submodule.span_induction with
  | mem φ h =>
    have hl : IsOpen {k | finRep E a k φ = φ} := h.level
    have ho : IsOpen {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ} := by
      refine Subgroup.isOpen_of_mem_nhds (Representation.stabilizer (finRep E a) (mulChi a χ φ))
        (g := 1) (Filter.mem_of_superset
          ((hl.inter (isOpen_ker_chiDet (a := a) χ)).mem_nhds ⟨by simp, by simp⟩)
          (show _ ⊆ {k | finRep E a k (mulChi a χ φ) = mulChi a χ φ} from ?_))
      rintro k ⟨h1, h2⟩
      have h1' : rt E a (finGL E a k) φ = φ := h1
      have h2' : chiDet a χ (finGL E a k) = 1 := h2
      change rt E a (finGL E a k) (mulChi a χ φ) = _
      rw [rt_mulChi, h1', h2']
      simp
    have hs := sqUniq E a ha r χ hχ φ h.one (by simpa using h.sq [])
    refine ⟨ho, (CuspidalL2GL.memL2_iff_isSqInt (ContAut.continuous_of_isOpen_stab E a _ ho) (fun γ g => ?_) hs.1).2 hs⟩
    rw [mulChi_apply, mulChi_apply, map_mul, chiDet_ratGL, one_mul, h.left]
  | zero =>
    rw [map_zero]
    refine ⟨?_, fun _ _ _ => rfl, MeasureTheory.MemLp.zero⟩
    convert isOpen_univ using 1
    ext k
    simp only [Set.mem_setOf_eq, map_zero, Set.mem_univ]
  | add φ ψ _ _ h h' =>
    rw [map_add (f := _)]
    refine ⟨Subgroup.isOpen_mono
      (H₁ := Representation.stabilizer (finRep E a) (mulChi a χ φ) ⊓
        Representation.stabilizer (finRep E a) (mulChi a χ ψ))
      (H₂ := Representation.stabilizer (finRep E a) (mulChi a χ φ + mulChi a χ ψ))
      (by apply Representation.le_stabilizer_add)
      (by rw [Subgroup.coe_inf]; exact h.1.inter h'.1),
      fun γ hγ g => congrArg₂ (· + ·) (h.2.1 γ hγ g) (h'.2.1 γ hγ g), h.2.2.add h'.2.2⟩
  | smul c φ _ h =>
    rw [map_smul]
    refine ⟨Subgroup.isOpen_mono
      (H₁ := Representation.stabilizer (finRep E a) (mulChi a χ φ))
      (H₂ := Representation.stabilizer (finRep E a) (c • mulChi a χ φ))
      (by apply Representation.le_stabilizer_smul) h.1,
      fun γ hγ g => congrArg (c • ·) (h.2.1 γ hγ g), h.2.2.const_smul c⟩
