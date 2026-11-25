module

public import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects

import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNsmulMem

@[expose] public section

theorem UpperTheory.Reformulated.B.ExistsZsmulMem.exists_zsmul_mem.{u_1, u_2} :
    ∀ {E : Type u_1} [Field E] [NumberField E] {W : Type u_2} [AddCommGroup W]
    [_root_.Module E W] {La : AddSubgroup W},
    GroundTheory.Heights₂.Heights.FiniteCovolume.IsLattice (E := E) La →
      ∀ (x : W),
        ∃ (d : ℤ),
          d ≠ (0 : ℤ) ∧
            d • x ∈ La := by
  intro E _ _ W _ _ La h x
  obtain ⟨d, hd, hmem⟩ := UpperTheory.Reformulated.B.ExistsNsmulMem.exists_nsmul_mem h x
  exact ⟨(d : ℤ), by exact_mod_cast hd.ne', by simpa using hmem⟩
