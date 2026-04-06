import Mathlib.GroupTheory.Congruence.Defs
namespace Con

@[to_additive]
theorem comap_conGen_of_Bijective {M N : Type*} [Mul M] [Mul N] (f : M → N)
    (hf : Function.Bijective f) (H : ∀ (x y : M), f (x * y) = f x * f y) (rel : N → N → Prop) :
    Con.comap f H (conGen rel) = conGen (fun x y ↦ rel (f x) (f y)) := by
  ext a b
  constructor
  · intro h
    simp only [Con.comap_rel] at h
    have H : ∀ n1 n2, (conGen rel) n1 n2 → ∀ a b, f a = n1 → f b = n2 →
        (conGen fun x y ↦ rel (f x) (f y)) a b := by
      intro n1 n2 h
      induction h with
      | of x y h =>
        intro _ _ fa fb
        apply ConGen.Rel.of
        rw [fa, fb]
        exact h
      | refl x =>
        intro _ _ fc fd
        rw [hf.1 (fc.trans fd.symm)]
        exact ConGen.Rel.refl _
      | symm _ h => exact fun a b fs fb ↦ ConGen.Rel.symm (h b a fb fs)
      | trans _ _ ih ih1 =>
        exact fun a b fa fb ↦ Exists.casesOn (hf.right _) fun c' hc' ↦
        ConGen.Rel.trans (ih a c' fa hc') (ih1 c' b hc' fb)
      | mul _ _ ih ih1 =>
        rename_i w x y z _ _
        intro a b fa fb
        rcases Function.bijective_iff_has_inverse.mp hf with ⟨f', is_inv⟩
        have Ha : a = f' w * f' y := by
          rw [← is_inv.1 a, fa]
          have H : f (f' (w * y)) = f (f' w * f' y) := by
            rw [is_inv.2 (w * y), H, is_inv.2 w, is_inv.2 y]
          exact hf.1 H
        have Hb : b = f' x * f' z := by
          rw [← is_inv.1 b, fb]
          have H : f (f' (x * z)) = f (f' x * f' z) := by
            rw [is_inv.2 (x * z), H, is_inv.2 x, is_inv.2 z]
          exact hf.1 H
        rw [Ha, Hb]
        exact ConGen.Rel.mul (ih (f' w) (f' x) (is_inv.right w) (is_inv.right x))
          (ih1 (f' y) (f' z) (is_inv.right y) (is_inv.right z))
    exact H (f a) (f b) h a b rfl rfl
  intro h
  simp only [Con.comap_rel]
  exact ConGen.Rel.rec (fun x y h ↦ ConGen.Rel.of (f x) (f y) h) (fun x ↦ ConGen.Rel.refl (f x))
    (fun _ h ↦ ConGen.Rel.symm h) (fun _ _ h1 h2 ↦ h1.trans h2) (fun {w x y z} _ _ h1 h2 ↦
    (congrArg (fun a ↦ (conGen rel) a (f (x * z))) (H w y)).mpr
    (((congrArg (fun a ↦ (conGen rel) (f w * f y) a) (H x z))).mpr
    (ConGen.Rel.mul h1 h2))) h

end Con
