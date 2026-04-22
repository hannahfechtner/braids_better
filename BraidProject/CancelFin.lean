import BraidProject.Cancellability
import BraidProject.ConvertToFinHelpMe

open Braid

theorem BraidMonoidInf.cancel_right_of_BraidMonoidFin_eq {a : ℕ} (c d e : FreeMonoid (Fin a.pred))
    (h : BraidMonoidFin.mk _ (c * e) = BraidMonoidFin.mk _ (d * e)) :
    (BraidMonoidInf.mk ((FreeMonoid.map (λ i : Fin a.pred => i.val) c))
    = BraidMonoidInf.mk ((FreeMonoid.map (λ i : Fin a.pred => i.val) d))) := by
  have := BraidMonoidInf.eq_of_BraidMonoidFin_eq _ _ _ h
  rw [map_mul, map_mul, map_mul] at this
  exact right_cancellative this

theorem BraidMonoidFin.cancel_right_mk {n : ℕ} (a b c : FreeMonoid (Fin n.pred)) (h : BraidMonoidFin.mk _ (a * c) =
    BraidMonoidFin.mk _ (b * c)) : BraidMonoidFin.mk _ a  = BraidMonoidFin.mk _ b :=
  BraidMonoidFin.eq_of_BraidMonoidInf_eq' (BraidMonoidInf.cancel_right_of_BraidMonoidFin_eq a b c h)

theorem BraidMonoidFin.right_cancellative {n : ℕ} (a b c : BraidMonoidFin n) (h : a * c = b * c) :
    a = b := by
  unfold BraidMonoidFin at a b c
  induction a with | h a'
  induction b with | h b'
  induction c with | h c'
  exact BraidMonoidFin.cancel_right_mk _ _ _ h

theorem BraidMonoidInf.cancel_left_of_BraidMonoidFin_eq {a : ℕ} (c d e : FreeMonoid (Fin a.pred))
    (h : BraidMonoidFin.mk _ (e * c) = BraidMonoidFin.mk _ (e * d)) :
    BraidMonoidInf.mk (FreeMonoid.map (fun i : Fin a.pred => i.val) c) =
    BraidMonoidInf.mk (FreeMonoid.map (fun i : Fin a.pred => i.val) d) := by
  have := BraidMonoidInf.eq_of_BraidMonoidFin_eq _ _ _ h
  rw [map_mul, map_mul, map_mul] at this
  exact left_cancellative this

theorem BraidMonoidFin.cancel_left {n : ℕ} (a b c : FreeMonoid (Fin n.pred))
    (h : BraidMonoidFin.mk _ (c * a) = BraidMonoidFin.mk _ (c * b)) :
    BraidMonoidFin.mk _ a = BraidMonoidFin.mk _ b :=
  BraidMonoidFin.eq_of_BraidMonoidInf_eq'
    (BraidMonoidInf.cancel_left_of_BraidMonoidFin_eq a b c h)

theorem BraidMonoidFin.left_cancellative {n : ℕ} (a b c : BraidMonoidFin n) (h : c * a = c * b) :
    a = b := by
  unfold BraidMonoidFin at a b c
  induction a with | h a'
  induction b with | h b'
  induction c with | h c'
  exact BraidMonoidFin.cancel_left _ _ _ h

instance {n : ℕ} : IsLeftCancelMul (BraidMonoidFin n) := ⟨fun _ _ _ => BraidMonoidFin.left_cancellative _ _ _⟩

instance {n : ℕ} : IsRightCancelMul (BraidMonoidFin n) := ⟨fun _ _ _ => BraidMonoidFin.right_cancellative _ _ _⟩

instance {n : ℕ} : CancelMonoid (BraidMonoidFin n) where
  mul_right_cancel := fun _ _ _ => BraidMonoidFin.right_cancellative _ _ _
  mul_left_cancel := fun _ _ _ => BraidMonoidFin.left_cancellative _ _ _
