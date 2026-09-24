import BraidProject.Additions.FreeMonoid
import BraidProject.Additions.List
import BraidProject.Additions.SignedList
import BraidProject.Additions.FreeGroup

def SignedList.bounded [LT α] (k : α) (u : List (α × Bool)) := ∀ x ∈ u, x.1 < k

theorem SignedList.bounded_append [LT α] {a b : List (α × Bool)}: SignedList.bounded n (a ++ b) ↔ SignedList.bounded n a ∧ SignedList.bounded n b := by
  constructor
  · intro h
    constructor
    · exact fun x hx => h _ (List.mem_append_left b hx)
    exact fun x hx =>  h _ (List.mem_append_right a hx)
  intro h x hx
  apply List.mem_append.mp at hx
  cases hx with
  | inl h1 => apply h.1 _ h1
  | inr h2 => apply h.2 _ h2

theorem SignedList.bounded_tail  [LT α] {a2 : List (α × Bool)} (h : SignedList.bounded n (a1 :: a2)) : SignedList.bounded n a2 :=
  fun _ hx => h _ (List.mem_cons_of_mem _ hx)

theorem SignedList.bounded_invRev  [LT α] {a : List (α × Bool)} (h : SignedList.bounded n a) : SignedList.bounded n (FreeGroup.invRev a) := by
  intro x hx
  unfold FreeGroup.invRev at hx
  simp only [List.mem_map, List.mem_reverse] at hx
  rcases hx with ⟨a1, ha1⟩
  rw [← ha1.2]
  apply h (a1.1, a1.2) ha1.1

theorem SignedList.bounded_trans [LT α] [IsTrans α (· < ·)] {n m : α}
    {a : List (α × Bool)} (h : SignedList.bounded n a) (h2 : n < m) :
    SignedList.bounded m a := by
  intro x hx
  exact Trans.trans (h x hx) h2

def SignedList.mapNatToFin (L : List (ℕ × Bool)) (n : ℕ) (hL : SignedList.bounded n L) : List (Fin n × Bool) :=
  (List.pmap (λ ⟨i, b⟩ h => (Fin.mk i h, b) ) L) hL

theorem SignedList.mapNatToFin_append (ha : SignedList.bounded n a) (hb : SignedList.bounded n b) :
    SignedList.mapNatToFin (a ++ b) n (by apply SignedList.bounded_append.mpr; constructor; assumption; assumption) =
    SignedList.mapNatToFin a n ha ++ SignedList.mapNatToFin b n hb := by
  unfold SignedList.mapNatToFin
  rw [List.pmap_append]

theorem SignedList.mapNatToFin_append' (hbb : SignedList.bounded n (a ++ b)) :
    SignedList.mapNatToFin (a ++ b) n hbb =
    SignedList.mapNatToFin a n (SignedList.bounded_append.mp hbb).1 ++ SignedList.mapNatToFin b n (SignedList.bounded_append.mp hbb).2 := by
  unfold SignedList.mapNatToFin
  rw [List.pmap_append]

theorem SignedList.mapNatToFin_cons (ha : SignedList.bounded n (a1 :: a2)) (ha' : SignedList.bounded n a2) :
    SignedList.mapNatToFin (a1 :: a2) n ha = (Fin.mk a1.1 (ha a1 (by simp)), a1.2) :: SignedList.mapNatToFin a2 n ha' := by
  unfold SignedList.mapNatToFin
  simp [List.pmap_cons]

theorem SignedList.mapNatToFin_invRev (ha : SignedList.bounded n a) (ha' : SignedList.bounded n (FreeGroup.invRev a)) :
    SignedList.mapNatToFin (FreeGroup.invRev a) n ha' = FreeGroup.invRev (SignedList.mapNatToFin a n ha) := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    rw [SignedList.mapNatToFin_cons ha (SignedList.bounded_tail ha)]
    conv => rhs; rw [FreeGroup.invRev_cons]
    specialize ih (SignedList.bounded_tail ha) (SignedList.bounded_invRev (SignedList.bounded_tail ha))
    rw [← ih]
    have : FreeGroup.invRev [(⟨head.1, (ha head (by simp))⟩, head.2)] =
        SignedList.mapNatToFin (FreeGroup.invRev [head]) n (SignedList.bounded_invRev
        (by intro x hx; simp at hx; rw [hx]; exact ha head (by simp))) := rfl
    rw [this]
    rw [← SignedList.mapNatToFin_append' (by rw [← FreeGroup.invRev_cons]; exact SignedList.bounded_invRev ha)]
    congr
    rw [FreeGroup.invRev_cons]

theorem SignedList.mapNatToFin_map_val {n : ℕ} (a : List (ℕ × Bool)) (ha : SignedList.bounded n a) :
    List.map (fun p : Fin n × Bool => (p.1.val, p.2)) (SignedList.mapNatToFin a n ha) = a := by
  unfold SignedList.mapNatToFin
  induction a with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.pmap, List.map_cons, List.cons.injEq]
    exact ⟨trivial, ih _⟩

theorem SignedList.map_val_mapNatToFin {n : ℕ} (a : List (Fin n × Bool))
    (ha : SignedList.bounded n (List.map (fun p : Fin n × Bool => (p.1.val, p.2)) a)) :
    SignedList.mapNatToFin (List.map (fun p : Fin n × Bool => (p.1.val, p.2)) a) n ha = a := by
  induction a with
  | nil => rfl
  | cons head tail ih =>
    unfold SignedList.mapNatToFin
    simp only [List.map_cons, List.pmap, List.cons.injEq]
    exact ⟨trivial, ih _⟩

-- helps connect SignedList.mapNatToFin with FreeMonoid.mapNatToFin
theorem SignedList.mapNatToFin_of_is_true (d : List (ℕ × Bool)) (n : ℕ) (hdt : SignedList.is_true d)
    (hdb : SignedList.bounded n d)
    (hdm : ∀ x ∈ List.map (fun p : ℕ × Bool => p.1) d, x < n) :
    SignedList.mapNatToFin d n hdb =
      List.map (fun x => (x, true)) (FreeMonoid.mapNatToFin n (List.map (fun p : ℕ × Bool => p.1) d) hdm) := by
  induction d with
  | nil => rfl
  | cons head tail ih =>
    have ht : SignedList.bounded n tail := fun x hx => hdb x (List.mem_cons_of_mem _ hx)
    have htm : ∀ x ∈ List.map (fun p : ℕ × Bool => p.1) tail, x < n := by
      intro x hx
      apply hdm
      rw [List.map_cons, List.mem_cons]
      right; exact hx
    rw [mapNatToFin_cons _ ht, ih (SignedList.is_true_of_cons hdt).2 ht htm]
    have : head.2 = true := (SignedList.is_true_of_cons hdt).1 head (by simp)
    congr

theorem SignedList.mapNatToFin_of_is_false (e : List (ℕ × Bool)) (n : ℕ) (hef : SignedList.is_false e)
    (heb : SignedList.bounded n e)
    (hem : ∀ x ∈ List.map (fun p : ℕ × Bool => p.1) e.reverse, x < n) :
    SignedList.mapNatToFin e n heb =
      FreeGroup.invRev (List.map (fun x => (x, true))
        (FreeMonoid.mapNatToFin n (List.map (fun p : ℕ × Bool => p.1) e.reverse) hem)) := by
  have helper : ∀ x ∈ List.map (fun p : ℕ × Bool => p.1) (FreeGroup.invRev e), x < n := by
    intro x hx
    simp only [List.mem_map, Prod.exists, exists_and_right, Bool.exists_bool, exists_eq_right] at hx
    cases hx with
    | inl h =>
      have := SignedList.bounded_invRev heb (x, false) h
      aesop
    | inr h =>
      have := SignedList.bounded_invRev heb (x, true) h
      aesop
  rw [← @FreeGroup.invRev_invRev _ (SignedList.mapNatToFin e n heb),
    ← SignedList.mapNatToFin_invRev heb (SignedList.bounded_invRev heb),
    SignedList.mapNatToFin_of_is_true _ n (SignedList.is_true_invRev_of_false hef) (SignedList.bounded_invRev heb) helper]
  simp [FreeGroup.invRev]
  rfl
