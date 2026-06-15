namespace Classical

universe u v w
/--
Given `h : ∃ x y, p x y`, returns a pair `(x, y)` witnessing `p x y`.
-/
noncomputable def choose₂ {α : Type u} {β : Type w} {p : α → β → Prop}
    (h : ∃ x y, p x y) : α × β :=
  ⟨choose h, choose (Classical.choose_spec h)⟩


/--
Specification theorem for `choose₂`.
-/
theorem choose₂_spec {α : Type u} {β : Type w} {p : α → β → Prop}
    (h : ∃ x y, p x y) : p (choose₂ h).1 (choose₂ h).2 :=
  Classical.choose_spec (Classical.choose_spec h)

/--
Given `h : ∃ x y z, p x y z`, returns a triple `(x, y, z)` witnessing `p x y z`.

Here the triple is represented as `(α × β × γ)`, i.e. `α × (β × γ)`.
-/
noncomputable def choose₃ {α : Type u} {β : Type v} {γ : Type w}
    {p : α → β → γ → Prop} (h : ∃ x y z, p x y z) : α × β × γ :=
  ⟨choose h, ⟨choose (Classical.choose_spec h), choose (choose_spec (choose_spec h))⟩⟩

/--
Specification theorem for `choose₃`.
-/
theorem choose₃_spec {α : Type u} {β : Type v} {γ : Type w}
    {p : α → β → γ → Prop} (h : ∃ x y z, p x y z) :
    p (choose₃ h).1 (choose₃ h).2.1 (choose₃ h).2.2 :=
  choose_spec (choose_spec (choose_spec h))

noncomputable def choose₃₁ {α : Type u} {β : Type v} {γ : Type w}
    {p : α → β → γ → Prop} (h : ∃ x y z, p x y z) : α :=
  (choose₃ h).1

noncomputable def choose₃₂ {α : Type u} {β : Type v} {γ : Type w}
    {p : α → β → γ → Prop} (h : ∃ x y z, p x y z) : β :=
  (choose₃ h).2.1

noncomputable def choose₃₃ {α : Type u} {β : Type v} {γ : Type w}
    {p : α → β → γ → Prop} (h : ∃ x y z, p x y z) : γ :=
  (choose₃ h).2.2

theorem choose₃_spec' {α : Type u} {β : Type v} {γ : Type w}
    {p : α → β → γ → Prop} (h : ∃ x y z, p x y z) :
    p (choose₃₁ h) (choose₃₂ h) (choose₃₃ h) :=
  choose_spec (choose_spec (choose_spec h))

end Classical
