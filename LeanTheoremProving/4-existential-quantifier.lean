example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  Exists.intro 1 h

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  Exists.intro 0 h

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  Exists.intro y (And.intro hxy hyz)

#check @Exists.intro -- ∀ {α : Sort u_1} {p : α → Prop} (w : α), p w → Exists p

example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩

example (x : Nat) (h : x > 0) : ∃ y, y < x :=
  ⟨0, h⟩

example (x y z : Nat) (hxy : x < y) (hyz : y < z) : ∃ w, x < w ∧ w < z :=
  ⟨y, hxy, hyz⟩

section ge
variable (g : Nat → Nat → Nat)
variable (hg : g 0 0 = 0)

theorem gex1 (hg : g 0 0 = 0): ∃ x, g x x = x := ⟨0, hg⟩
theorem gex2 (hg : g 0 0 = 0): ∃ x, g x 0 = x := ⟨0, hg⟩
theorem gex3 (hg : g 0 0 = 0): ∃ x, g 0 0 = x := ⟨0, hg⟩
theorem gex4 (hg : g 0 0 = 0): ∃ x, g x x = 0 := ⟨0, hg⟩

set_option pp.explicit true  -- display implicit arguments
#print gex1
#print gex2
#print gex3
#print gex4
end ge

variable (α : Type) (p q : α → Prop)

example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩

variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨(w : α), (hw : p w ∧ q w)⟩ => ⟨w, hw.right, hw.left⟩

-- decompose the conjuction
variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  let ⟨w, hpw, hqw⟩ := h
  ⟨w, hqw, hpw⟩

variable (α : Type) (p q : α → Prop)
-- pattern matching in arguments
example : (∃ x, p x ∧ q x) → ∃ x, q x ∧ p x :=
  fun ⟨w, hpw, hqw⟩ => ⟨w, hqw, hpw⟩

def is_even(a: Nat) := ∃ b, a = 2*b
theorem even_plus_even (h1: is_even a) (h2: is_even b): is_even (a+b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1+w2, by rw [hw1, hw2, Nat.mul_add]⟩

open Classical
variable (p : α → Prop)

example (h : ¬ ∀ x, ¬ p x) : ∃ x, p x :=
  byContradiction
    (fun h1 : ¬ ∃ x, p x =>
      have h2 : ∀ x, ¬ p x :=
        fun x =>
        fun h3 : p x =>
        have h4 : ∃ x, p x := ⟨x, h3⟩
        show False from h1 h4
      show False from h h2)

open Classical

variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : (∃ x : α, r) → r :=
  fun ⟨w, hw⟩ => hw
example (a : α) : r → (∃ x : α, r) :=
  fun hw => ⟨a, hw⟩
example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  Iff.intro (
    fun h =>
      match h with
      | ⟨w, hw⟩ => ⟨⟨w, hw.left⟩, hw.right⟩
  )
  (
    fun h =>
      match h with
      | ⟨⟨w, hw⟩, hr⟩ => ⟨w, ⟨hw, hr⟩⟩
  )
example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
  Iff.intro (
    fun h =>
      match h with
      | ⟨w, hw⟩ =>
        match hw with
        | Or.inl hpw => Or.inl ⟨w, hpw⟩
        | Or.inr hqw => Or.inr ⟨w, hqw⟩
  ) (
    fun h =>
      match h with
      | Or.inl ⟨w, hpw⟩ => ⟨w, Or.inl hpw⟩
      | Or.inr ⟨w, hqw⟩ => ⟨w, Or.inr hqw⟩
  )

example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
  Iff.intro (
    fun h =>
      fun ⟨w, hnw⟩ =>
        have h1 : p w := h w
        show False from hnw h1
  ) (
    fun h =>
      fun x : α =>
        byContradiction (
          fun h1 : ¬ p x =>
          show False from h ⟨x, h1⟩
        )
  )
example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
  Iff.intro (
    fun ⟨w, hw⟩ =>
      fun h =>
        show False from h w hw
  ) (
    fun h =>
      byContradiction (
        fun h1 : ¬ ∃ x, p x =>
          have h2 : ∀ x, ¬ p x :=
            fun x =>
              fun h3 : p x =>
                have h4 : ∃ x, p x := ⟨x, h3⟩
                show False from h1 h4
          show False from h h2
      )
  )
example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
  Iff.intro (
    fun (h: ¬ ∃ x, p x) =>
      fun x =>
        fun hnw: p x =>
          h ⟨x, hnw⟩
  ) (
    fun h =>
      fun ⟨w, hw⟩ =>
        h w hw
  )
example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
  Iff.intro (
    fun (h: ¬ ∀ x, p x) =>
      byContradiction (
        fun h1 : ¬ ∃ x, ¬ p x =>
          have h2 : ∀ x, p x :=
            fun x =>
              byContradiction (
                fun h3: ¬ p x =>
                  show False from h1 ⟨x, h3⟩
              )
          show False from h h2
      )
  ) (
    fun ⟨w, hnw⟩ =>
      fun h: ∀ x, p x =>
        hnw (h w)
  )

example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
  Iff.intro (
    fun h =>
      fun ⟨w, hw⟩ =>
        h w hw
  ) (
    fun h =>
      fun x =>
        fun hpx: p x =>
          have h1 : ∃ x, p x := ⟨x, hpx⟩
          show r from h h1
  )
example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
  Iff.intro (
    fun ⟨w, hw⟩ =>
      fun h1: ∀ x, p x =>
        hw (h1 w)
  ) ( -- copy from the answer
    fun h: (∀ x, p x) → r =>
    show ∃ x, p x → r from
      byCases
        (fun hap: ∀ x, p x => ⟨a, fun _ => h hap⟩)
        (fun hnap: ¬ ∀ x, p x =>
          byContradiction (
            fun hnex : ¬ ∃ x, p x → r =>
              have hap: ∀ x, p x :=
                fun x =>
                  byContradiction (
                    fun hnp: ¬ p x =>
                      have hex: ∃ x, p x → r := ⟨x, (fun hp => absurd hp hnp)⟩
                      show False from hnex hex
                  )
            show False from hnap hap
          )
        )
  )


example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
  Iff.intro (
    fun ⟨w, hrpx⟩ =>
      fun hr: r =>
        ⟨w, hrpx hr⟩
  ) (
    fun hr_expx =>
      byCases (
        fun hr: r =>
          match hr_expx hr with
            | ⟨w, hw⟩ => ⟨w, fun _: r => hw⟩
      ) (
        fun hnr: ¬ r =>
          ⟨a, fun hr: r => absurd hr hnr⟩
      )
  )
