section conj0
variable (p q : Prop)

#check p → q → p ∧ q
#check ¬p → p ↔ False
#check p ∨ q → q ∨ p
end conj0

-- conjunction
section conj1
variable (p q : Prop)
example (hp: p) (hq : q) : p ∧ q := And.intro hp hq
#check fun (hp: p) (hq : q) => And.intro hp hq
end conj1

section conj2
variable (p q : Prop)

example (h : p ∧ q) : p := And.left h
example (h : p ∧ q) : q := And.right h
end conj2

section conj3
variable (p q : Prop)

example (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)
end conj3

-- And.intro only has one constructor, so anonymous constructor is allowed
section anonyCtor
variable (p q : Prop)
variable (hp: p) (hq: q)

-- anonymous constructor
#check (⟨hp, hq⟩ : p ∧ q)
end anonyCtor

section syntacticGadget
variable (xs: List Nat)
#check List.length xs
#check xs.length
end syntacticGadget

-- left right
section left_right
variable (p q : Prop)
example (h: p ∧ q): q ∧ p :=
  ⟨h.right, h.left⟩
end left_right

-- flatten nested ctor
section flatten
variable (p q : Prop)
example (h: p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, ⟨h.left, h.right⟩⟩

example (h: p ∧ q) : q ∧ p ∧ q :=
  ⟨h.right, h.left, h.right⟩
end flatten

-- disjunction
-- Or has two constructors: intro_left and intro_right, so anonymous constructor is not allowed
section disj
variable (p q : Prop)
example (hp: p) : p ∨ q := Or.intro_left q hp
example (hq: q) : p ∨ q := Or.intro_right p hq
end disj

section disj_elem
variable (p q r: Prop)
example (h: p ∨ q): q ∨ p :=
  Or.elim h
    (fun hp: p => Or.intro_right q hp)
    (fun hq: q => Or.intro_left p hq)
end disj_elem

section or_intro_infer
variable (p q r: Prop)
example (h: p ∨ q): q ∨ p :=
  h.elim -- equals to Or.elim h
    (fun hp: p => Or.inr hp) -- infer q, intro_right _ hp
    (fun hq: q => Or.inl hq) -- infer p, intro_left _ hq
end or_intro_infer

-- negation and falsity
-- ¬ p = p → False
section neg1
variable (p q: Prop)

example (hpq: p → q) (hnq: ¬q) : ¬p :=
  fun hp: p =>
  show False from hnq (hpq hp)
end neg1

section neg2
variable (p q : Prop)

example (hp : p) (hnp : ¬p) : q := False.elim (hnp hp)
end neg2

-- absurd derive arbitrary facts
section absurd_test
variable (p q : Prop)
example (hp: p) (hnp: ¬p) : q :=
  absurd hp hnp
end absurd_test

section absurd2
variable (p q r: Prop)
example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp
  -- absurd hnp (hqp hq) -- type mismatch
end absurd2

section absurd2'
variable (p q r: Prop)
example (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
    (hnp (hqp hq)).elim -- False.elim
end absurd2'

-- logical equivalence
#check Iff.intro
#check Iff.mp -- (p ↔ q) → p → q
#check Iff.mpr -- (p ↔ q) → q → p

section iff2
theorem and_swap {p q: Prop}: p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h: p ∧ q => And.intro (And.right h) (And.left h)) -- p ∧ q → q ∧ p
    (fun h: q ∧ p => And.intro (And.right h) (And.left h)) -- q ∧ p → p ∧ q

#check and_swap
end iff2


section iff
variable (p q: Prop)
theorem and_swap2 : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h: p ∧ q => And.intro (And.right h) (And.left h)) -- p ∧ q → q ∧ p
    (fun h: q ∧ p => And.intro (And.right h) (And.left h)) -- q ∧ p → p ∧ q

#check and_swap2 p q

variable (h: p ∧ q)
example: q ∧ p := Iff.mp (and_swap2 p q) h
end iff

section iff_annoy
variable (p q: Prop)
theorem and_swap_annoy: p ∧ q ↔ q ∧ p :=
  ⟨
    fun h => ⟨h.right, h.left⟩, -- p ∧ q → q ∧ p
    fun h => ⟨h.right, h.left⟩, -- q ∧ p → p ∧ q
  ⟩

example (h: p ∧ q): q ∧ p := (and_swap_annoy p q).mp h
end iff_annoy

-- subgoals
section subgoals
variable (p q: Prop)

-- have h: p := s; t ⇔ (fun h: p => t) s
example (h: p ∧ q): q ∧ p :=
  have hp: p := h.left
  have hq: q := h.right
  show q ∧ p from
    ⟨hq, hp⟩
end subgoals

section reason_backward
variable (p q: Prop)

example (h: p ∧ q): q ∧ p :=
  suffices hp: p from
    suffices hq: q from
      ⟨hq, hp⟩
    show q from h.right
  show p from h.left
end reason_backward

section LargeClassical
-- classical logic
open Classical

section classical
variable (p: Prop)
#check em p -- one of p or ¬p must be true

-- ¬¬p ⇔ (p → False) → False
-- dne : ¬¬p → p
theorem dne {p : Prop} (h: ¬¬p) : p :=
  Or.elim (em p)
    (fun hp: p => hp)
    (fun hnp: ¬p => False.elim (h hnp))
end classical

-- exercise: solution given by copilot
section em_prove
theorem em {p: Prop}: p ∨ ¬p :=
    dne (
      -- fun : ¬(p ∨ ¬p) → False, i.e. ¬¬(p ∨ ¬p)
      -- hnn is argument, the type is ¬(p ∨ ¬p)
      λ hnn : ¬(p ∨ ¬p) =>
        have hnp : ¬p :=
          λ hp : p => hnn (Or.inl hp)
        hnn (Or.inr hnp)
    )
end em_prove

example (h: ¬¬p): p :=
  byCases -- derived from em p
    (fun hp: p => hp)
    (fun hnp: ¬p => False.elim (h hnp))

example (h: ¬¬p): p :=
  byContradiction -- byContradiction is derived from em p
    (fun h1: ¬p =>
      show False from h h1)

example (h: ¬(p ∧ q)): ¬p ∨ ¬q :=
  byCases
    (fun hp: p => Or.inr (show ¬q from fun hq: q => h ⟨hp, hq⟩)) -- ¬q is q→False, so create a function, i.e. fun hq: q => h ⟨hp, hq⟩
    (fun hnp: ¬p => Or.inl hnp)

open Classical

-- distributivity
example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (fun h : p ∧ (q ∨ r) =>
      have hp : p := h.left
      Or.elim (h.right)
        (fun hq : q =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inl ⟨hp, hq⟩)
        (fun hr : r =>
          show (p ∧ q) ∨ (p ∧ r) from Or.inr ⟨hp, hr⟩))
    (fun h : (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (fun hpq : p ∧ q =>
          have hp : p := hpq.left
          have hq : q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (fun hpr : p ∧ r =>
          have hp : p := hpr.left
          have hr : r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

-- an example that requires classical reasoning
example (p q : Prop) : ¬(p ∧ ¬q) → (p → q) :=
  fun h : ¬(p ∧ ¬q) =>
  fun hp : p =>
  show q from
    Or.elim (em q)
      (fun hq : q => hq)
      (fun hnq : ¬q => absurd (And.intro hp hnq) h) -- (p ∧ ¬q) ¬(p ∧ ¬q)

end LargeClassical

section exercise
variable (p q r: Prop)
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (λ h: p ∧ q => ⟨h.right, h.left⟩)
    (λ h: q ∧ p => ⟨h.right, h.left⟩)

example : p ∨ q ↔ q ∨ p :=
  Iff.intro
    (λ h: p ∨ q => h.elim
      (λ hp: p => Or.inr hp)
      (λ hq: q => Or.inl hq))
    (λ h: q ∨ p => h.elim
      (λ hq: q => Or.inr hq)
      (λ hp: p => Or.inl hp))

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  Iff.intro
    (λ h: (p ∧ q) ∧ r => ⟨h.left.left, ⟨h.left.right, h.right⟩⟩)
    (λ h: p ∧ (q ∧ r) => ⟨⟨h.left, h.right.left⟩, h.right.right⟩)
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  Iff.intro
    (λ h: (p ∨ q) ∨ r => h.elim
      (λ hpq: p ∨ q => hpq.elim
        (λ hp: p => Or.inl hp)
        (λ hq: q => Or.inr (Or.inl hq)))
      (λ hr: r => Or.inr (Or.inr hr)))
    (λ h: p ∨ (q ∨ r) => h.elim
      (λ hp: p => Or.inl (Or.inl hp))
      (λ hqr: q ∨ r => hqr.elim
        (λ hq: q => Or.inl (Or.inr hq))
        (λ hr: r => Or.inr hr)))

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  Iff.intro
    (λ h: p ∧ (q ∨ r) =>
      have hp: p := h.left
      Or.elim (h.right)
        (λ hq: q => Or.inl ⟨hp, hq⟩)
        (λ hr: r => Or.inr ⟨hp, hr⟩))
    (λ h: (p ∧ q) ∨ (p ∧ r) =>
      Or.elim h
        (λ hpq: p ∧ q =>
          have hp: p := hpq.left
          have hq: q := hpq.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inl hq⟩)
        (λ hpr: p ∧ r =>
          have hp: p := hpr.left
          have hr: r := hpr.right
          show p ∧ (q ∨ r) from ⟨hp, Or.inr hr⟩))

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  Iff.intro
    (
      λ h: p ∨ (q ∧ r) =>
        h.elim
          (λ hp: p => ⟨Or.inl hp, Or.inl hp⟩)
          (λ hqr: q ∧ r =>
            have hq: q := hqr.left
            have hr: r := hqr.right
            show (p ∨ q) ∧ (p ∨ r) from ⟨Or.inr hq, Or.inr hr⟩)
    )
    (
      λ h: (p ∨ q) ∧ (p ∨ r) =>
        have hpq: p ∨ q := h.left
        have hpr: p ∨ r := h.right
        show p ∨ (q ∧ r) from
          Or.elim hpq
            (λ hp: p => Or.inl hp)
            (λ hq: q =>
              Or.elim hpr
                (λ hp: p => Or.inl hp) -- this branch is impossible
                (λ hr: r => Or.inr ⟨hq, hr⟩))
    )

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  Iff.intro
    (
      λ h: p → (q → r) =>
        fun hpq: p ∧ q =>
          have hp: p := hpq.left
          have hq: q := hpq.right
          show r from h hp hq
    )
    (
      λ h: p ∧ q → r =>
        fun hp: p =>
          fun hq: q =>
            show r from h ⟨hp, hq⟩
    )
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  Iff.intro
    (
      λ h: (p ∨ q → r) =>
        ⟨λ hp: p => h (Or.inl hp), λ hq: q => h (Or.inr hq)⟩
    )
    (
      λ h: (p → r) ∧ (q → r) =>
        λ hpq: (p ∨ q) =>
          have hpr: (p → r) := h.left
          have hqr: (q → r) := h.right
          show r from hpq.elim
            (λ hp: p => hpr hp)
            (λ hq: q => hqr hq)
    )
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  Iff.intro
    (
      λ h: ¬(p ∨ q) =>
        ⟨
          λ hp: p => h (Or.inl hp),
          λ hq: q => h (Or.inr hq),
        ⟩
    )
    (
      λ h: ¬p ∧ ¬q =>
        λ hpq: p ∨ q =>
          have hnp: ¬p := h.left
          have hnq: ¬q := h.right
          hpq.elim
            (λ hp: p => hnp hp)
            (λ hq: q => hnq hq)
    )
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
  λ h: ¬p ∨ ¬q =>
    λ hpq: p ∧ q =>
      have hp: p := hpq.left
      have hq: q := hpq.right
      h.elim
        (λ hnp: ¬p => hnp hp)
        (λ hnq: ¬q => hnq hq)
example : ¬(p ∧ ¬p) :=
  λ h: p ∧ ¬p =>
    h.right h.left

example : p ∧ ¬q → ¬(p → q) :=
  λ h: p ∧ ¬q =>
    λ hpq: p → q =>
      h.right (hpq h.left)
example : ¬p → (p → q) :=
  λ hnp: ¬p =>
    λ hp: p =>
      False.elim (hnp hp)
example : (¬p ∨ q) → (p → q) :=
  λ hnpq: ¬p ∨ q =>
    λ hp: p =>
      hnpq.elim
        (λ hnp: ¬p => absurd hp hnp)
        (λ hq: q => hq)
example : p ∨ False ↔ p :=
  Iff.intro
    (
      λ h: p ∨ False =>
        h.elim
          (λ hp: p => hp)
          (λ hf: False => hf.elim)
    )
    (
      Or.inl
    )
example : p ∧ False ↔ False :=
  Iff.intro
    (
      And.right
    )
    (
      λ hf: False => ⟨False.elim hf, hf⟩
    )
example : (p → q) → (¬q → ¬p) :=
  λ hpq: p → q =>
    λ hnq: ¬q =>
      λ hp: p =>
        hnq (hpq hp)

end exercise

section exercise2
-- classical pattern: em dne byContradiction byCases
open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  λ h: p → q ∨ r =>
    (em q).elim
      (
        λ hq: q =>
          Or.inl
            λ hp: p => hq
      )
      (
        λ hnq: ¬q =>
          Or.inr
          λ hp: p =>
            (h hp).elim
              (λ hq: q => absurd hq hnq)
              (λ hr: r => hr)
      )


example : ¬(p ∧ q) → ¬p ∨ ¬q :=
  λ hnpq : ¬(p ∧ q) =>
    (em p).elim
      (
        λ hp: p =>
          (em q).elim
            (
              λ hq: q =>
                False.elim (hnpq ⟨hp, hq⟩)
            )
            Or.inr
      )
      Or.inl
theorem tmp : ¬(p → q) → p ∧ ¬q :=
  λ hnpq: ¬(p → q) =>
    (em p).elim
      (
        λ hp: p =>
          (em q).elim
            (λ hq: q => False.elim (hnpq (λ _: p => hq)))
            (λ hnq: ¬q => ⟨hp, hnq⟩)
      )
      (
        λ hnp: ¬p =>
          False.elim (hnpq (λ hp: p => absurd hp hnp))
      )
example : (p → q) → (¬p ∨ q) :=
  λ h: (p → q) =>
    (em p).elim
      (
        λ hp: p =>
          Or.inr (h hp)
      )
      Or.inl
example : (¬q → ¬p) → (p → q) :=
  λ h: (¬q → ¬p) =>
    (em q).elim
      (
        λ hq: q =>
          λ hp: p =>
            hq
      )
      (
        λ hnq: ¬q =>
          λ hp: p =>
            absurd hp (h hnq)
      )
example : p ∨ ¬p :=
  byCases
    Or.inl
    Or.inr

example : (((p → q) → p) → p) :=
  λ hpqp: ((p → q) → p) =>
    byCases
      (
        λ hpq: (p → q) =>
          hpqp hpq
      )
      (
        λ hnpq: ¬(p → q) =>
          (em p).elim
            (λ hp: p => hp)
            (λ hnp: ¬p => False.elim (hnpq (λ hp: p => absurd hp hnp)))
      )

end exercise2
