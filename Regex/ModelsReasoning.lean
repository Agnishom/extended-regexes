import Regex.Models

open RE

/-!
# Match semantics with setoid reasoning

We develop some helper functions to obtain a lemma for the match semantics.
The main property derived here is the characterization of `repeat_cat` and
its interaction with `reverse_regex`.
-/

variable {α σ : Type} [EffectiveBooleanAlgebra α σ]
         {r p q : RE α}

/-- correctness of regular expressions. -/
def models_equivalence (r q : RE α) : Prop :=
  ∀ {sp}, sp ⊨ r ↔ sp ⊨ q

infixr:30 " ↔ᵣ " => models_equivalence

/-- ↔ᵣ is an equivalence relation. -/
theorem equiv_trans (rq : r ↔ᵣ q) (qp : q ↔ᵣ p) : r ↔ᵣ p :=
  ⟨ Iff.mp qp ∘ Iff.mp rq , Iff.mpr rq ∘ Iff.mpr qp ⟩

theorem equiv_sym (rq : r ↔ᵣ q) : q ↔ᵣ r :=
  ⟨ Iff.mpr rq , Iff.mp rq ⟩

theorem equiv_refl : r ↔ᵣ r := ⟨ id , id ⟩

/-- Core properties of associativity, using `models`. -/
theorem equiv_cat_assoc :
  ((r ⬝ q) ⬝ w) ↔ᵣ (r ⬝ (q ⬝ w)) :=
  λ {sp} =>
  ⟨ λ h => by
    match sp with
    | ⟨s,u,v⟩ =>
      simp at h;
      simp;
      match h with
      | ⟨sp1,sp2,⟨ss1,ss2,b1,b2,k⟩,a2,c⟩ => exact (
        Eq.ndrec (motive := fun u =>
        (∃ (u₁ : List σ),
            ∃ (u₂ : List σ),
              (∃ (u₁_1 : List σ),
                  ∃ (u₂_1 : List σ),
                    ((s, u₁_1, u₂_1 ++ (u₂ ++ v)) ⊨ r) ∧
                      ((List.reverse u₁_1 ++ s, u₂_1, u₂ ++ v) ⊨ q) ∧ u₁_1 ++ u₂_1 = u₁) ∧
                ((List.reverse u₁ ++ s, u₂, v) ⊨ w) ∧ u₁ ++ u₂ = u) →
          ∃ (u₁ : List σ),
            ∃ (u₂ : List σ),
              ((s, u₁, u₂ ++ v) ⊨ r) ∧
                (∃ (u₁_1 : List σ),
                    ∃ (u₂_1 : List σ),
                      ((List.reverse u₁ ++ s, u₁_1, u₂_1 ++ v) ⊨ q) ∧
                        ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂_1, v) ⊨ w) ∧ u₁_1 ++ u₂_1 = u₂) ∧
                  u₁ ++ u₂ = u)
        (fun h =>
          Eq.ndrec (motive := fun sp1 =>
            (List.reverse sp1 ++ s, sp2, v) ⊨ w →
              (∃ (u₁ : List σ),
                  ∃ (u₂ : List σ),
                    (∃ (u₁_1 : List σ),
                        ∃ (u₂_1 : List σ),
                          ((s, u₁_1, u₂_1 ++ (u₂ ++ v)) ⊨ r) ∧
                            ((List.reverse u₁_1 ++ s, u₂_1, u₂ ++ v) ⊨ q) ∧ u₁_1 ++ u₂_1 = u₁) ∧
                      ((List.reverse u₁ ++ s, u₂, v) ⊨ w) ∧ u₁ ++ u₂ = sp1 ++ sp2) →
                ∃ (u₁ : List σ),
                  ∃ (u₂ : List σ),
                    ((s, u₁, u₂ ++ v) ⊨ r) ∧
                      (∃ (u₁_1 : List σ),
                          ∃ (u₂_1 : List σ),
                            ((List.reverse u₁ ++ s, u₁_1, u₂_1 ++ v) ⊨ q) ∧
                              ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂_1, v) ⊨ w) ∧ u₁_1 ++ u₂_1 = u₂) ∧
                        u₁ ++ u₂ = sp1 ++ sp2)
            (fun a2 h =>
              Eq.mpr (β :=
                ∃ (u₁ : List σ),
                  ∃ (u₂ : List σ),
                    ((s, u₁, u₂ ++ v) ⊨ r) ∧
                      (∃ (u₁_1 : List σ),
                          ∃ (u₂_1 : List σ),
                            ((List.reverse u₁ ++ s, u₁_1, u₂_1 ++ v) ⊨ q) ∧
                              ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂_1, v) ⊨ w) ∧ u₁_1 ++ u₂_1 = u₂) ∧
                        u₁ ++ u₂ = ss1 ++ (ss2 ++ sp2))
                (id
                  (congrArg (a₁ := fun x =>
                    ∃ (x_1 : List σ),
                      ((s, x, x_1 ++ v) ⊨ r) ∧
                        (∃ (u₁ : List σ),
                            ∃ (u₂ : List σ),
                              ((List.reverse x ++ s, u₁, u₂ ++ v) ⊨ q) ∧
                                ((List.reverse u₁ ++ (List.reverse x ++ s), u₂, v) ⊨ w) ∧ u₁ ++ u₂ = x_1) ∧
                          x ++ x_1 = ss1 ++ ss2 ++ sp2)
                    (a₂ := fun x =>
                    ∃ (x_1 : List σ),
                      ((s, x, x_1 ++ v) ⊨ r) ∧
                        (∃ (u₁ : List σ),
                            ∃ (u₂ : List σ),
                              ((List.reverse x ++ s, u₁, u₂ ++ v) ⊨ q) ∧
                                ((List.reverse u₁ ++ (List.reverse x ++ s), u₂, v) ⊨ w) ∧ u₁ ++ u₂ = x_1) ∧
                          x ++ x_1 = ss1 ++ (ss2 ++ sp2))
                    Exists
                    (funext (β := fun x => Prop) (f := fun x =>
                      ∃ (x_1 : List σ),
                        ((s, x, x_1 ++ v) ⊨ r) ∧
                          (∃ (u₁ : List σ),
                              ∃ (u₂ : List σ),
                                ((List.reverse x ++ s, u₁, u₂ ++ v) ⊨ q) ∧
                                  ((List.reverse u₁ ++ (List.reverse x ++ s), u₂, v) ⊨ w) ∧ u₁ ++ u₂ = x_1) ∧
                            x ++ x_1 = ss1 ++ ss2 ++ sp2)
                      (g := fun x =>
                      ∃ (x_1 : List σ),
                        ((s, x, x_1 ++ v) ⊨ r) ∧
                          (∃ (u₁ : List σ),
                              ∃ (u₂ : List σ),
                                ((List.reverse x ++ s, u₁, u₂ ++ v) ⊨ q) ∧
                                  ((List.reverse u₁ ++ (List.reverse x ++ s), u₂, v) ⊨ w) ∧ u₁ ++ u₂ = x_1) ∧
                            x ++ x_1 = ss1 ++ (ss2 ++ sp2))
                      fun u₁ =>
                      congrArg (a₁ := fun x =>
                        ((s, u₁, x ++ v) ⊨ r) ∧
                          (∃ (u₁_1 : List σ),
                              ∃ (u₂ : List σ),
                                ((List.reverse u₁ ++ s, u₁_1, u₂ ++ v) ⊨ q) ∧
                                  ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂, v) ⊨ w) ∧ u₁_1 ++ u₂ = x) ∧
                            u₁ ++ x = ss1 ++ ss2 ++ sp2)
                        (a₂ := fun x =>
                        ((s, u₁, x ++ v) ⊨ r) ∧
                          (∃ (u₁_1 : List σ),
                              ∃ (u₂ : List σ),
                                ((List.reverse u₁ ++ s, u₁_1, u₂ ++ v) ⊨ q) ∧
                                  ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂, v) ⊨ w) ∧ u₁_1 ++ u₂ = x) ∧
                            u₁ ++ x = ss1 ++ (ss2 ++ sp2))
                        Exists
                        (funext (β := fun x => Prop) (f := fun x =>
                          ((s, u₁, x ++ v) ⊨ r) ∧
                            (∃ (u₁_1 : List σ),
                                ∃ (u₂ : List σ),
                                  ((List.reverse u₁ ++ s, u₁_1, u₂ ++ v) ⊨ q) ∧
                                    ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂, v) ⊨ w) ∧ u₁_1 ++ u₂ = x) ∧
                              u₁ ++ x = ss1 ++ ss2 ++ sp2)
                          (g := fun x =>
                          ((s, u₁, x ++ v) ⊨ r) ∧
                            (∃ (u₁_1 : List σ),
                                ∃ (u₂ : List σ),
                                  ((List.reverse u₁ ++ s, u₁_1, u₂ ++ v) ⊨ q) ∧
                                    ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂, v) ⊨ w) ∧ u₁_1 ++ u₂ = x) ∧
                              u₁ ++ x = ss1 ++ (ss2 ++ sp2))
                          fun u₂ =>
                          congrArg (And ((s, u₁, u₂ ++ v) ⊨ r))
                            (congrArg
                              (And
                                (∃ (u₁_1 : List σ),
                                  ∃ (u₂_1 : List σ),
                                    ((List.reverse u₁ ++ s, u₁_1, u₂_1 ++ v) ⊨ q) ∧
                                      ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂_1, v) ⊨ w) ∧ u₁_1 ++ u₂_1 = u₂))
                              (congrArg (Eq (u₁ ++ u₂)) (List.append_assoc ss1 ss2 sp2)))))))
                (Prod.casesOn (motive := fun h =>
                  ∃ (u₁ : List σ),
                    ∃ (u₂ : List σ),
                      ((s, u₁, u₂ ++ v) ⊨ r) ∧
                        (∃ (u₁_1 : List σ),
                            ∃ (u₂_1 : List σ),
                              ((List.reverse u₁ ++ s, u₁_1, u₂_1 ++ v) ⊨ q) ∧
                                ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂_1, v) ⊨ w) ∧ u₁_1 ++ u₂_1 = u₂) ∧
                          u₁ ++ u₂ = ss1 ++ (ss2 ++ sp2))
                  sp fun fst snd =>
                  Exists.casesOn (p := fun u₁ =>
                    ∃ (u₂ : List σ),
                      (∃ (u₁_1 : List σ),
                          ∃ (u₂_1 : List σ),
                            ((s, u₁_1, u₂_1 ++ (u₂ ++ v)) ⊨ r) ∧
                              ((List.reverse u₁_1 ++ s, u₂_1, u₂ ++ v) ⊨ q) ∧ u₁_1 ++ u₂_1 = u₁) ∧
                        ((List.reverse u₁ ++ s, u₂, v) ⊨ w) ∧ u₁ ++ u₂ = ss1 ++ (ss2 ++ sp2))
                    (motive := fun h =>
                    ∃ (u₁ : List σ),
                      ∃ (u₂ : List σ),
                        ((s, u₁, u₂ ++ v) ⊨ r) ∧
                          (∃ (u₁_1 : List σ),
                              ∃ (u₂_1 : List σ),
                                ((List.reverse u₁ ++ s, u₁_1, u₂_1 ++ v) ⊨ q) ∧
                                  ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂_1, v) ⊨ w) ∧ u₁_1 ++ u₂_1 = u₂) ∧
                            u₁ ++ u₂ = ss1 ++ (ss2 ++ sp2))
                    (Eq.mp
                      (congrArg (a₁ := fun x =>
                        ∃ (x_1 : List σ),
                          (∃ (u₁ : List σ),
                              ∃ (u₂ : List σ),
                                ((s, u₁, u₂ ++ (x_1 ++ v)) ⊨ r) ∧
                                  ((List.reverse u₁ ++ s, u₂, x_1 ++ v) ⊨ q) ∧ u₁ ++ u₂ = x) ∧
                            ((List.reverse x ++ s, x_1, v) ⊨ w) ∧ x ++ x_1 = ss1 ++ ss2 ++ sp2)
                        (a₂ := fun x =>
                        ∃ (x_1 : List σ),
                          (∃ (u₁ : List σ),
                              ∃ (u₂ : List σ),
                                ((s, u₁, u₂ ++ (x_1 ++ v)) ⊨ r) ∧
                                  ((List.reverse u₁ ++ s, u₂, x_1 ++ v) ⊨ q) ∧ u₁ ++ u₂ = x) ∧
                            ((List.reverse x ++ s, x_1, v) ⊨ w) ∧ x ++ x_1 = ss1 ++ (ss2 ++ sp2))
                        Exists
                        (funext (β := fun x => Prop) (f := fun x =>
                          ∃ (x_1 : List σ),
                            (∃ (u₁ : List σ),
                                ∃ (u₂ : List σ),
                                  ((s, u₁, u₂ ++ (x_1 ++ v)) ⊨ r) ∧
                                    ((List.reverse u₁ ++ s, u₂, x_1 ++ v) ⊨ q) ∧ u₁ ++ u₂ = x) ∧
                              ((List.reverse x ++ s, x_1, v) ⊨ w) ∧ x ++ x_1 = ss1 ++ ss2 ++ sp2)
                          (g := fun x =>
                          ∃ (x_1 : List σ),
                            (∃ (u₁ : List σ),
                                ∃ (u₂ : List σ),
                                  ((s, u₁, u₂ ++ (x_1 ++ v)) ⊨ r) ∧
                                    ((List.reverse u₁ ++ s, u₂, x_1 ++ v) ⊨ q) ∧ u₁ ++ u₂ = x) ∧
                              ((List.reverse x ++ s, x_1, v) ⊨ w) ∧ x ++ x_1 = ss1 ++ (ss2 ++ sp2))
                          fun u₁ =>
                          congrArg (a₁ := fun x =>
                            (∃ (u₁_1 : List σ),
                                ∃ (u₂ : List σ),
                                  ((s, u₁_1, u₂ ++ (x ++ v)) ⊨ r) ∧
                                    ((List.reverse u₁_1 ++ s, u₂, x ++ v) ⊨ q) ∧ u₁_1 ++ u₂ = u₁) ∧
                              ((List.reverse u₁ ++ s, x, v) ⊨ w) ∧ u₁ ++ x = ss1 ++ ss2 ++ sp2)
                            (a₂ := fun x =>
                            (∃ (u₁_1 : List σ),
                                ∃ (u₂ : List σ),
                                  ((s, u₁_1, u₂ ++ (x ++ v)) ⊨ r) ∧
                                    ((List.reverse u₁_1 ++ s, u₂, x ++ v) ⊨ q) ∧ u₁_1 ++ u₂ = u₁) ∧
                              ((List.reverse u₁ ++ s, x, v) ⊨ w) ∧ u₁ ++ x = ss1 ++ (ss2 ++ sp2))
                            Exists
                            (funext (β := fun x => Prop) (f := fun x =>
                              (∃ (u₁_1 : List σ),
                                  ∃ (u₂ : List σ),
                                    ((s, u₁_1, u₂ ++ (x ++ v)) ⊨ r) ∧
                                      ((List.reverse u₁_1 ++ s, u₂, x ++ v) ⊨ q) ∧ u₁_1 ++ u₂ = u₁) ∧
                                ((List.reverse u₁ ++ s, x, v) ⊨ w) ∧ u₁ ++ x = ss1 ++ ss2 ++ sp2)
                              (g := fun x =>
                              (∃ (u₁_1 : List σ),
                                  ∃ (u₂ : List σ),
                                    ((s, u₁_1, u₂ ++ (x ++ v)) ⊨ r) ∧
                                      ((List.reverse u₁_1 ++ s, u₂, x ++ v) ⊨ q) ∧ u₁_1 ++ u₂ = u₁) ∧
                                ((List.reverse u₁ ++ s, x, v) ⊨ w) ∧ u₁ ++ x = ss1 ++ (ss2 ++ sp2))
                              fun u₂ =>
                              congrArg
                                (And
                                  (∃ (u₁_1 : List σ),
                                    ∃ (u₂_1 : List σ),
                                      ((s, u₁_1, u₂_1 ++ (u₂ ++ v)) ⊨ r) ∧
                                        ((List.reverse u₁_1 ++ s, u₂_1, u₂ ++ v) ⊨ q) ∧ u₁_1 ++ u₂_1 = u₁))
                                (congrArg (And ((List.reverse u₁ ++ s, u₂, v) ⊨ w))
                                  (congrArg (Eq (u₁ ++ u₂)) (List.append_assoc ss1 ss2 sp2))))))
                      h)
                    fun w_1 h_1 =>
                    Prod.casesOn (motive := fun h =>
                      ∃ (u₁ : List σ),
                        ∃ (u₂ : List σ),
                          ((s, u₁, u₂ ++ v) ⊨ r) ∧
                            (∃ (u₁_1 : List σ),
                                ∃ (u₂_1 : List σ),
                                  ((List.reverse u₁ ++ s, u₁_1, u₂_1 ++ v) ⊨ q) ∧
                                    ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂_1, v) ⊨ w) ∧ u₁_1 ++ u₂_1 = u₂) ∧
                              u₁ ++ u₂ = ss1 ++ (ss2 ++ sp2))
                      snd fun fst_1 snd_1 =>
                      Exists.casesOn (p := fun u₂ =>
                        (∃ (u₁ : List σ),
                            ∃ (u₂_1 : List σ),
                              ((s, u₁, u₂_1 ++ (u₂ ++ v)) ⊨ r) ∧
                                ((List.reverse u₁ ++ s, u₂_1, u₂ ++ v) ⊨ q) ∧ u₁ ++ u₂_1 = w_1) ∧
                          ((List.reverse w_1 ++ s, u₂, v) ⊨ w) ∧ w_1 ++ u₂ = ss1 ++ (ss2 ++ sp2))
                        (motive := fun h =>
                        ∃ (u₁ : List σ),
                          ∃ (u₂ : List σ),
                            ((s, u₁, u₂ ++ v) ⊨ r) ∧
                              (∃ (u₁_1 : List σ),
                                  ∃ (u₂_1 : List σ),
                                    ((List.reverse u₁ ++ s, u₁_1, u₂_1 ++ v) ⊨ q) ∧
                                      ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂_1, v) ⊨ w) ∧
                                        u₁_1 ++ u₂_1 = u₂) ∧
                                u₁ ++ u₂ = ss1 ++ (ss2 ++ sp2))
                        h_1 fun w_2 h =>
                        And.casesOn (motive := fun h =>
                          ∃ (u₁ : List σ),
                            ∃ (u₂ : List σ),
                              ((s, u₁, u₂ ++ v) ⊨ r) ∧
                                (∃ (u₁_1 : List σ),
                                    ∃ (u₂_1 : List σ),
                                      ((List.reverse u₁ ++ s, u₁_1, u₂_1 ++ v) ⊨ q) ∧
                                        ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂_1, v) ⊨ w) ∧
                                          u₁_1 ++ u₂_1 = u₂) ∧
                                  u₁ ++ u₂ = ss1 ++ (ss2 ++ sp2))
                          h fun left right =>
                          Exists.casesOn (p := fun u₁ =>
                            ∃ (u₂ : List σ),
                              ((s, u₁, u₂ ++ (w_2 ++ v)) ⊨ r) ∧
                                ((List.reverse u₁ ++ s, u₂, w_2 ++ v) ⊨ q) ∧ u₁ ++ u₂ = w_1)
                            (motive := fun h =>
                            ∃ (u₁ : List σ),
                              ∃ (u₂ : List σ),
                                ((s, u₁, u₂ ++ v) ⊨ r) ∧
                                  (∃ (u₁_1 : List σ),
                                      ∃ (u₂_1 : List σ),
                                        ((List.reverse u₁ ++ s, u₁_1, u₂_1 ++ v) ⊨ q) ∧
                                          ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂_1, v) ⊨ w) ∧
                                            u₁_1 ++ u₂_1 = u₂) ∧
                                    u₁ ++ u₂ = ss1 ++ (ss2 ++ sp2))
                            left fun w_3 h =>
                            And.casesOn (motive := fun h =>
                              ∃ (u₁ : List σ),
                                ∃ (u₂ : List σ),
                                  ((s, u₁, u₂ ++ v) ⊨ r) ∧
                                    (∃ (u₁_1 : List σ),
                                        ∃ (u₂_1 : List σ),
                                          ((List.reverse u₁ ++ s, u₁_1, u₂_1 ++ v) ⊨ q) ∧
                                            ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂_1, v) ⊨ w) ∧
                                              u₁_1 ++ u₂_1 = u₂) ∧
                                      u₁ ++ u₂ = ss1 ++ (ss2 ++ sp2))
                              right fun left right_1 =>
                              Exists.casesOn (p := fun u₂ =>
                                ((s, w_3, u₂ ++ (w_2 ++ v)) ⊨ r) ∧
                                  ((List.reverse w_3 ++ s, u₂, w_2 ++ v) ⊨ q) ∧ w_3 ++ u₂ = w_1)
                                (motive := fun h =>
                                ∃ (u₁ : List σ),
                                  ∃ (u₂ : List σ),
                                    ((s, u₁, u₂ ++ v) ⊨ r) ∧
                                      (∃ (u₁_1 : List σ),
                                          ∃ (u₂_1 : List σ),
                                            ((List.reverse u₁ ++ s, u₁_1, u₂_1 ++ v) ⊨ q) ∧
                                              ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂_1, v) ⊨ w) ∧
                                                u₁_1 ++ u₂_1 = u₂) ∧
                                        u₁ ++ u₂ = ss1 ++ (ss2 ++ sp2))
                                h fun w_4 h_1 =>
                                And.casesOn (motive := fun h =>
                                  ∃ (u₁ : List σ),
                                    ∃ (u₂ : List σ),
                                      ((s, u₁, u₂ ++ v) ⊨ r) ∧
                                        (∃ (u₁_1 : List σ),
                                            ∃ (u₂_1 : List σ),
                                              ((List.reverse u₁ ++ s, u₁_1, u₂_1 ++ v) ⊨ q) ∧
                                                ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂_1, v) ⊨ w) ∧
                                                  u₁_1 ++ u₂_1 = u₂) ∧
                                          u₁ ++ u₂ = ss1 ++ (ss2 ++ sp2))
                                  h_1 fun left_1 right =>
                                  And.casesOn (motive := fun h =>
                                    ∃ (u₁ : List σ),
                                      ∃ (u₂ : List σ),
                                        ((s, u₁, u₂ ++ v) ⊨ r) ∧
                                          (∃ (u₁_1 : List σ),
                                              ∃ (u₂_1 : List σ),
                                                ((List.reverse u₁ ++ s, u₁_1, u₂_1 ++ v) ⊨ q) ∧
                                                  ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂_1, v) ⊨ w) ∧
                                                    u₁_1 ++ u₂_1 = u₂) ∧
                                            u₁ ++ u₂ = ss1 ++ (ss2 ++ sp2))
                                    right fun left_2 right_2 =>
                                    Eq.ndrec (motive := fun w_1 =>
                                      (List.reverse w_1 ++ s, w_2, v) ⊨ w →
                                        w_1 ++ w_2 = ss1 ++ (ss2 ++ sp2) →
                                          ∃ (u₁ : List σ),
                                            ∃ (u₂ : List σ),
                                              ((s, u₁, u₂ ++ v) ⊨ r) ∧
                                                (∃ (u₁_1 : List σ),
                                                    ∃ (u₂_1 : List σ),
                                                      ((List.reverse u₁ ++ s, u₁_1, u₂_1 ++ v) ⊨ q) ∧
                                                        ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂_1, v) ⊨ w) ∧
                                                          u₁_1 ++ u₂_1 = u₂) ∧
                                                  u₁ ++ u₂ = ss1 ++ (ss2 ++ sp2))
                                      (fun left right_1 =>
                                        Exists.intro (p := fun u₁ =>
                                          ∃ (u₂ : List σ),
                                            ((s, u₁, u₂ ++ v) ⊨ r) ∧
                                              (∃ (u₁_1 : List σ),
                                                  ∃ (u₂_1 : List σ),
                                                    ((List.reverse u₁ ++ s, u₁_1, u₂_1 ++ v) ⊨ q) ∧
                                                      ((List.reverse u₁_1 ++ (List.reverse u₁ ++ s), u₂_1, v) ⊨ w) ∧
                                                        u₁_1 ++ u₂_1 = u₂) ∧
                                                u₁ ++ u₂ = ss1 ++ (ss2 ++ sp2))
                                          ss1
                                          (Exists.intro (p := fun u₂ =>
                                            ((s, ss1, u₂ ++ v) ⊨ r) ∧
                                              (∃ (u₁ : List σ),
                                                  ∃ (u₂_1 : List σ),
                                                    ((List.reverse ss1 ++ s, u₁, u₂_1 ++ v) ⊨ q) ∧
                                                      ((List.reverse u₁ ++ (List.reverse ss1 ++ s), u₂_1, v) ⊨ w) ∧
                                                        u₁ ++ u₂_1 = u₂) ∧
                                                ss1 ++ u₂ = ss1 ++ (ss2 ++ sp2))
                                            (ss2 ++ sp2)
                                            {
                                              left :=
                                                of_eq_true
                                                  (Eq.trans
                                                    (congrFun (β := fun R => Prop) (f :=
                                                      models (s, ss1, ss2 ++ sp2 ++ v)) (g :=
                                                      models (s, ss1, ss2 ++ (sp2 ++ v)))
                                                      (congrArg models
                                                        (congrArg (Prod.mk s)
                                                          (congrArg (Prod.mk ss1) (List.append_assoc ss2 sp2 v))))
                                                      r)
                                                    (eq_true b1)),
                                              right :=
                                                {
                                                  left :=
                                                    Exists.intro (p := fun u₁ =>
                                                      ∃ (u₂ : List σ),
                                                        ((List.reverse ss1 ++ s, u₁, u₂ ++ v) ⊨ q) ∧
                                                          ((List.reverse u₁ ++ (List.reverse ss1 ++ s), u₂, v) ⊨ w) ∧
                                                            u₁ ++ u₂ = ss2 ++ sp2)
                                                      ss2
                                                      (Exists.intro (p := fun u₂ =>
                                                        ((List.reverse ss1 ++ s, ss2, u₂ ++ v) ⊨ q) ∧
                                                          ((List.reverse ss2 ++ (List.reverse ss1 ++ s), u₂, v) ⊨ w) ∧
                                                            ss2 ++ u₂ = ss2 ++ sp2)
                                                        sp2
                                                        { left := of_eq_true (eq_true b2),
                                                          right :=
                                                            {
                                                              left :=
                                                                Eq.mp
                                                                  (congrFun (β := fun R => Prop) (f :=
                                                                    models (List.reverse (ss1 ++ ss2) ++ s, sp2, v))
                                                                    (g :=
                                                                    models
                                                                      (List.reverse ss2 ++ (List.reverse ss1 ++ s), sp2,
                                                                        v))
                                                                    (congrArg models
                                                                      (congrFun (β := fun snd =>
                                                                        List σ × List σ × List σ)
                                                                        (congrArg Prod.mk
                                                                          (Eq.trans
                                                                            (congrFun (β := fun a => List σ)
                                                                              (congrArg HAppend.hAppend
                                                                                (List.reverse_append ss1 ss2))
                                                                              s)
                                                                            (List.append_assoc (List.reverse ss2)
                                                                              (List.reverse ss1) s)))
                                                                        (sp2, v)))
                                                                    w)
                                                                  a2,
                                                              right := of_eq_true (eq_self (ss2 ++ sp2)) :
                                                              ((List.reverse ss2 ++ (List.reverse ss1 ++ s), sp2, v) ⊨
                                                                  w) ∧
                                                                ss2 ++ sp2 = ss2 ++ sp2 } :
                                                          ((List.reverse ss1 ++ s, ss2, sp2 ++ v) ⊨ q) ∧
                                                            ((List.reverse ss2 ++ (List.reverse ss1 ++ s), sp2, v) ⊨
                                                                w) ∧
                                                              ss2 ++ sp2 = ss2 ++ sp2 }),
                                                  right := Eq.refl (ss1 ++ (ss2 ++ sp2)) :
                                                  (∃ (u₁ : List σ),
                                                      ∃ (u₂ : List σ),
                                                        ((List.reverse ss1 ++ s, u₁, u₂ ++ v) ⊨ q) ∧
                                                          ((List.reverse u₁ ++ (List.reverse ss1 ++ s), u₂, v) ⊨ w) ∧
                                                            u₁ ++ u₂ = ss2 ++ sp2) ∧
                                                    ss1 ++ (ss2 ++ sp2) = ss1 ++ (ss2 ++ sp2) } :
                                              ((s, ss1, ss2 ++ sp2 ++ v) ⊨ r) ∧
                                                (∃ (u₁ : List σ),
                                                    ∃ (u₂ : List σ),
                                                      ((List.reverse ss1 ++ s, u₁, u₂ ++ v) ⊨ q) ∧
                                                        ((List.reverse u₁ ++ (List.reverse ss1 ++ s), u₂, v) ⊨ w) ∧
                                                          u₁ ++ u₂ = ss2 ++ sp2) ∧
                                                  ss1 ++ (ss2 ++ sp2) = ss1 ++ (ss2 ++ sp2) }))
                                      right_2 left right_1))
            k a2 h)
        c h
      ),
    λ h => by
    match sp with
    | ⟨s,u,v⟩ =>
      simp at h;
      simp;
      match h with
      | ⟨sp1,sp2,a1,⟨ss1,ss2,b1,b2,k⟩,c⟩ =>
        subst c k;
        exact ⟨(sp1 ++ ss1),_,(⟨_,_,
                (by rw[←List.append_assoc]; exact a1),b1,rfl⟩),
                        (by simp; exact b2),
                        (List.append_assoc sp1 ss1 ss2)⟩
  ⟩

/-- Congruence of matching with respect to concatenation, using `models`. -/
theorem equiv_cat_cong (rr : r ↔ᵣ r') (qq : q ↔ᵣ q') :
  r ⬝ q ↔ᵣ r' ⬝ q' :=
  λ {sp} =>
  ⟨ λ h => by
    match sp with
    | ⟨s,u,v⟩ =>
      simp at h;
      match h with
      | ⟨sp1,sp2,a1,b1,c⟩ => simp; exact ⟨sp1,sp2,rr.mp a1,qq.mp b1,c⟩,
    λ h => by
    match sp with
    | ⟨s,u,v⟩ =>
      simp at h;
      match h with
      | ⟨sp1,sp2,a1,b1,c⟩ => simp; exact ⟨sp1,sp2,rr.mpr a1,qq.mpr b1,c⟩
  ⟩

/-- Epsilon is the left unit with respect to concatenation, using `models`. -/
theorem equiv_eps_cat :
  ε ⬝ r ↔ᵣ r :=
  λ {sp} =>
  match sp with
  | ⟨b,n,l⟩ =>
  ⟨ λ h => by
      simp at h
      match h with
      | ⟨ [],_,r1,r2,c⟩ => simp at r2 c; subst c; assumption,
    λ h => by
     simp;
     exact ⟨[],(by simp),_,(by simp; exact h),(by simp)⟩
  ⟩

/-- Epsilon is the right unit with respect to concatenation, using `models`. -/
theorem equiv_cat_eps :
  r ⬝ ε ↔ᵣ r :=
  λ {sp} =>
  match sp with
  | ⟨b,n,l⟩ =>
  ⟨ λ h => by
      simp at h
      match h with
      | ⟨ s1,[],r1,r2,c⟩ => simp at r2 c; subst c; assumption,
    λ h => by
     simp;
     exact ⟨_,[],(by simp; exact h),(by simp),(by simp)⟩
  ⟩

/-- Symmetry of iterated product, using `models`. -/
theorem equiv_repeat_cat_cat :
  (r ⁽ m ⁾) ⬝ r ↔ᵣ r ⬝ (r ⁽ m ⁾)  :=
  match m with
  | 0 => equiv_trans equiv_eps_cat (equiv_sym equiv_cat_eps)
  | .succ _ => equiv_trans equiv_cat_assoc
                           (equiv_cat_cong equiv_refl equiv_repeat_cat_cat)

/-- Reversal of repetition is repetition of reversal and vice versa, using `models`. -/
theorem equiv_reverse_regex_repeat_cat {r : RE α} {m : ℕ} :
  ((r ⁽ m ⁾) ʳ) ↔ᵣ
  ((r ʳ) ⁽ m ⁾) :=
  match m with
  | 0       => equiv_refl
  | .succ _ => equiv_trans (equiv_cat_cong equiv_reverse_regex_repeat_cat equiv_refl)
                           equiv_repeat_cat_cat
