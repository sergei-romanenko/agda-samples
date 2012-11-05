theory MOESI
imports Main
begin

inductive moesi :: "(nat * nat * nat * nat * nat) => bool" where
  "moesi (i, 0, 0, 0, 0)" |
  "moesi (Suc i, m, s, e, o') ==> moesi (i, 0, Suc (s + e), 0, m + o')" |
  "moesi (i, m, s, Suc e, o') ==> moesi (i, Suc m, s, e, o')" |
  "moesi (i, m, Suc s, e, o') ==> moesi (i + m + s + e + o', 0, 0, Suc 0, 0)" |
  "moesi (Suc i, m, s, e, o') ==> moesi (i + m + s + e + o', 0, 0, Suc 0, 0)"

inductive unsafe :: "(nat * nat * nat * nat * nat) => bool" where 
  "unsafe (i, Suc m, Suc s, e, o')" |
  "unsafe (i, Suc m, s, Suc e, o')" |
  "unsafe (i, Suc m, s, e, Suc o')" |
  "unsafe (i, Suc (Suc m), s, e, o')" |
  "unsafe (i, m, s, Suc (Suc e), o')"


inductive moesi' :: "(nat * nat * nat * nat * nat) => bool" where
  "moesi'(_, 0, 0, Suc 0, 0)" |
  "moesi'(_, Suc 0, 0, 0, 0)" |
  "moesi'(_, 0, _, 0, _)"

lemma inclusion: "moesi c ==> moesi' c"
  apply(erule moesi.induct)
  apply(erule moesi'.cases | simp add: moesi'.intros)+
done

lemma safety: "moesi' c ==> ~unsafe c"
  apply(erule moesi'.cases)
  apply(erule unsafe.cases | auto)+
done

theorem valid: "moesi c ==> ~unsafe c"
  apply(insert inclusion safety, simp)
done

end
