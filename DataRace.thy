theory DataRace
imports Main
begin

inductive datarace :: "(nat * nat * nat) => bool" where
  "datarace (out, 0, 0)" |
  "datarace (Suc out, 0, 0) ==> datarace (out, Suc 0, 0)" |
  "datarace (Suc out, 0, scs) ==> datarace (out, 0, Suc scs)" |
  "datarace (out, Suc cs, scs) ==> datarace (Suc out, cs, scs)" |
  "datarace (out, cs, Suc scs) ==> datarace (Suc out, cs, scs)"

inductive unsafe :: "(nat * nat * nat) => bool" where 
  "unsafe (out, Suc cs, Suc scs)"


inductive datarace' :: "(nat * nat * nat) => bool" where
  "datarace'(_, 0, _)" |
  "datarace'(_, Suc 0, 0)"

lemma inclusion: "datarace c ==> datarace' c"
  apply(erule datarace.induct)
  apply(erule datarace'.cases | simp add: datarace'.intros)+
done

lemma safety: "datarace' c ==> ~unsafe c"
  apply(erule datarace'.cases)
  apply(erule unsafe.cases | auto)+
done

theorem valid: "datarace c ==> ~unsafe c"
  apply(insert inclusion safety, simp)
done

end

